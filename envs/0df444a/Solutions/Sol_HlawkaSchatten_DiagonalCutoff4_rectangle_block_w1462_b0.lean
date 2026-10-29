-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1462_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:33.718455+00:00
-- url     : https://prove2.me/submissions/39d62a7c-ecf6-4bce-a08a-9a32b90b33ee

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
theorem support_rectangle_w1462_s0_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-217535159/1250000000 : ℝ)*x 0 + (743335121/1250000000 : ℝ)*x 1 + (4838723577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217535159/1250000000 : ℝ)^2211 ≤ (10274892305829/100000000000000 : ℝ)^1699 := by
    have hnat : (217535159 : ℕ)^2211*100000000000000^1699 ≤ 10274892305829^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217535159 1250000000 10274892305829 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (743335121/1250000000 : ℝ)^2211 ≤ (50845375477717/100000000000000 : ℝ)^1699 := by
    have hnat : (743335121 : ℕ)^2211*100000000000000^1699 ≤ 50845375477717^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743335121 1250000000 50845375477717 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838723577/10000000000 : ℝ)^2211 ≤ (38879732199239/100000000000000 : ℝ)^1699 := by
    have hnat : (4838723577 : ℕ)^2211*100000000000000^1699 ≤ 38879732199239^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838723577 10000000000 38879732199239 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217535159/1250000000 : ℝ), (743335121/1250000000 : ℝ), (4838723577/10000000000 : ℝ)] ![(10274892305829/100000000000000 : ℝ), (50845375477717/100000000000000 : ℝ), (38879732199239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217535159/1250000000 : ℝ)|^2211 ≤ (10274892305829/100000000000000 : ℝ)^1699
        have hw : |(-217535159/1250000000 : ℝ)|=(217535159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(743335121/1250000000 : ℝ)|^2211 ≤ (50845375477717/100000000000000 : ℝ)^1699
        have hw : |(743335121/1250000000 : ℝ)|=(743335121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4838723577/10000000000 : ℝ)|^2211 ≤ (38879732199239/100000000000000 : ℝ)^1699
        have hw : |(4838723577/10000000000 : ℝ)|=(4838723577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s0_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1097687103/2000000000 : ℝ)*x 0 + (-2364746213/10000000000 : ℝ)*x 1 + (151210111/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097687103/2000000000 : ℝ)^2211 ≤ (9161369784901/20000000000000 : ℝ)^1699 := by
    have hnat : (1097687103 : ℕ)^2211*20000000000000^1699 ≤ 9161369784901^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097687103 2000000000 9161369784901 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2364746213/10000000000 : ℝ)^2211 ≤ (15313419112907/100000000000000 : ℝ)^1699 := by
    have hnat : (2364746213 : ℕ)^2211*100000000000000^1699 ≤ 15313419112907^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364746213 10000000000 15313419112907 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151210111/312500000 : ℝ)^2211 ≤ (19439865968913/50000000000000 : ℝ)^1699 := by
    have hnat : (151210111 : ℕ)^2211*50000000000000^1699 ≤ 19439865968913^1699*312500000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151210111 312500000 19439865968913 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097687103/2000000000 : ℝ), (-2364746213/10000000000 : ℝ), (151210111/312500000 : ℝ)] ![(9161369784901/20000000000000 : ℝ), (15313419112907/100000000000000 : ℝ), (19439865968913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097687103/2000000000 : ℝ)|^2211 ≤ (9161369784901/20000000000000 : ℝ)^1699
        have hw : |(1097687103/2000000000 : ℝ)|=(1097687103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2364746213/10000000000 : ℝ)|^2211 ≤ (15313419112907/100000000000000 : ℝ)^1699
        have hw : |(-2364746213/10000000000 : ℝ)|=(2364746213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151210111/312500000 : ℝ)|^2211 ≤ (19439865968913/50000000000000 : ℝ)^1699
        have hw : |(151210111/312500000 : ℝ)|=(151210111/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s0_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2744217783/5000000000 : ℝ)*x 0 + (4838723521/10000000000 : ℝ)*x 1 + (-1182373093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744217783/5000000000 : ℝ)^2211 ≤ (1832273979137/4000000000000 : ℝ)^1699 := by
    have hnat : (2744217783 : ℕ)^2211*4000000000000^1699 ≤ 1832273979137^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744217783 5000000000 1832273979137 4000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4838723521/10000000000 : ℝ)^2211 ≤ (38879731613673/100000000000000 : ℝ)^1699 := by
    have hnat : (4838723521 : ℕ)^2211*100000000000000^1699 ≤ 38879731613673^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838723521 10000000000 38879731613673 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182373093/5000000000 : ℝ)^2211 ≤ (3828354721343/25000000000000 : ℝ)^1699 := by
    have hnat : (1182373093 : ℕ)^2211*25000000000000^1699 ≤ 3828354721343^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182373093 5000000000 3828354721343 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744217783/5000000000 : ℝ), (4838723521/10000000000 : ℝ), (-1182373093/5000000000 : ℝ)] ![(1832273979137/4000000000000 : ℝ), (38879731613673/100000000000000 : ℝ), (3828354721343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744217783/5000000000 : ℝ)|^2211 ≤ (1832273979137/4000000000000 : ℝ)^1699
        have hw : |(2744217783/5000000000 : ℝ)|=(2744217783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4838723521/10000000000 : ℝ)|^2211 ≤ (38879731613673/100000000000000 : ℝ)^1699
        have hw : |(4838723521/10000000000 : ℝ)|=(4838723521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1182373093/5000000000 : ℝ)|^2211 ≤ (3828354721343/25000000000000 : ℝ)^1699
        have hw : |(-1182373093/5000000000 : ℝ)|=(1182373093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s0_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4161303597/10000000000 : ℝ)*x 0 + (3102687931/10000000000 : ℝ)*x 1 + (276429033/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4161303597/10000000000 : ℝ)^2211 ≤ (31950875207281/100000000000000 : ℝ)^1699 := by
    have hnat : (4161303597 : ℕ)^2211*100000000000000^1699 ≤ 31950875207281^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161303597 10000000000 31950875207281 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102687931/10000000000 : ℝ)^2211 ≤ (21805772263499/100000000000000 : ℝ)^1699 := by
    have hnat : (3102687931 : ℕ)^2211*100000000000000^1699 ≤ 21805772263499^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102687931 10000000000 21805772263499 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276429033/500000000 : ℝ)^2211 ≤ (46243352512267/100000000000000 : ℝ)^1699 := by
    have hnat : (276429033 : ℕ)^2211*100000000000000^1699 ≤ 46243352512267^1699*500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276429033 500000000 46243352512267 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4161303597/10000000000 : ℝ), (3102687931/10000000000 : ℝ), (276429033/500000000 : ℝ)] ![(31950875207281/100000000000000 : ℝ), (21805772263499/100000000000000 : ℝ), (46243352512267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4161303597/10000000000 : ℝ)|^2211 ≤ (31950875207281/100000000000000 : ℝ)^1699
        have hw : |(4161303597/10000000000 : ℝ)|=(4161303597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102687931/10000000000 : ℝ)|^2211 ≤ (21805772263499/100000000000000 : ℝ)^1699
        have hw : |(3102687931/10000000000 : ℝ)|=(3102687931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276429033/500000000 : ℝ)|^2211 ≤ (46243352512267/100000000000000 : ℝ)^1699
        have hw : |(276429033/500000000 : ℝ)|=(276429033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s0_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-348828473/2000000000 : ℝ)*x 0 + (973399423/2000000000 : ℝ)*x 1 + (2958699257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (348828473/2000000000 : ℝ)^2211 ≤ (10304568523227/100000000000000 : ℝ)^1699 := by
    have hnat : (348828473 : ℕ)^2211*100000000000000^1699 ≤ 10304568523227^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348828473 2000000000 10304568523227 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973399423/2000000000 : ℝ)^2211 ≤ (39175635393293/100000000000000 : ℝ)^1699 := by
    have hnat : (973399423 : ℕ)^2211*100000000000000^1699 ≤ 39175635393293^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973399423 2000000000 39175635393293 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2958699257/5000000000 : ℝ)^2211 ≤ (25259898033051/50000000000000 : ℝ)^1699 := by
    have hnat : (2958699257 : ℕ)^2211*50000000000000^1699 ≤ 25259898033051^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958699257 5000000000 25259898033051 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-348828473/2000000000 : ℝ), (973399423/2000000000 : ℝ), (2958699257/5000000000 : ℝ)] ![(10304568523227/100000000000000 : ℝ), (39175635393293/100000000000000 : ℝ), (25259898033051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-348828473/2000000000 : ℝ)|^2211 ≤ (10304568523227/100000000000000 : ℝ)^1699
        have hw : |(-348828473/2000000000 : ℝ)|=(348828473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973399423/2000000000 : ℝ)|^2211 ≤ (39175635393293/100000000000000 : ℝ)^1699
        have hw : |(973399423/2000000000 : ℝ)|=(973399423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2958699257/5000000000 : ℝ)|^2211 ≤ (25259898033051/50000000000000 : ℝ)^1699
        have hw : |(2958699257/5000000000 : ℝ)|=(2958699257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s0_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2592946063/5000000000 : ℝ)*x 0 + (-51442843/400000000 : ℝ)*x 1 + (5917398587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592946063/5000000000 : ℝ)^2211 ≤ (42548520954279/100000000000000 : ℝ)^1699 := by
    have hnat : (2592946063 : ℕ)^2211*100000000000000^1699 ≤ 42548520954279^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592946063 5000000000 42548520954279 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51442843/400000000 : ℝ)^2211 ≤ (3465841077771/50000000000000 : ℝ)^1699 := by
    have hnat : (51442843 : ℕ)^2211*50000000000000^1699 ≤ 3465841077771^1699*400000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51442843 400000000 3465841077771 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5917398587/10000000000 : ℝ)^2211 ≤ (10103959375431/20000000000000 : ℝ)^1699 := by
    have hnat : (5917398587 : ℕ)^2211*20000000000000^1699 ≤ 10103959375431^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5917398587 10000000000 10103959375431 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592946063/5000000000 : ℝ), (-51442843/400000000 : ℝ), (5917398587/10000000000 : ℝ)] ![(42548520954279/100000000000000 : ℝ), (3465841077771/50000000000000 : ℝ), (10103959375431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592946063/5000000000 : ℝ)|^2211 ≤ (42548520954279/100000000000000 : ℝ)^1699
        have hw : |(2592946063/5000000000 : ℝ)|=(2592946063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51442843/400000000 : ℝ)|^2211 ≤ (3465841077771/50000000000000 : ℝ)^1699
        have hw : |(-51442843/400000000 : ℝ)|=(51442843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5917398587/10000000000 : ℝ)|^2211 ≤ (10103959375431/20000000000000 : ℝ)^1699
        have hw : |(5917398587/10000000000 : ℝ)|=(5917398587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s0_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5185892163/10000000000 : ℝ)*x 0 + (739674803/1250000000 : ℝ)*x 1 + (-1286071277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185892163/10000000000 : ℝ)^2211 ≤ (21274260674667/50000000000000 : ℝ)^1699 := by
    have hnat : (5185892163 : ℕ)^2211*50000000000000^1699 ≤ 21274260674667^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185892163 10000000000 21274260674667 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739674803/1250000000 : ℝ)^2211 ≤ (25259897533087/50000000000000 : ℝ)^1699 := by
    have hnat : (739674803 : ℕ)^2211*50000000000000^1699 ≤ 25259897533087^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739674803 1250000000 25259897533087 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286071277/10000000000 : ℝ)^2211 ≤ (6931683572381/100000000000000 : ℝ)^1699 := by
    have hnat : (1286071277 : ℕ)^2211*100000000000000^1699 ≤ 6931683572381^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286071277 10000000000 6931683572381 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185892163/10000000000 : ℝ), (739674803/1250000000 : ℝ), (-1286071277/10000000000 : ℝ)] ![(21274260674667/50000000000000 : ℝ), (25259897533087/50000000000000 : ℝ), (6931683572381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185892163/10000000000 : ℝ)|^2211 ≤ (21274260674667/50000000000000 : ℝ)^1699
        have hw : |(5185892163/10000000000 : ℝ)|=(5185892163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(739674803/1250000000 : ℝ)|^2211 ≤ (25259897533087/50000000000000 : ℝ)^1699
        have hw : |(739674803/1250000000 : ℝ)|=(739674803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1286071277/10000000000 : ℝ)|^2211 ≤ (6931683572381/100000000000000 : ℝ)^1699
        have hw : |(-1286071277/10000000000 : ℝ)|=(1286071277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s0_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4169757883/10000000000 : ℝ)*x 0 + (5466675143/10000000000 : ℝ)*x 1 + (3166802471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169757883/10000000000 : ℝ)^2211 ≤ (32035375559677/100000000000000 : ℝ)^1699 := by
    have hnat : (4169757883 : ℕ)^2211*100000000000000^1699 ≤ 32035375559677^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169757883 10000000000 32035375559677 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466675143/10000000000 : ℝ)^2211 ≤ (45570646818179/100000000000000 : ℝ)^1699 := by
    have hnat : (5466675143 : ℕ)^2211*100000000000000^1699 ≤ 45570646818179^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466675143 10000000000 45570646818179 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3166802471/10000000000 : ℝ)^2211 ≤ (22393977605759/100000000000000 : ℝ)^1699 := by
    have hnat : (3166802471 : ℕ)^2211*100000000000000^1699 ≤ 22393977605759^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3166802471 10000000000 22393977605759 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169757883/10000000000 : ℝ), (5466675143/10000000000 : ℝ), (3166802471/10000000000 : ℝ)] ![(32035375559677/100000000000000 : ℝ), (45570646818179/100000000000000 : ℝ), (22393977605759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169757883/10000000000 : ℝ)|^2211 ≤ (32035375559677/100000000000000 : ℝ)^1699
        have hw : |(4169757883/10000000000 : ℝ)|=(4169757883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466675143/10000000000 : ℝ)|^2211 ≤ (45570646818179/100000000000000 : ℝ)^1699
        have hw : |(5466675143/10000000000 : ℝ)|=(5466675143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3166802471/10000000000 : ℝ)|^2211 ≤ (22393977605759/100000000000000 : ℝ)^1699
        have hw : |(3166802471/10000000000 : ℝ)|=(3166802471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1627/6250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4421/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4421 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4421*1^1024 ≤ 0^1024*1^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4421/1024 : ℝ) ≤ (478498581685422609/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4421 ≤ (478498581685422609/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4421*25000000000000000000^1024 ≤ 478498581685422609^1024*5^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 478498581685422609 25000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (478498581685422609/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4421 := by
      have hnat : (1 : ℕ)^1024*1^4421 ≤ 1^4421*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25478498581685422609/25000000000000000000 : ℝ) ≤ (2511002480207897/2500000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (25478498581685422609/25000000000000000000 : ℝ)^1024 ≤ (2511002480207897/2500000000000000 : ℝ)^4421 := by
      have hnat : (25478498581685422609 : ℕ)^1024*2500000000000000^4421 ≤ 2511002480207897^4421*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25478498581685422609 25000000000000000000 2511002480207897 2500000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511002480207897/2500000000000000 : ℝ)) (X := (25478498581685422609/25000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12978498581685422609/12500000000000000000 : ℝ) ≤ (1261002480207897/1250000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (12978498581685422609/12500000000000000000 : ℝ)^1024 ≤ (1261002480207897/1250000000000000 : ℝ)^4421 := by
      have hnat : (12978498581685422609 : ℕ)^1024*1250000000000000^4421 ≤ 1261002480207897^4421*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12978498581685422609 12500000000000000000 1261002480207897 1250000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261002480207897/1250000000000000 : ℝ)) (X := (12978498581685422609/12500000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11002480207897/1000000000000000 : ℝ)*(0 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11002480207897/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(478498581685422609/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11002480207897/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11002480207897/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511002480207897/2500000000000000 : ℝ) by norm_num, show 1+(478498581685422609/25000000000000000000 : ℝ)+(0 : ℝ)=(25478498581685422609/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(478498581685422609/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11002480207897/1000000000000000 : ℝ)*(2/5 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11002480207897/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261002480207897/1250000000000000 : ℝ) by norm_num, show 1+2*(478498581685422609/25000000000000000000 : ℝ)=(12978498581685422609/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11002480207897/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11002480207897/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11002480207897/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11002480207897/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11002480207897/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11002480207897/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217535159/1250000000 : ℝ)*X 0 0+(743335121/1250000000 : ℝ)*X 0 1+(4838723577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1097687103/2000000000 : ℝ)*X 1 0+(-2364746213/10000000000 : ℝ)*X 1 1+(151210111/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2744217783/5000000000 : ℝ)*X 2 0+(4838723521/10000000000 : ℝ)*X 2 1+(-1182373093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4161303597/10000000000 : ℝ)*X 0 0+(3102687931/10000000000 : ℝ)*X 0 1+(276429033/500000000 : ℝ)*X 0 2+(4161303597/10000000000 : ℝ)*X 1 0+(3102687931/10000000000 : ℝ)*X 1 1+(276429033/500000000 : ℝ)*X 1 2+(4161303597/10000000000 : ℝ)*X 2 0+(3102687931/10000000000 : ℝ)*X 2 1+(276429033/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-348828473/2000000000 : ℝ)*X 0 0+(973399423/2000000000 : ℝ)*X 0 1+(2958699257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2592946063/5000000000 : ℝ)*X 1 0+(-51442843/400000000 : ℝ)*X 1 1+(5917398587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185892163/10000000000 : ℝ)*X 2 0+(739674803/1250000000 : ℝ)*X 2 1+(-1286071277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4169757883/10000000000 : ℝ)*X 0 0+(5466675143/10000000000 : ℝ)*X 0 1+(3166802471/10000000000 : ℝ)*X 0 2+(4169757883/10000000000 : ℝ)*X 1 0+(5466675143/10000000000 : ℝ)*X 1 1+(3166802471/10000000000 : ℝ)*X 1 2+(4169757883/10000000000 : ℝ)*X 2 0+(5466675143/10000000000 : ℝ)*X 2 1+(3166802471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61104828347241125414103/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5883543/10000000000000 : ℝ)*(base1) + (222934693/20000000000000 : ℝ)*(base19) + (561530183/50000000000000 : ℝ)*(base23) + (66149641/50000000000000 : ℝ)*(upper3) + (142217571/100000000000000 : ℝ)*(upper5) + (657396024100333/100000000000000 : ℝ)*(major0) + (657396024100333/100000000000000 : ℝ)*(major1) + (657396024100333/100000000000000 : ℝ)*(major2) + (902565332451917/100000000000000 : ℝ)*(sp0) + (225641995281383/25000000000000 : ℝ)*(sp1) + (902567972738631/100000000000000 : ℝ)*(sp2) + (412221022968821/100000000000000 : ℝ)*(sp3) + (382218251/10000000000000 : ℝ)*(sp4) + (853825603/50000000000000 : ℝ)*(sp7) + (12881962170483/3125000000000 : ℝ)*(f.failure) + (902569095798997/100000000000000 : ℝ)*(f.sum) + (138475346120299/50000000000000000000000000000 : ℝ)*base66 + (330216384570299/100000000000000000000000000000 : ℝ)*base68 + (231758686570299/100000000000000000000000000000 : ℝ)*base70 + (65069274570299/100000000000000000000000000000 : ℝ)*base72 + (316229847720299/50000000000000000000000000000 : ℝ)*base74 + (344302071929701/100000000000000000000000000000 : ℝ)*base75 + (195117391170299/100000000000000000000000000000 : ℝ)*base78 + (286527070929701/100000000000000000000000000000 : ℝ)*base79 + (341872799070299/50000000000000000000000000000 : ℝ)*base82 + (17423/62500000000000000000 : ℝ)*base89 + (17423/62500000000000000000 : ℝ)*base91 + (17423/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50367708598956965824047/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (462466871/50000000000000 : ℝ)*(base19) + (933998197/100000000000000 : ℝ)*(base23) + (6823249/6250000000000 : ℝ)*(base32) + (17777929/12500000000000 : ℝ)*(upper3) + (78416821/100000000000000 : ℝ)*(upper5) + (346705796211061/50000000000000 : ℝ)*(major0) + (346705796211061/50000000000000 : ℝ)*(major1) + (346705796211061/50000000000000 : ℝ)*(major2) + (22466439/1000000000000 : ℝ)*(sp1) + (571397327/25000000000000 : ℝ)*(sp2) + (952016555830019/100000000000000 : ℝ)*(sp4) + (119001673031547/12500000000000 : ℝ)*(sp5) + (476006668121257/50000000000000 : ℝ)*(sp6) + (434806385528341/100000000000000 : ℝ)*(sp7) + (217403247350163/50000000000000 : ℝ)*(f.failure) + (952016555830019/100000000000000 : ℝ)*(f.sum) + (41145991748717/25000000000000000000000000000 : ℝ)*base65 + (490840023548717/50000000000000000000000000000 : ℝ)*base67 + (500020052098717/50000000000000000000000000000 : ℝ)*base69 + (548448071998717/50000000000000000000000000000 : ℝ)*base71 + (96632349373717/25000000000000000000000000000 : ℝ)*base73 + (639333364798717/50000000000000000000000000000 : ℝ)*base75 + (293285760298717/50000000000000000000000000000 : ℝ)*base77 + (516454212598717/50000000000000000000000000000 : ℝ)*base79 + (126789147323717/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (735497/1000000000000000000000 : ℝ)*base90 + (735497/1000000000000000000000 : ℝ)*base92 + (735497/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1462_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1627/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1462_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1462_s1_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1907982709/10000000000 : ℝ)*x 0 + (2796141351/5000000000 : ℝ)*x 1 + (31784713/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1907982709/10000000000 : ℝ)^2211 ≤ (5790857205581/50000000000000 : ℝ)^1699 := by
    have hnat : (1907982709 : ℕ)^2211*50000000000000^1699 ≤ 5790857205581^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907982709 10000000000 5790857205581 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796141351/5000000000 : ℝ)^2211 ≤ (5867244251029/12500000000000 : ℝ)^1699 := by
    have hnat : (2796141351 : ℕ)^2211*12500000000000^1699 ≤ 5867244251029^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796141351 5000000000 5867244251029 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31784713/62500000 : ℝ)^2211 ≤ (10370082891449/25000000000000 : ℝ)^1699 := by
    have hnat : (31784713 : ℕ)^2211*25000000000000^1699 ≤ 10370082891449^1699*62500000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31784713 62500000 10370082891449 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1907982709/10000000000 : ℝ), (2796141351/5000000000 : ℝ), (31784713/62500000 : ℝ)] ![(5790857205581/50000000000000 : ℝ), (5867244251029/12500000000000 : ℝ), (10370082891449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1907982709/10000000000 : ℝ)|^2211 ≤ (5790857205581/50000000000000 : ℝ)^1699
        have hw : |(-1907982709/10000000000 : ℝ)|=(1907982709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796141351/5000000000 : ℝ)|^2211 ≤ (5867244251029/12500000000000 : ℝ)^1699
        have hw : |(2796141351/5000000000 : ℝ)|=(2796141351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31784713/62500000 : ℝ)|^2211 ≤ (10370082891449/25000000000000 : ℝ)^1699
        have hw : |(31784713/62500000 : ℝ)|=(31784713/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s1_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1348381433/2500000000 : ℝ)*x 0 + (-2175831711/10000000000 : ℝ)*x 1 + (5085556221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348381433/2500000000 : ℝ)^2211 ≤ (44778713045727/100000000000000 : ℝ)^1699 := by
    have hnat : (1348381433 : ℕ)^2211*100000000000000^1699 ≤ 44778713045727^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348381433 2500000000 44778713045727 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175831711/10000000000 : ℝ)^2211 ≤ (6870466326917/50000000000000 : ℝ)^1699 := by
    have hnat : (2175831711 : ℕ)^2211*50000000000000^1699 ≤ 6870466326917^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175831711 10000000000 6870466326917 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5085556221/10000000000 : ℝ)^2211 ≤ (4148035429143/10000000000000 : ℝ)^1699 := by
    have hnat : (5085556221 : ℕ)^2211*10000000000000^1699 ≤ 4148035429143^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085556221 10000000000 4148035429143 10000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348381433/2500000000 : ℝ), (-2175831711/10000000000 : ℝ), (5085556221/10000000000 : ℝ)] ![(44778713045727/100000000000000 : ℝ), (6870466326917/50000000000000 : ℝ), (4148035429143/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348381433/2500000000 : ℝ)|^2211 ≤ (44778713045727/100000000000000 : ℝ)^1699
        have hw : |(1348381433/2500000000 : ℝ)|=(1348381433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2175831711/10000000000 : ℝ)|^2211 ≤ (6870466326917/50000000000000 : ℝ)^1699
        have hw : |(-2175831711/10000000000 : ℝ)|=(2175831711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5085556221/10000000000 : ℝ)|^2211 ≤ (4148035429143/10000000000000 : ℝ)^1699
        have hw : |(5085556221/10000000000 : ℝ)|=(5085556221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s1_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1078705507/2000000000 : ℝ)*x 0 + (5085554241/10000000000 : ℝ)*x 1 + (-2175831897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078705507/2000000000 : ℝ)^2211 ≤ (11194683131443/25000000000000 : ℝ)^1699 := by
    have hnat : (1078705507 : ℕ)^2211*25000000000000^1699 ≤ 11194683131443^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078705507 2000000000 11194683131443 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085554241/10000000000 : ℝ)^2211 ≤ (4148033327473/10000000000000 : ℝ)^1699 := by
    have hnat : (5085554241 : ℕ)^2211*10000000000000^1699 ≤ 4148033327473^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085554241 10000000000 4148033327473 10000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175831897/10000000000 : ℝ)^2211 ≤ (13740934182453/100000000000000 : ℝ)^1699 := by
    have hnat : (2175831897 : ℕ)^2211*100000000000000^1699 ≤ 13740934182453^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175831897 10000000000 13740934182453 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078705507/2000000000 : ℝ), (5085554241/10000000000 : ℝ), (-2175831897/10000000000 : ℝ)] ![(11194683131443/25000000000000 : ℝ), (4148033327473/10000000000000 : ℝ), (13740934182453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078705507/2000000000 : ℝ)|^2211 ≤ (11194683131443/25000000000000 : ℝ)^1699
        have hw : |(1078705507/2000000000 : ℝ)|=(1078705507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085554241/10000000000 : ℝ)|^2211 ≤ (4148033327473/10000000000000 : ℝ)^1699
        have hw : |(5085554241/10000000000 : ℝ)|=(5085554241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175831897/10000000000 : ℝ)|^2211 ≤ (13740934182453/100000000000000 : ℝ)^1699
        have hw : |(-2175831897/10000000000 : ℝ)|=(2175831897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s1_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4270625097/10000000000 : ℝ)*x 0 + (93690041/250000000 : ℝ)*x 1 + (303568037/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270625097/10000000000 : ℝ)^2211 ≤ (16523752034499/50000000000000 : ℝ)^1699 := by
    have hnat : (4270625097 : ℕ)^2211*50000000000000^1699 ≤ 16523752034499^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270625097 10000000000 16523752034499 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93690041/250000000 : ℝ)^2211 ≤ (13940309782493/50000000000000 : ℝ)^1699 := by
    have hnat : (93690041 : ℕ)^2211*50000000000000^1699 ≤ 13940309782493^1699*250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93690041 250000000 13940309782493 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303568037/625000000 : ℝ)^2211 ≤ (19535938177323/50000000000000 : ℝ)^1699 := by
    have hnat : (303568037 : ℕ)^2211*50000000000000^1699 ≤ 19535938177323^1699*625000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303568037 625000000 19535938177323 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270625097/10000000000 : ℝ), (93690041/250000000 : ℝ), (303568037/625000000 : ℝ)] ![(16523752034499/50000000000000 : ℝ), (13940309782493/50000000000000 : ℝ), (19535938177323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270625097/10000000000 : ℝ)|^2211 ≤ (16523752034499/50000000000000 : ℝ)^1699
        have hw : |(4270625097/10000000000 : ℝ)|=(4270625097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93690041/250000000 : ℝ)|^2211 ≤ (13940309782493/50000000000000 : ℝ)^1699
        have hw : |(93690041/250000000 : ℝ)|=(93690041/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(303568037/625000000 : ℝ)|^2211 ≤ (19535938177323/50000000000000 : ℝ)^1699
        have hw : |(303568037/625000000 : ℝ)|=(303568037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s1_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-381667629/2000000000 : ℝ)*x 0 + (509134399/1000000000 : ℝ)*x 1 + (5586397211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381667629/2000000000 : ℝ)^2211 ≤ (22626019959/195312500000 : ℝ)^1699 := by
    have hnat : (381667629 : ℕ)^2211*195312500000^1699 ≤ 22626019959^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381667629 2000000000 22626019959 195312500000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509134399/1000000000 : ℝ)^2211 ≤ (20770899536031/50000000000000 : ℝ)^1699 := by
    have hnat : (509134399 : ℕ)^2211*50000000000000^1699 ≤ 20770899536031^1699*1000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509134399 1000000000 20770899536031 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5586397211/10000000000 : ℝ)^2211 ≤ (46873678693863/100000000000000 : ℝ)^1699 := by
    have hnat : (5586397211 : ℕ)^2211*100000000000000^1699 ≤ 46873678693863^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586397211 10000000000 46873678693863 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-381667629/2000000000 : ℝ), (509134399/1000000000 : ℝ), (5586397211/10000000000 : ℝ)] ![(22626019959/195312500000 : ℝ), (20770899536031/50000000000000 : ℝ), (46873678693863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-381667629/2000000000 : ℝ)|^2211 ≤ (22626019959/195312500000 : ℝ)^1699
        have hw : |(-381667629/2000000000 : ℝ)|=(381667629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(509134399/1000000000 : ℝ)|^2211 ≤ (20770899536031/50000000000000 : ℝ)^1699
        have hw : |(509134399/1000000000 : ℝ)|=(509134399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5586397211/10000000000 : ℝ)|^2211 ≤ (46873678693863/100000000000000 : ℝ)^1699
        have hw : |(5586397211/10000000000 : ℝ)|=(5586397211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s1_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5260815527/10000000000 : ℝ)*x 0 + (-209373739/1250000000 : ℝ)*x 1 + (5586397249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260815527/10000000000 : ℝ)^2211 ≤ (43350226844113/100000000000000 : ℝ)^1699 := by
    have hnat : (5260815527 : ℕ)^2211*100000000000000^1699 ≤ 43350226844113^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260815527 10000000000 43350226844113 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209373739/1250000000 : ℝ)^2211 ≤ (9776094042719/100000000000000 : ℝ)^1699 := by
    have hnat : (209373739 : ℕ)^2211*100000000000000^1699 ≤ 9776094042719^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209373739 1250000000 9776094042719 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5586397249/10000000000 : ℝ)^2211 ≤ (23436839554397/50000000000000 : ℝ)^1699 := by
    have hnat : (5586397249 : ℕ)^2211*50000000000000^1699 ≤ 23436839554397^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586397249 10000000000 23436839554397 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260815527/10000000000 : ℝ), (-209373739/1250000000 : ℝ), (5586397249/10000000000 : ℝ)] ![(43350226844113/100000000000000 : ℝ), (9776094042719/100000000000000 : ℝ), (23436839554397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260815527/10000000000 : ℝ)|^2211 ≤ (43350226844113/100000000000000 : ℝ)^1699
        have hw : |(5260815527/10000000000 : ℝ)|=(5260815527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209373739/1250000000 : ℝ)|^2211 ≤ (9776094042719/100000000000000 : ℝ)^1699
        have hw : |(-209373739/1250000000 : ℝ)|=(209373739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5586397249/10000000000 : ℝ)|^2211 ≤ (23436839554397/50000000000000 : ℝ)^1699
        have hw : |(5586397249/10000000000 : ℝ)|=(5586397249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s1_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2630407701/5000000000 : ℝ)*x 0 + (5586397217/10000000000 : ℝ)*x 1 + (-1674990133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630407701/5000000000 : ℝ)^2211 ≤ (10837556375921/25000000000000 : ℝ)^1699 := by
    have hnat : (2630407701 : ℕ)^2211*25000000000000^1699 ≤ 10837556375921^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630407701 5000000000 10837556375921 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5586397217/10000000000 : ℝ)^2211 ≤ (23436839379689/50000000000000 : ℝ)^1699 := by
    have hnat : (5586397217 : ℕ)^2211*50000000000000^1699 ≤ 23436839379689^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586397217 10000000000 23436839379689 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674990133/10000000000 : ℝ)^2211 ≤ (1955219144259/20000000000000 : ℝ)^1699 := by
    have hnat : (1674990133 : ℕ)^2211*20000000000000^1699 ≤ 1955219144259^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674990133 10000000000 1955219144259 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630407701/5000000000 : ℝ), (5586397217/10000000000 : ℝ), (-1674990133/10000000000 : ℝ)] ![(10837556375921/25000000000000 : ℝ), (23436839379689/50000000000000 : ℝ), (1955219144259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630407701/5000000000 : ℝ)|^2211 ≤ (10837556375921/25000000000000 : ℝ)^1699
        have hw : |(2630407701/5000000000 : ℝ)|=(2630407701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5586397217/10000000000 : ℝ)|^2211 ≤ (23436839379689/50000000000000 : ℝ)^1699
        have hw : |(5586397217/10000000000 : ℝ)|=(5586397217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1674990133/10000000000 : ℝ)|^2211 ≤ (1955219144259/20000000000000 : ℝ)^1699
        have hw : |(-1674990133/10000000000 : ℝ)|=(1674990133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s1_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (854280829/2000000000 : ℝ)*x 0 + (2422206669/5000000000 : ℝ)*x 1 + (3760484759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854280829/2000000000 : ℝ)^2211 ≤ (16527674767403/50000000000000 : ℝ)^1699 := by
    have hnat : (854280829 : ℕ)^2211*50000000000000^1699 ≤ 16527674767403^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854280829 2000000000 16527674767403 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422206669/5000000000 : ℝ)^2211 ≤ (1946961896271/5000000000000 : ℝ)^1699 := by
    have hnat : (2422206669 : ℕ)^2211*5000000000000^1699 ≤ 1946961896271^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422206669 5000000000 1946961896271 5000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3760484759/10000000000 : ℝ)^2211 ≤ (28005412529203/100000000000000 : ℝ)^1699 := by
    have hnat : (3760484759 : ℕ)^2211*100000000000000^1699 ≤ 28005412529203^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760484759 10000000000 28005412529203 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854280829/2000000000 : ℝ), (2422206669/5000000000 : ℝ), (3760484759/10000000000 : ℝ)] ![(16527674767403/50000000000000 : ℝ), (1946961896271/5000000000000 : ℝ), (28005412529203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854280829/2000000000 : ℝ)|^2211 ≤ (16527674767403/50000000000000 : ℝ)^1699
        have hw : |(854280829/2000000000 : ℝ)|=(854280829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2422206669/5000000000 : ℝ)|^2211 ≤ (1946961896271/5000000000000 : ℝ)^1699
        have hw : |(2422206669/5000000000 : ℝ)|=(2422206669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3760484759/10000000000 : ℝ)|^2211 ≤ (28005412529203/100000000000000 : ℝ)^1699
        have hw : |(3760484759/10000000000 : ℝ)|=(3760484759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1627/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7917/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2329/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1627/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1627/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1627/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1627/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1627/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1627/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1139/50000 : ℝ) ^ (4421/1024 : ℝ) ≤ (506769742233/6250000000000000000 : ℝ) := by
    have hpowers : (1139/50000 : ℝ)^4421 ≤ (506769742233/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1139 : ℕ)^4421*6250000000000000000^1024 ≤ 506769742233^1024*50000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1139 50000 506769742233 6250000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1139/50000 : ℝ)) (X := (506769742233/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1627/6250 : ℝ) ^ (4421/1024 : ℝ) ≤ (29958652820697901/10000000000000000000 : ℝ) := by
    have hpowers : (1627/6250 : ℝ)^4421 ≤ (29958652820697901/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1627 : ℕ)^4421*10000000000000000000^1024 ≤ 29958652820697901^1024*6250^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1627 6250 29958652820697901 10000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1627/6250 : ℝ)) (X := (29958652820697901/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000506769742233/3125000000000000000 : ℝ) ≤ (10000000375612529/10000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (3125000506769742233/3125000000000000000 : ℝ)^1024 ≤ (10000000375612529/10000000000000000 : ℝ)^4421 := by
      have hnat : (3125000506769742233 : ℕ)^1024*10000000000000000^4421 ≤ 10000000375612529^4421*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000506769742233 3125000000000000000 10000000375612529 10000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000375612529/10000000000000000 : ℝ)) (X := (3125000506769742233/3125000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50149797318261427369/50000000000000000000 : ℝ) ≤ (5003465645980849/5000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (50149797318261427369/50000000000000000000 : ℝ)^1024 ≤ (5003465645980849/5000000000000000 : ℝ)^4421 := by
      have hnat : (50149797318261427369 : ℕ)^1024*5000000000000000^4421 ≤ 5003465645980849^4421*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50149797318261427369 50000000000000000000 5003465645980849 5000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003465645980849/5000000000000000 : ℝ)) (X := (50149797318261427369/50000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5029958652820697901/5000000000000000000 : ℝ) ≤ (10013862208310867/10000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (5029958652820697901/5000000000000000000 : ℝ)^1024 ≤ (10013862208310867/10000000000000000 : ℝ)^4421 := by
      have hnat : (5029958652820697901 : ℕ)^1024*10000000000000000^4421 ≤ 10013862208310867^4421*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5029958652820697901 5000000000000000000 10013862208310867 10000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013862208310867/10000000000000000 : ℝ)) (X := (5029958652820697901/5000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(506769742233/6250000000000000000 : ℝ) ≤ ((39584738611235533317/39590000000000000000 : ℝ)+2*(2310305449723/791800000000000 : ℝ)*(1139/50000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (39584738611235533317/39590000000000000000 : ℝ)+2*(2310305449723/791800000000000 : ℝ)*(1139/50000 : ℝ)=(10000000375612529/10000000000000000 : ℝ) by norm_num, show 1+2*(506769742233/6250000000000000000 : ℝ)=(3125000506769742233/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29958652820697901/10000000000000000000 : ℝ)+(506769742233/6250000000000000000 : ℝ) ≤ ((39584738611235533317/39590000000000000000 : ℝ)+(2310305449723/791800000000000 : ℝ)*((1627/6250 : ℝ)+(1139/50000 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (39584738611235533317/39590000000000000000 : ℝ)+(2310305449723/791800000000000 : ℝ)*((1627/6250 : ℝ)+(1139/50000 : ℝ))=(5003465645980849/5000000000000000 : ℝ) by norm_num, show 1+(29958652820697901/10000000000000000000 : ℝ)+(506769742233/6250000000000000000 : ℝ)=(50149797318261427369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29958652820697901/10000000000000000000 : ℝ) ≤ ((39584738611235533317/39590000000000000000 : ℝ)+2*(2310305449723/791800000000000 : ℝ)*(1627/6250 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (39584738611235533317/39590000000000000000 : ℝ)+2*(2310305449723/791800000000000 : ℝ)*(1627/6250 : ℝ)=(10013862208310867/10000000000000000 : ℝ) by norm_num, show 1+2*(29958652820697901/10000000000000000000 : ℝ)=(5029958652820697901/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39584738611235533317/39590000000000000000 : ℝ)*(X 1 0+X 2 0)+(2310305449723/791800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (1139/50000 : ℝ)) (hi := (1627/6250 : ℝ)) (c := (39584738611235533317/39590000000000000000 : ℝ)) (alpha := (2310305449723/791800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39584738611235533317/39590000000000000000 : ℝ)*(X 0 1+X 2 1)+(2310305449723/791800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (1139/50000 : ℝ)) (hi := (1627/6250 : ℝ)) (c := (39584738611235533317/39590000000000000000 : ℝ)) (alpha := (2310305449723/791800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39584738611235533317/39590000000000000000 : ℝ)*(X 0 2+X 1 2)+(2310305449723/791800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (1139/50000 : ℝ)) (hi := (1627/6250 : ℝ)) (c := (39584738611235533317/39590000000000000000 : ℝ)) (alpha := (2310305449723/791800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1907982709/10000000000 : ℝ)*X 0 0+(2796141351/5000000000 : ℝ)*X 0 1+(31784713/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1348381433/2500000000 : ℝ)*X 1 0+(-2175831711/10000000000 : ℝ)*X 1 1+(5085556221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1078705507/2000000000 : ℝ)*X 2 0+(5085554241/10000000000 : ℝ)*X 2 1+(-2175831897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4270625097/10000000000 : ℝ)*X 0 0+(93690041/250000000 : ℝ)*X 0 1+(303568037/625000000 : ℝ)*X 0 2+(4270625097/10000000000 : ℝ)*X 1 0+(93690041/250000000 : ℝ)*X 1 1+(303568037/625000000 : ℝ)*X 1 2+(4270625097/10000000000 : ℝ)*X 2 0+(93690041/250000000 : ℝ)*X 2 1+(303568037/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-381667629/2000000000 : ℝ)*X 0 0+(509134399/1000000000 : ℝ)*X 0 1+(5586397211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260815527/10000000000 : ℝ)*X 1 0+(-209373739/1250000000 : ℝ)*X 1 1+(5586397249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630407701/5000000000 : ℝ)*X 2 0+(5586397217/10000000000 : ℝ)*X 2 1+(-1674990133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854280829/2000000000 : ℝ)*X 0 0+(2422206669/5000000000 : ℝ)*X 0 1+(3760484759/10000000000 : ℝ)*X 0 2+(854280829/2000000000 : ℝ)*X 1 0+(2422206669/5000000000 : ℝ)*X 1 1+(3760484759/10000000000 : ℝ)*X 1 2+(854280829/2000000000 : ℝ)*X 2 0+(2422206669/5000000000 : ℝ)*X 2 1+(3760484759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (871695485937372482959852287/123718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (551766217/50000000000000 : ℝ)*(base19) + (1680301807/100000000000000 : ℝ)*(base23) + (569319/625000000000 : ℝ)*(upper3) + (11183819/25000000000000 : ℝ)*(upper4) + (1636239/2000000000000 : ℝ)*(upper5) + (179675279477887/12500000000000 : ℝ)*(major0) + (179675279477887/12500000000000 : ℝ)*(major1) + (179675279477887/12500000000000 : ℝ)*(major2) + (986729003392689/50000000000000 : ℝ)*(sp0) + (986737174466129/50000000000000 : ℝ)*(sp1) + (493368443040721/25000000000000 : ℝ)*(sp2) + (901322626644671/100000000000000 : ℝ)*(sp3) + (8722839657/50000000000000 : ℝ)*(sp4) + (1231535477/20000000000000 : ℝ)*(sp7) + (112666098040257/12500000000000 : ℝ)*(f.failure) + (493368863116173/25000000000000 : ℝ)*(f.sum) + (14233275123237/2474375000000000000000000000 : ℝ)*base66 + (6443165117555503/4625000000000000000000000000000 : ℝ)*base68 + (26983845334430503/4625000000000000000000000000000 : ℝ)*base70 + (42344986534305503/4625000000000000000000000000000 : ℝ)*base72 + (2368344128533/2474375000000000000000000000 : ℝ)*base73 + (21791087382930503/4625000000000000000000000000000 : ℝ)*base76 + (1234046422805503/4625000000000000000000000000000 : ℝ)*base78 + (4417089552944497/4625000000000000000000000000000 : ℝ)*base79 + (68386201091501/19795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2301517/250000000000000000000 : ℝ)*base89 + (2301517/250000000000000000000 : ℝ)*base91 + (2301517/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (402071613807620513845175793/53500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1660037779/100000000000000 : ℝ)*(base19) + (1670067439/100000000000000 : ℝ)*(base23) + (40301773/20000000000000 : ℝ)*(upper3) + (7857923/25000000000000 : ℝ)*(lower4) + (29792687/20000000000000 : ℝ)*(upper5) + (1471277064151109/100000000000000 : ℝ)*(major0) + (1471277064151109/100000000000000 : ℝ)*(major1) + (1471277064151109/100000000000000 : ℝ)*(major2) + (10758739283/100000000000000 : ℝ)*(sp1) + (2138070571/20000000000000 : ℝ)*(sp2) + (1009991873871973/50000000000000 : ℝ)*(sp4) + (504992832241721/25000000000000 : ℝ)*(sp5) + (2019971387323651/100000000000000 : ℝ)*(sp6) + (23064253251159/2500000000000 : ℝ)*(sp7) + (23064253251159/2500000000000 : ℝ)*(f.failure) + (1009991873871973/50000000000000 : ℝ)*(f.sum) + (1623552033111/1070000000000000000000000000 : ℝ)*base65 + (1788414836031233/1000000000000000000000000000000 : ℝ)*base68 + (353642462031233/1000000000000000000000000000000 : ℝ)*base70 + (1210019159968767/1000000000000000000000000000000 : ℝ)*base71 + (1828193311919/1070000000000000000000000000 : ℝ)*base74 + (1555460484968767/1000000000000000000000000000000 : ℝ)*base75 + (3117722056968767/1000000000000000000000000000000 : ℝ)*base77 + (1181182381968767/1000000000000000000000000000000 : ℝ)*base79 + (3346955017329/1070000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (264779/50000000000000000000 : ℝ)*base89 + (264779/50000000000000000000 : ℝ)*base91 + (264779/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1462_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1627/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7917/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2329/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1462_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1462_s2_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-969363771/5000000000 : ℝ)*x 0 + (5451055051/10000000000 : ℝ)*x 1 + (1301739031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (969363771/5000000000 : ℝ)^2211 ≤ (11825167437063/100000000000000 : ℝ)^1699 := by
    have hnat : (969363771 : ℕ)^2211*100000000000000^1699 ≤ 11825167437063^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969363771 5000000000 11825167437063 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451055051/10000000000 : ℝ)^2211 ≤ (45401270092049/100000000000000 : ℝ)^1699 := by
    have hnat : (5451055051 : ℕ)^2211*100000000000000^1699 ≤ 45401270092049^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451055051 10000000000 45401270092049 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301739031/2500000000 : ℝ)^2211 ≤ (42773562458319/100000000000000 : ℝ)^1699 := by
    have hnat : (1301739031 : ℕ)^2211*100000000000000^1699 ≤ 42773562458319^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301739031 2500000000 42773562458319 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-969363771/5000000000 : ℝ), (5451055051/10000000000 : ℝ), (1301739031/2500000000 : ℝ)] ![(11825167437063/100000000000000 : ℝ), (45401270092049/100000000000000 : ℝ), (42773562458319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-969363771/5000000000 : ℝ)|^2211 ≤ (11825167437063/100000000000000 : ℝ)^1699
        have hw : |(-969363771/5000000000 : ℝ)|=(969363771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451055051/10000000000 : ℝ)|^2211 ≤ (45401270092049/100000000000000 : ℝ)^1699
        have hw : |(5451055051/10000000000 : ℝ)|=(5451055051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301739031/2500000000 : ℝ)|^2211 ≤ (42773562458319/100000000000000 : ℝ)^1699
        have hw : |(1301739031/2500000000 : ℝ)|=(1301739031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s2_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2679045623/5000000000 : ℝ)*x 0 + (-2064143557/10000000000 : ℝ)*x 1 + (5206952811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679045623/5000000000 : ℝ)^2211 ≤ (22198124962711/50000000000000 : ℝ)^1699 := by
    have hnat : (2679045623 : ℕ)^2211*50000000000000^1699 ≤ 22198124962711^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679045623 5000000000 22198124962711 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064143557/10000000000 : ℝ)^2211 ≤ (320755575491/2500000000000 : ℝ)^1699 := by
    have hnat : (2064143557 : ℕ)^2211*2500000000000^1699 ≤ 320755575491^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064143557 10000000000 320755575491 2500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206952811/10000000000 : ℝ)^2211 ≤ (8554705408321/20000000000000 : ℝ)^1699 := by
    have hnat : (5206952811 : ℕ)^2211*20000000000000^1699 ≤ 8554705408321^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206952811 10000000000 8554705408321 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679045623/5000000000 : ℝ), (-2064143557/10000000000 : ℝ), (5206952811/10000000000 : ℝ)] ![(22198124962711/50000000000000 : ℝ), (320755575491/2500000000000 : ℝ), (8554705408321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679045623/5000000000 : ℝ)|^2211 ≤ (22198124962711/50000000000000 : ℝ)^1699
        have hw : |(2679045623/5000000000 : ℝ)|=(2679045623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064143557/10000000000 : ℝ)|^2211 ≤ (320755575491/2500000000000 : ℝ)^1699
        have hw : |(-2064143557/10000000000 : ℝ)|=(2064143557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206952811/10000000000 : ℝ)|^2211 ≤ (8554705408321/20000000000000 : ℝ)^1699
        have hw : |(5206952811/10000000000 : ℝ)|=(5206952811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s2_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1071617849/2000000000 : ℝ)*x 0 + (5206954457/10000000000 : ℝ)*x 1 + (-2064144049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071617849/2000000000 : ℝ)^2211 ≤ (554952854363/1250000000000 : ℝ)^1699 := by
    have hnat : (1071617849 : ℕ)^2211*1250000000000^1699 ≤ 554952854363^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071617849 2000000000 554952854363 1250000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206954457/10000000000 : ℝ)^2211 ≤ (21386772318857/50000000000000 : ℝ)^1699 := by
    have hnat : (5206954457 : ℕ)^2211*50000000000000^1699 ≤ 21386772318857^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206954457 10000000000 21386772318857 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064144049/10000000000 : ℝ)^2211 ≤ (12830226999381/100000000000000 : ℝ)^1699 := by
    have hnat : (2064144049 : ℕ)^2211*100000000000000^1699 ≤ 12830226999381^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064144049 10000000000 12830226999381 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071617849/2000000000 : ℝ), (5206954457/10000000000 : ℝ), (-2064144049/10000000000 : ℝ)] ![(554952854363/1250000000000 : ℝ), (21386772318857/50000000000000 : ℝ), (12830226999381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071617849/2000000000 : ℝ)|^2211 ≤ (554952854363/1250000000000 : ℝ)^1699
        have hw : |(1071617849/2000000000 : ℝ)|=(1071617849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206954457/10000000000 : ℝ)|^2211 ≤ (21386772318857/50000000000000 : ℝ)^1699
        have hw : |(5206954457/10000000000 : ℝ)|=(5206954457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064144049/10000000000 : ℝ)|^2211 ≤ (12830226999381/100000000000000 : ℝ)^1699
        have hw : |(-2064144049/10000000000 : ℝ)|=(2064144049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s2_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2146201587/5000000000 : ℝ)*x 0 + (4032530877/10000000000 : ℝ)*x 1 + (4566997553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146201587/5000000000 : ℝ)^2211 ≤ (33266984239221/100000000000000 : ℝ)^1699 := by
    have hnat : (2146201587 : ℕ)^2211*100000000000000^1699 ≤ 33266984239221^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146201587 5000000000 33266984239221 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032530877/10000000000 : ℝ)^2211 ≤ (30670232458717/100000000000000 : ℝ)^1699 := by
    have hnat : (4032530877 : ℕ)^2211*100000000000000^1699 ≤ 30670232458717^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032530877 10000000000 30670232458717 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4566997553/10000000000 : ℝ)^2211 ≤ (36062783282553/100000000000000 : ℝ)^1699 := by
    have hnat : (4566997553 : ℕ)^2211*100000000000000^1699 ≤ 36062783282553^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566997553 10000000000 36062783282553 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146201587/5000000000 : ℝ), (4032530877/10000000000 : ℝ), (4566997553/10000000000 : ℝ)] ![(33266984239221/100000000000000 : ℝ), (30670232458717/100000000000000 : ℝ), (36062783282553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146201587/5000000000 : ℝ)|^2211 ≤ (33266984239221/100000000000000 : ℝ)^1699
        have hw : |(2146201587/5000000000 : ℝ)|=(2146201587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032530877/10000000000 : ℝ)|^2211 ≤ (30670232458717/100000000000000 : ℝ)^1699
        have hw : |(4032530877/10000000000 : ℝ)|=(4032530877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4566997553/10000000000 : ℝ)|^2211 ≤ (36062783282553/100000000000000 : ℝ)^1699
        have hw : |(4566997553/10000000000 : ℝ)|=(4566997553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s2_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-242345969/1250000000 : ℝ)*x 0 + (1302076509/2500000000 : ℝ)*x 1 + (5449694097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242345969/1250000000 : ℝ)^2211 ≤ (739092912907/6250000000000 : ℝ)^1699 := by
    have hnat : (242345969 : ℕ)^2211*6250000000000^1699 ≤ 739092912907^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242345969 1250000000 739092912907 6250000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302076509/2500000000 : ℝ)^2211 ≤ (42787993885747/100000000000000 : ℝ)^1699 := by
    have hnat : (1302076509 : ℕ)^2211*100000000000000^1699 ≤ 42787993885747^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302076509 2500000000 42787993885747 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449694097/10000000000 : ℝ)^2211 ≤ (45386519484607/100000000000000 : ℝ)^1699 := by
    have hnat : (5449694097 : ℕ)^2211*100000000000000^1699 ≤ 45386519484607^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449694097 10000000000 45386519484607 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-242345969/1250000000 : ℝ), (1302076509/2500000000 : ℝ), (5449694097/10000000000 : ℝ)] ![(739092912907/6250000000000 : ℝ), (42787993885747/100000000000000 : ℝ), (45386519484607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-242345969/1250000000 : ℝ)|^2211 ≤ (739092912907/6250000000000 : ℝ)^1699
        have hw : |(-242345969/1250000000 : ℝ)|=(242345969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302076509/2500000000 : ℝ)|^2211 ≤ (42787993885747/100000000000000 : ℝ)^1699
        have hw : |(1302076509/2500000000 : ℝ)|=(1302076509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449694097/10000000000 : ℝ)|^2211 ≤ (45386519484607/100000000000000 : ℝ)^1699
        have hw : |(5449694097/10000000000 : ℝ)|=(5449694097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s2_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5294423693/10000000000 : ℝ)*x 0 + (-364280497/2000000000 : ℝ)*x 1 + (1089938869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294423693/10000000000 : ℝ)^2211 ≤ (21855484004069/50000000000000 : ℝ)^1699 := by
    have hnat : (5294423693 : ℕ)^2211*50000000000000^1699 ≤ 21855484004069^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294423693 10000000000 21855484004069 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364280497/2000000000 : ℝ)^2211 ≤ (2725627451507/25000000000000 : ℝ)^1699 := by
    have hnat : (364280497 : ℕ)^2211*25000000000000^1699 ≤ 2725627451507^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364280497 2000000000 2725627451507 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089938869/2000000000 : ℝ)^2211 ≤ (45386522172437/100000000000000 : ℝ)^1699 := by
    have hnat : (1089938869 : ℕ)^2211*100000000000000^1699 ≤ 45386522172437^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089938869 2000000000 45386522172437 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294423693/10000000000 : ℝ), (-364280497/2000000000 : ℝ), (1089938869/2000000000 : ℝ)] ![(21855484004069/50000000000000 : ℝ), (2725627451507/25000000000000 : ℝ), (45386522172437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294423693/10000000000 : ℝ)|^2211 ≤ (21855484004069/50000000000000 : ℝ)^1699
        have hw : |(5294423693/10000000000 : ℝ)|=(5294423693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-364280497/2000000000 : ℝ)|^2211 ≤ (2725627451507/25000000000000 : ℝ)^1699
        have hw : |(-364280497/2000000000 : ℝ)|=(364280497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089938869/2000000000 : ℝ)|^2211 ≤ (45386522172437/100000000000000 : ℝ)^1699
        have hw : |(1089938869/2000000000 : ℝ)|=(1089938869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s2_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5294423657/10000000000 : ℝ)*x 0 + (272484731/500000000 : ℝ)*x 1 + (-1821402153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294423657/10000000000 : ℝ)^2211 ≤ (43710967621353/100000000000000 : ℝ)^1699 := by
    have hnat : (5294423657 : ℕ)^2211*100000000000000^1699 ≤ 43710967621353^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294423657 10000000000 43710967621353 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272484731/500000000 : ℝ)^2211 ≤ (22693262576447/50000000000000 : ℝ)^1699 := by
    have hnat : (272484731 : ℕ)^2211*50000000000000^1699 ≤ 22693262576447^1699*500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272484731 500000000 22693262576447 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1821402153/10000000000 : ℝ)^2211 ≤ (2725626804969/25000000000000 : ℝ)^1699 := by
    have hnat : (1821402153 : ℕ)^2211*25000000000000^1699 ≤ 2725626804969^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821402153 10000000000 2725626804969 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294423657/10000000000 : ℝ), (272484731/500000000 : ℝ), (-1821402153/10000000000 : ℝ)] ![(43710967621353/100000000000000 : ℝ), (22693262576447/50000000000000 : ℝ), (2725626804969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294423657/10000000000 : ℝ)|^2211 ≤ (43710967621353/100000000000000 : ℝ)^1699
        have hw : |(5294423657/10000000000 : ℝ)|=(5294423657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272484731/500000000 : ℝ)|^2211 ≤ (22693262576447/50000000000000 : ℝ)^1699
        have hw : |(272484731/500000000 : ℝ)|=(272484731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1821402153/10000000000 : ℝ)|^2211 ≤ (2725626804969/25000000000000 : ℝ)^1699
        have hw : |(-1821402153/10000000000 : ℝ)|=(1821402153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s2_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2146244363/5000000000 : ℝ)*x 0 + (1141009607/2500000000 : ℝ)*x 1 + (504439411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146244363/5000000000 : ℝ)^2211 ≤ (1330713883923/4000000000000 : ℝ)^1699 := by
    have hnat : (2146244363 : ℕ)^2211*4000000000000^1699 ≤ 1330713883923^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146244363 5000000000 1330713883923 4000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141009607/2500000000 : ℝ)^2211 ≤ (1801618915101/5000000000000 : ℝ)^1699 := by
    have hnat : (1141009607 : ℕ)^2211*5000000000000^1699 ≤ 1801618915101^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141009607 2500000000 1801618915101 5000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504439411/1250000000 : ℝ)^2211 ≤ (30699774587063/100000000000000 : ℝ)^1699 := by
    have hnat : (504439411 : ℕ)^2211*100000000000000^1699 ≤ 30699774587063^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504439411 1250000000 30699774587063 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146244363/5000000000 : ℝ), (1141009607/2500000000 : ℝ), (504439411/1250000000 : ℝ)] ![(1330713883923/4000000000000 : ℝ), (1801618915101/5000000000000 : ℝ), (30699774587063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146244363/5000000000 : ℝ)|^2211 ≤ (1330713883923/4000000000000 : ℝ)^1699
        have hw : |(2146244363/5000000000 : ℝ)|=(2146244363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141009607/2500000000 : ℝ)|^2211 ≤ (1801618915101/5000000000000 : ℝ)^1699
        have hw : |(1141009607/2500000000 : ℝ)|=(1141009607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504439411/1250000000 : ℝ)|^2211 ≤ (30699774587063/100000000000000 : ℝ)^1699
        have hw : |(504439411/1250000000 : ℝ)|=(504439411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2329/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10537/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15703/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2329/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2329/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2329/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2329/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2329/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2329/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7917/100000 : ℝ) ^ (4421/1024 : ℝ) ≤ (878283378448267/50000000000000000000 : ℝ) := by
    have hpowers : (7917/100000 : ℝ)^4421 ≤ (878283378448267/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7917 : ℕ)^4421*50000000000000000000^1024 ≤ 878283378448267^1024*100000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7917 100000 878283378448267 50000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7917/100000 : ℝ)) (X := (878283378448267/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2329/12500 : ℝ) ^ (4421/1024 : ℝ) ≤ (35350926975083647/50000000000000000000 : ℝ) := by
    have hpowers : (2329/12500 : ℝ)^4421 ≤ (35350926975083647/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2329 : ℕ)^4421*50000000000000000000^1024 ≤ 35350926975083647^1024*12500^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2329 12500 35350926975083647 50000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2329/12500 : ℝ)) (X := (35350926975083647/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000878283378448267/25000000000000000000 : ℝ) ≤ (2500020342683579/2500000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (25000878283378448267/25000000000000000000 : ℝ)^1024 ≤ (2500020342683579/2500000000000000 : ℝ)^4421 := by
      have hnat : (25000878283378448267 : ℕ)^1024*2500000000000000^4421 ≤ 2500020342683579^4421*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000878283378448267 25000000000000000000 2500020342683579 2500000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500020342683579/2500000000000000 : ℝ)) (X := (25000878283378448267/25000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25018114605176765957/25000000000000000000 : ℝ) ≤ (10001677828019441/10000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (25018114605176765957/25000000000000000000 : ℝ)^1024 ≤ (10001677828019441/10000000000000000 : ℝ)^4421 := by
      have hnat : (25018114605176765957 : ℕ)^1024*10000000000000000^4421 ≤ 10001677828019441^4421*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018114605176765957 25000000000000000000 10001677828019441 10000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001677828019441/10000000000000000 : ℝ)) (X := (25018114605176765957/25000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25035350926975083647/25000000000000000000 : ℝ) ≤ (5001637142652283/5000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (25035350926975083647/25000000000000000000 : ℝ)^1024 ≤ (5001637142652283/5000000000000000 : ℝ)^4421 := by
      have hnat : (25035350926975083647 : ℕ)^1024*5000000000000000^4421 ≤ 5001637142652283^4421*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035350926975083647 25000000000000000000 5001637142652283 5000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001637142652283/5000000000000000 : ℝ)) (X := (25035350926975083647/25000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(878283378448267/50000000000000000000 : ℝ) ≤ ((10712559358276552669/10715000000000000000 : ℝ)+2*(12771658281/8572000000000 : ℝ)*(7917/100000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (10712559358276552669/10715000000000000000 : ℝ)+2*(12771658281/8572000000000 : ℝ)*(7917/100000 : ℝ)=(2500020342683579/2500000000000000 : ℝ) by norm_num, show 1+2*(878283378448267/50000000000000000000 : ℝ)=(25000878283378448267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35350926975083647/50000000000000000000 : ℝ)+(878283378448267/50000000000000000000 : ℝ) ≤ ((10712559358276552669/10715000000000000000 : ℝ)+(12771658281/8572000000000 : ℝ)*((2329/12500 : ℝ)+(7917/100000 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (10712559358276552669/10715000000000000000 : ℝ)+(12771658281/8572000000000 : ℝ)*((2329/12500 : ℝ)+(7917/100000 : ℝ))=(10001677828019441/10000000000000000 : ℝ) by norm_num, show 1+(35350926975083647/50000000000000000000 : ℝ)+(878283378448267/50000000000000000000 : ℝ)=(25018114605176765957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35350926975083647/50000000000000000000 : ℝ) ≤ ((10712559358276552669/10715000000000000000 : ℝ)+2*(12771658281/8572000000000 : ℝ)*(2329/12500 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (10712559358276552669/10715000000000000000 : ℝ)+2*(12771658281/8572000000000 : ℝ)*(2329/12500 : ℝ)=(5001637142652283/5000000000000000 : ℝ) by norm_num, show 1+2*(35350926975083647/50000000000000000000 : ℝ)=(25035350926975083647/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10712559358276552669/10715000000000000000 : ℝ)*(X 1 0+X 2 0)+(12771658281/8572000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (7917/100000 : ℝ)) (hi := (2329/12500 : ℝ)) (c := (10712559358276552669/10715000000000000000 : ℝ)) (alpha := (12771658281/8572000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10712559358276552669/10715000000000000000 : ℝ)*(X 0 1+X 2 1)+(12771658281/8572000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (7917/100000 : ℝ)) (hi := (2329/12500 : ℝ)) (c := (10712559358276552669/10715000000000000000 : ℝ)) (alpha := (12771658281/8572000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10712559358276552669/10715000000000000000 : ℝ)*(X 0 2+X 1 2)+(12771658281/8572000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (7917/100000 : ℝ)) (hi := (2329/12500 : ℝ)) (c := (10712559358276552669/10715000000000000000 : ℝ)) (alpha := (12771658281/8572000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-969363771/5000000000 : ℝ)*X 0 0+(5451055051/10000000000 : ℝ)*X 0 1+(1301739031/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679045623/5000000000 : ℝ)*X 1 0+(-2064143557/10000000000 : ℝ)*X 1 1+(5206952811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071617849/2000000000 : ℝ)*X 2 0+(5206954457/10000000000 : ℝ)*X 2 1+(-2064144049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2146201587/5000000000 : ℝ)*X 0 0+(4032530877/10000000000 : ℝ)*X 0 1+(4566997553/10000000000 : ℝ)*X 0 2+(2146201587/5000000000 : ℝ)*X 1 0+(4032530877/10000000000 : ℝ)*X 1 1+(4566997553/10000000000 : ℝ)*X 1 2+(2146201587/5000000000 : ℝ)*X 2 0+(4032530877/10000000000 : ℝ)*X 2 1+(4566997553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-242345969/1250000000 : ℝ)*X 0 0+(1302076509/2500000000 : ℝ)*X 0 1+(5449694097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294423693/10000000000 : ℝ)*X 1 0+(-364280497/2000000000 : ℝ)*X 1 1+(1089938869/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294423657/10000000000 : ℝ)*X 2 0+(272484731/500000000 : ℝ)*X 2 1+(-1821402153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2146244363/5000000000 : ℝ)*X 0 0+(1141009607/2500000000 : ℝ)*X 0 1+(504439411/1250000000 : ℝ)*X 0 2+(2146244363/5000000000 : ℝ)*X 1 0+(1141009607/2500000000 : ℝ)*X 1 1+(504439411/1250000000 : ℝ)*X 1 2+(2146244363/5000000000 : ℝ)*X 2 0+(1141009607/2500000000 : ℝ)*X 2 1+(504439411/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251197722265244794015568187/33484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4988893/4000000000000 : ℝ)*(base19) + (109814889/100000000000000 : ℝ)*(upper2) + (81154787/12500000000000 : ℝ)*(lower4) + (445127369/100000000000000 : ℝ)*(upper5) + (93246287716933/3125000000000 : ℝ)*(major0) + (93246287716933/3125000000000 : ℝ)*(major1) + (93246287716933/3125000000000 : ℝ)*(major2) + (819341518965667/20000000000000 : ℝ)*(sp0) + (512081752483753/12500000000000 : ℝ)*(sp1) + (819330636040129/20000000000000 : ℝ)*(sp2) + (1871045325302189/100000000000000 : ℝ)*(sp3) + (53450235987/100000000000000 : ℝ)*(sp5) + (5441462769/10000000000000 : ℝ)*(sp6) + (4621844283/50000000000000 : ℝ)*(sp7) + (374210913798151/20000000000000 : ℝ)*(f.failure) + (819341518965667/20000000000000 : ℝ)*(f.sum) + (769734589313/267875000000000000000000000 : ℝ)*base65 + (10870214480487927/33484375000000000000000000000000 : ℝ)*base67 + (35590618345670099/16742187500000000000000000000000 : ℝ)*base70 + (35881775567357599/16742187500000000000000000000000 : ℝ)*base72 + (234332258773/1071500000000000000000000000 : ℝ)*base73 + (370325869375355823/33484375000000000000000000000000 : ℝ)*base76 + (203865777214076349/16742187500000000000000000000000 : ℝ)*base78 + (106187423001737927/33484375000000000000000000000000 : ℝ)*base79 + (287081448163/214300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (389669/400000000000000000000 : ℝ)*base90 + (389669/400000000000000000000 : ℝ)*base92 + (389669/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153099315884535866288208873/33484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69399793/100000000000000 : ℝ)*(base23) + (355719/2000000000000 : ℝ)*(lower2) + (3350467/20000000000000 : ℝ)*(upper3) + (37293471/100000000000000 : ℝ)*(lower4) + (38472111/50000000000000 : ℝ)*(upper5) + (47146662366183/1562500000000 : ℝ)*(major0) + (47146662366183/1562500000000 : ℝ)*(major1) + (47146662366183/1562500000000 : ℝ)*(major2) + (1771160353/50000000000000 : ℝ)*(sp1) + (8592162811/100000000000000 : ℝ)*(sp2) + (2071354251191423/50000000000000 : ℝ)*(sp4) + (207135248003107/5000000000000 : ℝ)*(sp5) + (4142699840820241/100000000000000 : ℝ)*(sp6) + (946032064039929/50000000000000 : ℝ)*(sp7) + (946032064039929/50000000000000 : ℝ)*(f.failure) + (2071354251191423/50000000000000 : ℝ)*(f.sum) + (4552876676743/535750000000000000000000000 : ℝ)*base65 + (218790275396632573/16742187500000000000000000000000 : ℝ)*base68 + (32983689192449099/8371093750000000000000000000000 : ℝ)*base70 + (44531927764851323/16742187500000000000000000000000 : ℝ)*base72 + (4381083601183/1071500000000000000000000000 : ℝ)*base74 + (1827960277810487/4185546875000000000000000000000 : ℝ)*base76 + (28316890405851323/16742187500000000000000000000000 : ℝ)*base78 + (213146636464344229/33484375000000000000000000000000 : ℝ)*base79 + (1913863374251/535750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6682149/1000000000000000000000 : ℝ)*base89 + (6682149/1000000000000000000000 : ℝ)*base91 + (6682149/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1462_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2329/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15703/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1462_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1462_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15703/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1462_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1462_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1462_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15703/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1462_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
