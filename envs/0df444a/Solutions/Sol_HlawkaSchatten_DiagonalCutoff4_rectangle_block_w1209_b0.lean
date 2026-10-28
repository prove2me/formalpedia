-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:06:22.118761+00:00
-- url     : https://prove2.me/submissions/74c45af6-a743-490d-82af-80d6d46f6744

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
theorem support_rectangle_w1209_s0_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1870785247/10000000000 : ℝ)*x 0 + (6038973961/10000000000 : ℝ)*x 1 + (4788887073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1870785247/10000000000 : ℝ)^4201 ≤ (68118511127/625000000000 : ℝ)^3177 := by
    have hnat : (1870785247 : ℕ)^4201*625000000000^3177 ≤ 68118511127^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870785247 10000000000 68118511127 625000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6038973961/10000000000 : ℝ)^4201 ≤ (25664566895359/50000000000000 : ℝ)^3177 := by
    have hnat : (6038973961 : ℕ)^4201*50000000000000^3177 ≤ 25664566895359^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038973961 10000000000 25664566895359 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4788887073/10000000000 : ℝ)^4201 ≤ (37771904411439/100000000000000 : ℝ)^3177 := by
    have hnat : (4788887073 : ℕ)^4201*100000000000000^3177 ≤ 37771904411439^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788887073 10000000000 37771904411439 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1870785247/10000000000 : ℝ), (6038973961/10000000000 : ℝ), (4788887073/10000000000 : ℝ)] ![(68118511127/625000000000 : ℝ), (25664566895359/50000000000000 : ℝ), (37771904411439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1870785247/10000000000 : ℝ)|^4201 ≤ (68118511127/625000000000 : ℝ)^3177
        have hw : |(-1870785247/10000000000 : ℝ)|=(1870785247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6038973961/10000000000 : ℝ)|^4201 ≤ (25664566895359/50000000000000 : ℝ)^3177
        have hw : |(6038973961/10000000000 : ℝ)|=(6038973961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4788887073/10000000000 : ℝ)|^4201 ≤ (37771904411439/100000000000000 : ℝ)^3177
        have hw : |(4788887073/10000000000 : ℝ)|=(4788887073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s0_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5513018719/10000000000 : ℝ)*x 0 + (-1293165329/5000000000 : ℝ)*x 1 + (1197221763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513018719/10000000000 : ℝ)^4201 ≤ (45502471490713/100000000000000 : ℝ)^3177 := by
    have hnat : (5513018719 : ℕ)^4201*100000000000000^3177 ≤ 45502471490713^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513018719 10000000000 45502471490713 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293165329/5000000000 : ℝ)^4201 ≤ (418140607493/2500000000000 : ℝ)^3177 := by
    have hnat : (1293165329 : ℕ)^4201*2500000000000^3177 ≤ 418140607493^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293165329 5000000000 418140607493 2500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197221763/2500000000 : ℝ)^4201 ≤ (37771904192417/100000000000000 : ℝ)^3177 := by
    have hnat : (1197221763 : ℕ)^4201*100000000000000^3177 ≤ 37771904192417^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197221763 2500000000 37771904192417 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513018719/10000000000 : ℝ), (-1293165329/5000000000 : ℝ), (1197221763/2500000000 : ℝ)] ![(45502471490713/100000000000000 : ℝ), (418140607493/2500000000000 : ℝ), (37771904192417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513018719/10000000000 : ℝ)|^4201 ≤ (45502471490713/100000000000000 : ℝ)^3177
        have hw : |(5513018719/10000000000 : ℝ)|=(5513018719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1293165329/5000000000 : ℝ)|^4201 ≤ (418140607493/2500000000000 : ℝ)^3177
        have hw : |(-1293165329/5000000000 : ℝ)|=(1293165329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1197221763/2500000000 : ℝ)|^4201 ≤ (37771904192417/100000000000000 : ℝ)^3177
        have hw : |(1197221763/2500000000 : ℝ)|=(1197221763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s0_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1102603741/2000000000 : ℝ)*x 0 + (4788887067/10000000000 : ℝ)*x 1 + (-1293165329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102603741/2000000000 : ℝ)^4201 ≤ (22751235668959/50000000000000 : ℝ)^3177 := by
    have hnat : (1102603741 : ℕ)^4201*50000000000000^3177 ≤ 22751235668959^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102603741 2000000000 22751235668959 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4788887067/10000000000 : ℝ)^4201 ≤ (18885952174431/50000000000000 : ℝ)^3177 := by
    have hnat : (4788887067 : ℕ)^4201*50000000000000^3177 ≤ 18885952174431^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788887067 10000000000 18885952174431 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293165329/5000000000 : ℝ)^4201 ≤ (418140607493/2500000000000 : ℝ)^3177 := by
    have hnat : (1293165329 : ℕ)^4201*2500000000000^3177 ≤ 418140607493^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293165329 5000000000 418140607493 2500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102603741/2000000000 : ℝ), (4788887067/10000000000 : ℝ), (-1293165329/5000000000 : ℝ)] ![(22751235668959/50000000000000 : ℝ), (18885952174431/50000000000000 : ℝ), (418140607493/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102603741/2000000000 : ℝ)|^4201 ≤ (22751235668959/50000000000000 : ℝ)^3177
        have hw : |(1102603741/2000000000 : ℝ)|=(1102603741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4788887067/10000000000 : ℝ)|^4201 ≤ (18885952174431/50000000000000 : ℝ)^3177
        have hw : |(4788887067/10000000000 : ℝ)|=(4788887067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1293165329/5000000000 : ℝ)|^4201 ≤ (418140607493/2500000000000 : ℝ)^3177
        have hw : |(-1293165329/5000000000 : ℝ)|=(1293165329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s0_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419562571/1000000000 : ℝ)*x 0 + (3118175851/10000000000 : ℝ)*x 1 + (5637916613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419562571/1000000000 : ℝ)^4201 ≤ (31711577445579/100000000000000 : ℝ)^3177 := by
    have hnat : (419562571 : ℕ)^4201*100000000000000^3177 ≤ 31711577445579^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419562571 1000000000 31711577445579 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118175851/10000000000 : ℝ)^4201 ≤ (10708936557383/50000000000000 : ℝ)^3177 := by
    have hnat : (3118175851 : ℕ)^4201*50000000000000^3177 ≤ 10708936557383^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118175851 10000000000 10708936557383 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5637916613/10000000000 : ℝ)^4201 ≤ (46870549422581/100000000000000 : ℝ)^3177 := by
    have hnat : (5637916613 : ℕ)^4201*100000000000000^3177 ≤ 46870549422581^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637916613 10000000000 46870549422581 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419562571/1000000000 : ℝ), (3118175851/10000000000 : ℝ), (5637916613/10000000000 : ℝ)] ![(31711577445579/100000000000000 : ℝ), (10708936557383/50000000000000 : ℝ), (46870549422581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419562571/1000000000 : ℝ)|^4201 ≤ (31711577445579/100000000000000 : ℝ)^3177
        have hw : |(419562571/1000000000 : ℝ)|=(419562571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118175851/10000000000 : ℝ)|^4201 ≤ (10708936557383/50000000000000 : ℝ)^3177
        have hw : |(3118175851/10000000000 : ℝ)|=(3118175851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5637916613/10000000000 : ℝ)|^4201 ≤ (46870549422581/100000000000000 : ℝ)^3177
        have hw : |(5637916613/10000000000 : ℝ)|=(5637916613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s0_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-58616783/312500000 : ℝ)*x 0 + (2410550063/5000000000 : ℝ)*x 1 + (48044989/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58616783/312500000 : ℝ)^4201 ≤ (5468562528357/50000000000000 : ℝ)^3177 := by
    have hnat : (58616783 : ℕ)^4201*50000000000000^3177 ≤ 5468562528357^3177*312500000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58616783 312500000 5468562528357 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2410550063/5000000000 : ℝ)^4201 ≤ (38108238951627/100000000000000 : ℝ)^3177 := by
    have hnat : (2410550063 : ℕ)^4201*100000000000000^3177 ≤ 38108238951627^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410550063 5000000000 38108238951627 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48044989/80000000 : ℝ)^4201 ≤ (12738658995467/25000000000000 : ℝ)^3177 := by
    have hnat : (48044989 : ℕ)^4201*25000000000000^3177 ≤ 12738658995467^3177*80000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48044989 80000000 12738658995467 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58616783/312500000 : ℝ), (2410550063/5000000000 : ℝ), (48044989/80000000 : ℝ)] ![(5468562528357/50000000000000 : ℝ), (38108238951627/100000000000000 : ℝ), (12738658995467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58616783/312500000 : ℝ)|^4201 ≤ (5468562528357/50000000000000 : ℝ)^3177
        have hw : |(-58616783/312500000 : ℝ)|=(58616783/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2410550063/5000000000 : ℝ)|^4201 ≤ (38108238951627/100000000000000 : ℝ)^3177
        have hw : |(2410550063/5000000000 : ℝ)|=(2410550063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(48044989/80000000 : ℝ)|^4201 ≤ (12738658995467/25000000000000 : ℝ)^3177
        have hw : |(48044989/80000000 : ℝ)|=(48044989/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s0_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173031387/10000000000 : ℝ)*x 0 + (-1369592557/10000000000 : ℝ)*x 1 + (6005625283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173031387/10000000000 : ℝ)^4201 ≤ (41829280762643/100000000000000 : ℝ)^3177 := by
    have hnat : (5173031387 : ℕ)^4201*100000000000000^3177 ≤ 41829280762643^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173031387 10000000000 41829280762643 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369592557/10000000000 : ℝ)^4201 ≤ (7216064637431/100000000000000 : ℝ)^3177 := by
    have hnat : (1369592557 : ℕ)^4201*100000000000000^3177 ≤ 7216064637431^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369592557 10000000000 7216064637431 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6005625283/10000000000 : ℝ)^4201 ≤ (50954654583267/100000000000000 : ℝ)^3177 := by
    have hnat : (6005625283 : ℕ)^4201*100000000000000^3177 ≤ 50954654583267^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005625283 10000000000 50954654583267 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173031387/10000000000 : ℝ), (-1369592557/10000000000 : ℝ), (6005625283/10000000000 : ℝ)] ![(41829280762643/100000000000000 : ℝ), (7216064637431/100000000000000 : ℝ), (50954654583267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173031387/10000000000 : ℝ)|^4201 ≤ (41829280762643/100000000000000 : ℝ)^3177
        have hw : |(5173031387/10000000000 : ℝ)|=(5173031387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1369592557/10000000000 : ℝ)|^4201 ≤ (7216064637431/100000000000000 : ℝ)^3177
        have hw : |(-1369592557/10000000000 : ℝ)|=(1369592557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6005625283/10000000000 : ℝ)|^4201 ≤ (50954654583267/100000000000000 : ℝ)^3177
        have hw : |(6005625283/10000000000 : ℝ)|=(6005625283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s0_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034606441/2000000000 : ℝ)*x 0 + (6005624119/10000000000 : ℝ)*x 1 + (-171199147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034606441/2000000000 : ℝ)^4201 ≤ (41829289508937/100000000000000 : ℝ)^3177 := by
    have hnat : (1034606441 : ℕ)^4201*100000000000000^3177 ≤ 41829289508937^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034606441 2000000000 41829289508937 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6005624119/10000000000 : ℝ)^4201 ≤ (25477320762071/50000000000000 : ℝ)^3177 := by
    have hnat : (6005624119 : ℕ)^4201*50000000000000^3177 ≤ 25477320762071^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005624119 10000000000 25477320762071 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171199147/1250000000 : ℝ)^4201 ≤ (7216068949991/100000000000000 : ℝ)^3177 := by
    have hnat : (171199147 : ℕ)^4201*100000000000000^3177 ≤ 7216068949991^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171199147 1250000000 7216068949991 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034606441/2000000000 : ℝ), (6005624119/10000000000 : ℝ), (-171199147/1250000000 : ℝ)] ![(41829289508937/100000000000000 : ℝ), (25477320762071/50000000000000 : ℝ), (7216068949991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034606441/2000000000 : ℝ)|^4201 ≤ (41829289508937/100000000000000 : ℝ)^3177
        have hw : |(1034606441/2000000000 : ℝ)|=(1034606441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6005624119/10000000000 : ℝ)|^4201 ≤ (25477320762071/50000000000000 : ℝ)^3177
        have hw : |(6005624119/10000000000 : ℝ)|=(6005624119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171199147/1250000000 : ℝ)|^4201 ≤ (7216068949991/100000000000000 : ℝ)^3177
        have hw : |(-171199147/1250000000 : ℝ)|=(171199147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s0_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102802909/5000000000 : ℝ)*x 0 + (5572989983/10000000000 : ℝ)*x 1 + (3185394031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102802909/5000000000 : ℝ)^4201 ≤ (15905680409193/50000000000000 : ℝ)^3177 := by
    have hnat : (2102802909 : ℕ)^4201*50000000000000^3177 ≤ 15905680409193^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102802909 5000000000 15905680409193 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5572989983/10000000000 : ℝ)^4201 ≤ (72122090679/156250000000 : ℝ)^3177 := by
    have hnat : (5572989983 : ℕ)^4201*156250000000^3177 ≤ 72122090679^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572989983 10000000000 72122090679 156250000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185394031/10000000000 : ℝ)^4201 ≤ (688453160319/3125000000000 : ℝ)^3177 := by
    have hnat : (3185394031 : ℕ)^4201*3125000000000^3177 ≤ 688453160319^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185394031 10000000000 688453160319 3125000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102802909/5000000000 : ℝ), (5572989983/10000000000 : ℝ), (3185394031/10000000000 : ℝ)] ![(15905680409193/50000000000000 : ℝ), (72122090679/156250000000 : ℝ), (688453160319/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102802909/5000000000 : ℝ)|^4201 ≤ (15905680409193/50000000000000 : ℝ)^3177
        have hw : |(2102802909/5000000000 : ℝ)|=(2102802909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5572989983/10000000000 : ℝ)|^4201 ≤ (72122090679/156250000000 : ℝ)^3177
        have hw : |(5572989983/10000000000 : ℝ)|=(5572989983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185394031/10000000000 : ℝ)|^4201 ≤ (688453160319/3125000000000 : ℝ)^3177
        have hw : |(3185394031/10000000000 : ℝ)|=(3185394031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (343/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (689/2500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8401/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8401 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8401*1^2048 ≤ 0^2048*1^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8401/2048 : ℝ) ≤ (2331470241356039407/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8401 ≤ (2331470241356039407/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8401*100000000000000000000^2048 ≤ 2331470241356039407^2048*5^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2331470241356039407 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2331470241356039407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8401 := by
      have hnat : (1 : ℕ)^2048*1^8401 ≤ 1^8401*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102331470241356039407/100000000000000000000 : ℝ) ≤ (1257042798049193/1250000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (102331470241356039407/100000000000000000000 : ℝ)^2048 ≤ (1257042798049193/1250000000000000 : ℝ)^8401 := by
      have hnat : (102331470241356039407 : ℕ)^2048*1250000000000000^8401 ≤ 1257042798049193^8401*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102331470241356039407 100000000000000000000 1257042798049193 1250000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257042798049193/1250000000000000 : ℝ)) (X := (102331470241356039407/100000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52331470241356039407/50000000000000000000 : ℝ) ≤ (632042798049193/625000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (52331470241356039407/50000000000000000000 : ℝ)^2048 ≤ (632042798049193/625000000000000 : ℝ)^8401 := by
      have hnat : (52331470241356039407 : ℕ)^2048*625000000000000^8401 ≤ 632042798049193^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52331470241356039407 50000000000000000000 632042798049193 625000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632042798049193/625000000000000 : ℝ)) (X := (52331470241356039407/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7042798049193/500000000000000 : ℝ)*(0 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(7042798049193/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2331470241356039407/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7042798049193/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (1 : ℝ)+(7042798049193/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1257042798049193/1250000000000000 : ℝ) by norm_num, show 1+(2331470241356039407/100000000000000000000 : ℝ)+(0 : ℝ)=(102331470241356039407/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2331470241356039407/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7042798049193/500000000000000 : ℝ)*(2/5 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(7042798049193/500000000000000 : ℝ)*(2/5 : ℝ)=(632042798049193/625000000000000 : ℝ) by norm_num, show 1+2*(2331470241356039407/100000000000000000000 : ℝ)=(52331470241356039407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7042798049193/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7042798049193/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7042798049193/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7042798049193/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7042798049193/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7042798049193/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1870785247/10000000000 : ℝ)*X 0 0+(6038973961/10000000000 : ℝ)*X 0 1+(4788887073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513018719/10000000000 : ℝ)*X 1 0+(-1293165329/5000000000 : ℝ)*X 1 1+(1197221763/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1102603741/2000000000 : ℝ)*X 2 0+(4788887067/10000000000 : ℝ)*X 2 1+(-1293165329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419562571/1000000000 : ℝ)*X 0 0+(3118175851/10000000000 : ℝ)*X 0 1+(5637916613/10000000000 : ℝ)*X 0 2+(419562571/1000000000 : ℝ)*X 1 0+(3118175851/10000000000 : ℝ)*X 1 1+(5637916613/10000000000 : ℝ)*X 1 2+(419562571/1000000000 : ℝ)*X 2 0+(3118175851/10000000000 : ℝ)*X 2 1+(5637916613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-58616783/312500000 : ℝ)*X 0 0+(2410550063/5000000000 : ℝ)*X 0 1+(48044989/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173031387/10000000000 : ℝ)*X 1 0+(-1369592557/10000000000 : ℝ)*X 1 1+(6005625283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034606441/2000000000 : ℝ)*X 2 0+(6005624119/10000000000 : ℝ)*X 2 1+(-171199147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102802909/5000000000 : ℝ)*X 0 0+(5572989983/10000000000 : ℝ)*X 0 1+(3185394031/10000000000 : ℝ)*X 0 2+(2102802909/5000000000 : ℝ)*X 1 0+(5572989983/10000000000 : ℝ)*X 1 1+(3185394031/10000000000 : ℝ)*X 1 2+(2102802909/5000000000 : ℝ)*X 2 0+(5572989983/10000000000 : ℝ)*X 2 1+(3185394031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2127597091239330864921/390625000000000000000000000 : ℝ) := by norm_num
    linear_combination (59937629/100000000000000 : ℝ)*(base1) + (666629817/50000000000000 : ℝ)*(base19) + (123990073/10000000000000 : ℝ)*(base23) + (3653099/4000000000000 : ℝ)*(base24) + (305065031/100000000000000 : ℝ)*(upper3) + (74801372363543/12500000000000 : ℝ)*(major0) + (74801372363543/12500000000000 : ℝ)*(major1) + (74801372363543/12500000000000 : ℝ)*(major2) + (799948904783251/100000000000000 : ℝ)*(sp0) + (799950464799403/100000000000000 : ℝ)*(sp1) + (49996904176927/6250000000000 : ℝ)*(sp2) + (198433793287759/50000000000000 : ℝ)*(sp3) + (1476606707/50000000000000 : ℝ)*(sp4) + (2331689543/100000000000000 : ℝ)*(sp7) + (39686997820269/10000000000000 : ℝ)*(f.failure) + (799951798059037/100000000000000 : ℝ)*(f.sum) + (1523931615087/1562500000000000000000000000 : ℝ)*base65 + (56708487758299/6250000000000000000000000000 : ℝ)*base67 + (54232003520799/6250000000000000000000000000 : ℝ)*base69 + (36655533077049/6250000000000000000000000000 : ℝ)*base71 + (2378768115087/1562500000000000000000000000 : ℝ)*base73 + (20245066752049/6250000000000000000000000000 : ℝ)*base75 + (39357484308299/6250000000000000000000000000 : ℝ)*base77 + (54437035452049/6250000000000000000000000000 : ℝ)*base79 + (4778380543481/781250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6333337/1000000000000000000000 : ℝ)*base90 + (6333337/1000000000000000000000 : ℝ)*base92 + (6333337/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19112493167194811787729/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209875017/25000000000000 : ℝ)*(base19) + (108790269/10000000000000 : ℝ)*(base23) + (27171711/25000000000000 : ℝ)*(base39) + (218477781/100000000000000 : ℝ)*(upper3) + (33301093/100000000000000 : ℝ)*(upper5) + (157881433214357/25000000000000 : ℝ)*(major0) + (157881433214357/25000000000000 : ℝ)*(major1) + (78940703021323/12500000000000 : ℝ)*(major2) + (2110738099/100000000000000 : ℝ)*(sp1) + (450086619/20000000000000 : ℝ)*(sp2) + (211054840212269/25000000000000 : ℝ)*(sp4) + (844216410610909/100000000000000 : ℝ)*(sp5) + (168843226240027/20000000000000 : ℝ)*(sp6) + (418831894245633/100000000000000 : ℝ)*(sp7) + (418831894245633/100000000000000 : ℝ)*(f.failure) + (10552743369199/1250000000000 : ℝ)*(f.sum) + (21199307023579/12500000000000000000000000000 : ℝ)*base65 + (36203745598589/6250000000000000000000000000 : ℝ)*base67 + (25242964173599/12500000000000000000000000000 : ℝ)*base70 + (12204427204839/6250000000000000000000000000 : ℝ)*base71 + (53456578948579/12500000000000000000000000000 : ℝ)*base73 + (22942212138901/12500000000000000000000000000 : ℝ)*base75 + (48303969313901/12500000000000000000000000000 : ℝ)*base77 + (30684591501401/12500000000000000000000000000 : ℝ)*base79 + (4376321092349/6250000000000000000000000000 : ℝ)*base82 + (72982109/10000000000000000000000 : ℝ)*base90 + (72982109/10000000000000000000000 : ℝ)*base92 + (72982109/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1209_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (343/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (689/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1209_s1_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070597839/10000000000 : ℝ)*x 0 + (28419839/50000000 : ℝ)*x 1 + (5015989199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070597839/10000000000 : ℝ)^4201 ≤ (12464131752403/100000000000000 : ℝ)^3177 := by
    have hnat : (2070597839 : ℕ)^4201*100000000000000^3177 ≤ 12464131752403^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070597839 10000000000 12464131752403 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28419839/50000000 : ℝ)^4201 ≤ (47377456032377/100000000000000 : ℝ)^3177 := by
    have hnat : (28419839 : ℕ)^4201*100000000000000^3177 ≤ 47377456032377^3177*50000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28419839 50000000 47377456032377 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015989199/10000000000 : ℝ)^4201 ≤ (10039603049103/25000000000000 : ℝ)^3177 := by
    have hnat : (5015989199 : ℕ)^4201*25000000000000^3177 ≤ 10039603049103^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015989199 10000000000 10039603049103 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070597839/10000000000 : ℝ), (28419839/50000000 : ℝ), (5015989199/10000000000 : ℝ)] ![(12464131752403/100000000000000 : ℝ), (47377456032377/100000000000000 : ℝ), (10039603049103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070597839/10000000000 : ℝ)|^4201 ≤ (12464131752403/100000000000000 : ℝ)^3177
        have hw : |(-2070597839/10000000000 : ℝ)|=(2070597839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28419839/50000000 : ℝ)|^4201 ≤ (47377456032377/100000000000000 : ℝ)^3177
        have hw : |(28419839/50000000 : ℝ)|=(28419839/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015989199/10000000000 : ℝ)|^4201 ≤ (10039603049103/25000000000000 : ℝ)^3177
        have hw : |(5015989199/10000000000 : ℝ)|=(5015989199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s1_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541545339/1000000000 : ℝ)*x 0 + (-2429867431/10000000000 : ℝ)*x 1 + (5015989681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541545339/1000000000 : ℝ)^4201 ≤ (22220349960817/50000000000000 : ℝ)^3177 := by
    have hnat : (541545339 : ℕ)^4201*50000000000000^3177 ≤ 22220349960817^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541545339 1000000000 22220349960817 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2429867431/10000000000 : ℝ)^4201 ≤ (7700441381197/50000000000000 : ℝ)^3177 := by
    have hnat : (2429867431 : ℕ)^4201*50000000000000^3177 ≤ 7700441381197^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429867431 10000000000 7700441381197 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015989681/10000000000 : ℝ)^4201 ≤ (2007920864957/5000000000000 : ℝ)^3177 := by
    have hnat : (5015989681 : ℕ)^4201*5000000000000^3177 ≤ 2007920864957^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015989681 10000000000 2007920864957 5000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541545339/1000000000 : ℝ), (-2429867431/10000000000 : ℝ), (5015989681/10000000000 : ℝ)] ![(22220349960817/50000000000000 : ℝ), (7700441381197/50000000000000 : ℝ), (2007920864957/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541545339/1000000000 : ℝ)|^4201 ≤ (22220349960817/50000000000000 : ℝ)^3177
        have hw : |(541545339/1000000000 : ℝ)|=(541545339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2429867431/10000000000 : ℝ)|^4201 ≤ (7700441381197/50000000000000 : ℝ)^3177
        have hw : |(-2429867431/10000000000 : ℝ)|=(2429867431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015989681/10000000000 : ℝ)|^4201 ≤ (2007920864957/5000000000000 : ℝ)^3177
        have hw : |(5015989681/10000000000 : ℝ)|=(5015989681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s1_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (338465757/625000000 : ℝ)*x 0 + (5015990497/10000000000 : ℝ)*x 1 + (-485973611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338465757/625000000 : ℝ)^4201 ≤ (44440686053681/100000000000000 : ℝ)^3177 := by
    have hnat : (338465757 : ℕ)^4201*100000000000000^3177 ≤ 44440686053681^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338465757 625000000 44440686053681 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5015990497/10000000000 : ℝ)^4201 ≤ (5019803242223/12500000000000 : ℝ)^3177 := by
    have hnat : (5015990497 : ℕ)^4201*12500000000000^3177 ≤ 5019803242223^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015990497 10000000000 5019803242223 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485973611/2000000000 : ℝ)^4201 ≤ (1540088799217/10000000000000 : ℝ)^3177 := by
    have hnat : (485973611 : ℕ)^4201*10000000000000^3177 ≤ 1540088799217^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485973611 2000000000 1540088799217 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338465757/625000000 : ℝ), (5015990497/10000000000 : ℝ), (-485973611/2000000000 : ℝ)] ![(44440686053681/100000000000000 : ℝ), (5019803242223/12500000000000 : ℝ), (1540088799217/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338465757/625000000 : ℝ)|^4201 ≤ (44440686053681/100000000000000 : ℝ)^3177
        have hw : |(338465757/625000000 : ℝ)|=(338465757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5015990497/10000000000 : ℝ)|^4201 ≤ (5019803242223/12500000000000 : ℝ)^3177
        have hw : |(5015990497/10000000000 : ℝ)|=(5015990497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485973611/2000000000 : ℝ)|^4201 ≤ (1540088799217/10000000000000 : ℝ)^3177
        have hw : |(-485973611/2000000000 : ℝ)|=(485973611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s1_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172468457/400000000 : ℝ)*x 0 + (3689464031/10000000000 : ℝ)*x 1 + (5035877763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172468457/400000000 : ℝ)^4201 ≤ (32876925473929/100000000000000 : ℝ)^3177 := by
    have hnat : (172468457 : ℕ)^4201*100000000000000^3177 ≤ 32876925473929^3177*400000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172468457 400000000 32876925473929 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3689464031/10000000000 : ℝ)^4201 ≤ (2675397615297/10000000000000 : ℝ)^3177 := by
    have hnat : (3689464031 : ℕ)^4201*10000000000000^3177 ≤ 2675397615297^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689464031 10000000000 2675397615297 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5035877763/10000000000 : ℝ)^4201 ≤ (10092274589519/25000000000000 : ℝ)^3177 := by
    have hnat : (5035877763 : ℕ)^4201*25000000000000^3177 ≤ 10092274589519^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035877763 10000000000 10092274589519 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172468457/400000000 : ℝ), (3689464031/10000000000 : ℝ), (5035877763/10000000000 : ℝ)] ![(32876925473929/100000000000000 : ℝ), (2675397615297/10000000000000 : ℝ), (10092274589519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172468457/400000000 : ℝ)|^4201 ≤ (32876925473929/100000000000000 : ℝ)^3177
        have hw : |(172468457/400000000 : ℝ)|=(172468457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3689464031/10000000000 : ℝ)|^4201 ≤ (2675397615297/10000000000000 : ℝ)^3177
        have hw : |(3689464031/10000000000 : ℝ)|=(3689464031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5035877763/10000000000 : ℝ)|^4201 ≤ (10092274589519/25000000000000 : ℝ)^3177
        have hw : |(5035877763/10000000000 : ℝ)|=(5035877763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s1_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071312181/10000000000 : ℝ)*x 0 + (2512438243/5000000000 : ℝ)*x 1 + (5674910837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071312181/10000000000 : ℝ)^4201 ≤ (623490904127/5000000000000 : ℝ)^3177 := by
    have hnat : (2071312181 : ℕ)^4201*5000000000000^3177 ≤ 623490904127^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071312181 10000000000 623490904127 5000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512438243/5000000000 : ℝ)^4201 ≤ (40252524965761/100000000000000 : ℝ)^3177 := by
    have hnat : (2512438243 : ℕ)^4201*100000000000000^3177 ≤ 40252524965761^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512438243 5000000000 40252524965761 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5674910837/10000000000 : ℝ)^4201 ≤ (11819414233937/25000000000000 : ℝ)^3177 := by
    have hnat : (5674910837 : ℕ)^4201*25000000000000^3177 ≤ 11819414233937^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674910837 10000000000 11819414233937 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071312181/10000000000 : ℝ), (2512438243/5000000000 : ℝ), (5674910837/10000000000 : ℝ)] ![(623490904127/5000000000000 : ℝ), (40252524965761/100000000000000 : ℝ), (11819414233937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071312181/10000000000 : ℝ)|^4201 ≤ (623490904127/5000000000000 : ℝ)^3177
        have hw : |(-2071312181/10000000000 : ℝ)|=(2071312181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512438243/5000000000 : ℝ)|^4201 ≤ (40252524965761/100000000000000 : ℝ)^3177
        have hw : |(2512438243/5000000000 : ℝ)|=(2512438243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5674910837/10000000000 : ℝ)|^4201 ≤ (11819414233937/25000000000000 : ℝ)^3177
        have hw : |(5674910837/10000000000 : ℝ)|=(5674910837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s1_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5243632189/10000000000 : ℝ)*x 0 + (-1770949271/10000000000 : ℝ)*x 1 + (2837453897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243632189/10000000000 : ℝ)^4201 ≤ (42585820301103/100000000000000 : ℝ)^3177 := by
    have hnat : (5243632189 : ℕ)^4201*100000000000000^3177 ≤ 42585820301103^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243632189 10000000000 42585820301103 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1770949271/10000000000 : ℝ)^4201 ≤ (10136556272597/100000000000000 : ℝ)^3177 := by
    have hnat : (1770949271 : ℕ)^4201*100000000000000^3177 ≤ 10136556272597^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770949271 10000000000 10136556272597 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2837453897/5000000000 : ℝ)^4201 ≤ (47277623413411/100000000000000 : ℝ)^3177 := by
    have hnat : (2837453897 : ℕ)^4201*100000000000000^3177 ≤ 47277623413411^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837453897 5000000000 47277623413411 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243632189/10000000000 : ℝ), (-1770949271/10000000000 : ℝ), (2837453897/5000000000 : ℝ)] ![(42585820301103/100000000000000 : ℝ), (10136556272597/100000000000000 : ℝ), (47277623413411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243632189/10000000000 : ℝ)|^4201 ≤ (42585820301103/100000000000000 : ℝ)^3177
        have hw : |(5243632189/10000000000 : ℝ)|=(5243632189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1770949271/10000000000 : ℝ)|^4201 ≤ (10136556272597/100000000000000 : ℝ)^3177
        have hw : |(-1770949271/10000000000 : ℝ)|=(1770949271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2837453897/5000000000 : ℝ)|^4201 ≤ (47277623413411/100000000000000 : ℝ)^3177
        have hw : |(2837453897/5000000000 : ℝ)|=(2837453897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s1_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (327727021/625000000 : ℝ)*x 0 + (2837454123/5000000000 : ℝ)*x 1 + (-442737101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327727021/625000000 : ℝ)^4201 ≤ (5323227734969/12500000000000 : ℝ)^3177 := by
    have hnat : (327727021 : ℕ)^4201*12500000000000^3177 ≤ 5323227734969^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327727021 625000000 5323227734969 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2837454123/5000000000 : ℝ)^4201 ≤ (47277628392739/100000000000000 : ℝ)^3177 := by
    have hnat : (2837454123 : ℕ)^4201*100000000000000^3177 ≤ 47277628392739^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837454123 5000000000 47277628392739 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442737101/2500000000 : ℝ)^4201 ≤ (10136549710557/100000000000000 : ℝ)^3177 := by
    have hnat : (442737101 : ℕ)^4201*100000000000000^3177 ≤ 10136549710557^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442737101 2500000000 10136549710557 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327727021/625000000 : ℝ), (2837454123/5000000000 : ℝ), (-442737101/2500000000 : ℝ)] ![(5323227734969/12500000000000 : ℝ), (47277628392739/100000000000000 : ℝ), (10136549710557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327727021/625000000 : ℝ)|^4201 ≤ (5323227734969/12500000000000 : ℝ)^3177
        have hw : |(327727021/625000000 : ℝ)|=(327727021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2837454123/5000000000 : ℝ)|^4201 ≤ (47277628392739/100000000000000 : ℝ)^3177
        have hw : |(2837454123/5000000000 : ℝ)|=(2837454123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442737101/2500000000 : ℝ)|^4201 ≤ (10136549710557/100000000000000 : ℝ)^3177
        have hw : |(-442737101/2500000000 : ℝ)|=(442737101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s1_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156577669/5000000000 : ℝ)*x 0 + (2508980721/5000000000 : ℝ)*x 1 + (3707725773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156577669/5000000000 : ℝ)^4201 ≤ (6578296961121/20000000000000 : ℝ)^3177 := by
    have hnat : (2156577669 : ℕ)^4201*20000000000000^3177 ≤ 6578296961121^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156577669 5000000000 6578296961121 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508980721/5000000000 : ℝ)^4201 ≤ (40179292814337/100000000000000 : ℝ)^3177 := by
    have hnat : (2508980721 : ℕ)^4201*100000000000000^3177 ≤ 40179292814337^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508980721 5000000000 40179292814337 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3707725773/10000000000 : ℝ)^4201 ≤ (26929222361403/100000000000000 : ℝ)^3177 := by
    have hnat : (3707725773 : ℕ)^4201*100000000000000^3177 ≤ 26929222361403^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707725773 10000000000 26929222361403 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156577669/5000000000 : ℝ), (2508980721/5000000000 : ℝ), (3707725773/10000000000 : ℝ)] ![(6578296961121/20000000000000 : ℝ), (40179292814337/100000000000000 : ℝ), (26929222361403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156577669/5000000000 : ℝ)|^4201 ≤ (6578296961121/20000000000000 : ℝ)^3177
        have hw : |(2156577669/5000000000 : ℝ)|=(2156577669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2508980721/5000000000 : ℝ)|^4201 ≤ (40179292814337/100000000000000 : ℝ)^3177
        have hw : |(2508980721/5000000000 : ℝ)|=(2508980721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3707725773/10000000000 : ℝ)|^4201 ≤ (26929222361403/100000000000000 : ℝ)^3177
        have hw : |(3707725773/10000000000 : ℝ)|=(3707725773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (689/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (188/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1007/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (689/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (343/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (689/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (343/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (689/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (343/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (689/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (343/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (689/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (343/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (689/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (343/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (343/50000 : ℝ) ^ (8401/2048 : ℝ) ≤ (133196142829/100000000000000000000 : ℝ) := by
    have hpowers : (343/50000 : ℝ)^8401 ≤ (133196142829/100000000000000000000 : ℝ)^2048 := by
      have hnat : (343 : ℕ)^8401*100000000000000000000^2048 ≤ 133196142829^2048*50000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        343 50000 133196142829 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (343/50000 : ℝ)) (X := (133196142829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (689/2500 : ℝ) ^ (8401/2048 : ℝ) ≤ (126455265586791103/25000000000000000000 : ℝ) := by
    have hpowers : (689/2500 : ℝ)^8401 ≤ (126455265586791103/25000000000000000000 : ℝ)^2048 := by
      have hnat : (689 : ℕ)^8401*25000000000000000000^2048 ≤ 126455265586791103^2048*2500^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        689 2500 126455265586791103 25000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (689/2500 : ℝ)) (X := (126455265586791103/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000133196142829/50000000000000000000 : ℝ) ≤ (80000000051953/80000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50000000133196142829/50000000000000000000 : ℝ)^2048 ≤ (80000000051953/80000000000000 : ℝ)^8401 := by
      have hnat : (50000000133196142829 : ℕ)^2048*80000000000000^8401 ≤ 80000000051953^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000133196142829 50000000000000000000 80000000051953 80000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80000000051953/80000000000000 : ℝ)) (X := (50000000133196142829/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100505821195543307241/100000000000000000000 : ℝ) ≤ (5006153710230911/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (100505821195543307241/100000000000000000000 : ℝ)^2048 ≤ (5006153710230911/5000000000000000 : ℝ)^8401 := by
      have hnat : (100505821195543307241 : ℕ)^2048*5000000000000000^8401 ≤ 5006153710230911^8401*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100505821195543307241 100000000000000000000 5006153710230911 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006153710230911/5000000000000000 : ℝ)) (X := (100505821195543307241/100000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12626455265586791103/12500000000000000000 : ℝ) ≤ (10024614834429519/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (12626455265586791103/12500000000000000000 : ℝ)^2048 ≤ (10024614834429519/10000000000000000 : ℝ)^8401 := by
      have hnat : (12626455265586791103 : ℕ)^2048*10000000000000000^8401 ≤ 10024614834429519^8401*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12626455265586791103 12500000000000000000 10024614834429519 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024614834429519/10000000000000000 : ℝ)) (X := (12626455265586791103/12500000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(133196142829/100000000000000000000 : ℝ) ≤ ((134361557201279717483/134370000000000000000 : ℝ)+2*(12307413967697/2687400000000000 : ℝ)*(343/50000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (134361557201279717483/134370000000000000000 : ℝ)+2*(12307413967697/2687400000000000 : ℝ)*(343/50000 : ℝ)=(80000000051953/80000000000000 : ℝ) by norm_num, show 1+2*(133196142829/100000000000000000000 : ℝ)=(50000000133196142829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(126455265586791103/25000000000000000000 : ℝ)+(133196142829/100000000000000000000 : ℝ) ≤ ((134361557201279717483/134370000000000000000 : ℝ)+(12307413967697/2687400000000000 : ℝ)*((689/2500 : ℝ)+(343/50000 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (134361557201279717483/134370000000000000000 : ℝ)+(12307413967697/2687400000000000 : ℝ)*((689/2500 : ℝ)+(343/50000 : ℝ))=(5006153710230911/5000000000000000 : ℝ) by norm_num, show 1+(126455265586791103/25000000000000000000 : ℝ)+(133196142829/100000000000000000000 : ℝ)=(100505821195543307241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(126455265586791103/25000000000000000000 : ℝ) ≤ ((134361557201279717483/134370000000000000000 : ℝ)+2*(12307413967697/2687400000000000 : ℝ)*(689/2500 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (134361557201279717483/134370000000000000000 : ℝ)+2*(12307413967697/2687400000000000 : ℝ)*(689/2500 : ℝ)=(10024614834429519/10000000000000000 : ℝ) by norm_num, show 1+2*(126455265586791103/25000000000000000000 : ℝ)=(12626455265586791103/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (134361557201279717483/134370000000000000000 : ℝ)*(X 1 0+X 2 0)+(12307413967697/2687400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (343/50000 : ℝ)) (hi := (689/2500 : ℝ)) (c := (134361557201279717483/134370000000000000000 : ℝ)) (alpha := (12307413967697/2687400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (134361557201279717483/134370000000000000000 : ℝ)*(X 0 1+X 2 1)+(12307413967697/2687400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (343/50000 : ℝ)) (hi := (689/2500 : ℝ)) (c := (134361557201279717483/134370000000000000000 : ℝ)) (alpha := (12307413967697/2687400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (134361557201279717483/134370000000000000000 : ℝ)*(X 0 2+X 1 2)+(12307413967697/2687400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (343/50000 : ℝ)) (hi := (689/2500 : ℝ)) (c := (134361557201279717483/134370000000000000000 : ℝ)) (alpha := (12307413967697/2687400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2070597839/10000000000 : ℝ)*X 0 0+(28419839/50000000 : ℝ)*X 0 1+(5015989199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541545339/1000000000 : ℝ)*X 1 0+(-2429867431/10000000000 : ℝ)*X 1 1+(5015989681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338465757/625000000 : ℝ)*X 2 0+(5015990497/10000000000 : ℝ)*X 2 1+(-485973611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172468457/400000000 : ℝ)*X 0 0+(3689464031/10000000000 : ℝ)*X 0 1+(5035877763/10000000000 : ℝ)*X 0 2+(172468457/400000000 : ℝ)*X 1 0+(3689464031/10000000000 : ℝ)*X 1 1+(5035877763/10000000000 : ℝ)*X 1 2+(172468457/400000000 : ℝ)*X 2 0+(3689464031/10000000000 : ℝ)*X 2 1+(5035877763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2071312181/10000000000 : ℝ)*X 0 0+(2512438243/5000000000 : ℝ)*X 0 1+(5674910837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243632189/10000000000 : ℝ)*X 1 0+(-1770949271/10000000000 : ℝ)*X 1 1+(2837453897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327727021/625000000 : ℝ)*X 2 0+(2837454123/5000000000 : ℝ)*X 2 1+(-442737101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2156577669/5000000000 : ℝ)*X 0 0+(2508980721/5000000000 : ℝ)*X 0 1+(3707725773/10000000000 : ℝ)*X 0 2+(2156577669/5000000000 : ℝ)*X 1 0+(2508980721/5000000000 : ℝ)*X 1 1+(3707725773/10000000000 : ℝ)*X 1 2+(2156577669/5000000000 : ℝ)*X 2 0+(2508980721/5000000000 : ℝ)*X 2 1+(3707725773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18236585614511447502258722531/2239500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20301671/1000000000000 : ℝ)*(base19) + (794475571/50000000000000 : ℝ)*(base23) + (84631127/20000000000000 : ℝ)*(upper3) + (47612059/100000000000000 : ℝ)*(upper4) + (114791/390625000000 : ℝ)*(upper5) + (1119902439122057/100000000000000 : ℝ)*(major0) + (1119902439122057/100000000000000 : ℝ)*(major1) + (1119902439122057/100000000000000 : ℝ)*(major2) + (299413627341141/20000000000000 : ℝ)*(sp0) + (1497076135666081/100000000000000 : ℝ)*(sp1) + (37426914422051/2500000000000 : ℝ)*(sp2) + (742719285092591/100000000000000 : ℝ)*(sp3) + (2507281869/25000000000000 : ℝ)*(sp4) + (7155879987/100000000000000 : ℝ)*(sp7) + (371363220486289/50000000000000 : ℝ)*(f.failure) + (1497078165833181/100000000000000 : ℝ)*(f.sum) + (352489952804629/134370000000000000000000000000 : ℝ)*base65 + (5459311579014424177/4479000000000000000000000000000000 : ℝ)*base67 + (13471238714705575823/4479000000000000000000000000000000 : ℝ)*base70 + (17804987731674424177/4479000000000000000000000000000000 : ℝ)*base71 + (186311110418951/134370000000000000000000000000 : ℝ)*base74 + (1956502136171575823/4479000000000000000000000000000000 : ℝ)*base76 + (7427028291635575823/4479000000000000000000000000000000 : ℝ)*base78 + (30304363712561575823/4479000000000000000000000000000000 : ℝ)*base80 + (532620092336351/134370000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (22901203/5000000000000000000000 : ℝ)*base89 + (22901203/5000000000000000000000 : ℝ)*base91 + (22901203/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4495735534603555516563302921/746500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (328732441/50000000000000 : ℝ)*(base19) + (1308723217/100000000000000 : ℝ)*(base23) + (22591253/100000000000000 : ℝ)*(lower3) + (30475899/12500000000000 : ℝ)*(lower4) + (1150804678918161/100000000000000 : ℝ)*(major0) + (1150804678918161/100000000000000 : ℝ)*(major1) + (1150804678918161/100000000000000 : ℝ)*(major2) + (1053122981/25000000000000 : ℝ)*(sp0) + (1766373803/100000000000000 : ℝ)*(sp1) + (613575969/10000000000000 : ℝ)*(sp2) + (1538383941080461/100000000000000 : ℝ)*(sp4) + (15383857297337/1000000000000 : ℝ)*(sp5) + (769190354544739/50000000000000 : ℝ)*(sp6) + (381610501758323/50000000000000 : ℝ)*(sp7) + (381610501758323/50000000000000 : ℝ)*(f.failure) + (307677630714477/20000000000000 : ℝ)*(f.sum) + (127486768507649/44790000000000000000000000000 : ℝ)*base65 + (4409006399951915693/1493000000000000000000000000000000 : ℝ)*base68 + (102016489739084307/1493000000000000000000000000000000 : ℝ)*base69 + (4593160959328084307/1493000000000000000000000000000000 : ℝ)*base71 + (27294575018071/44790000000000000000000000000 : ℝ)*base74 + (1442641175890915693/1493000000000000000000000000000000 : ℝ)*base76 + (2441130066745915693/1493000000000000000000000000000000 : ℝ)*base78 + (6022512808047915693/1493000000000000000000000000000000 : ℝ)*base80 + (122707110033899/44790000000000000000000000000 : ℝ)*base81 + (11054521/5000000000000000000000 : ℝ)*base89 + (11054521/5000000000000000000000 : ℝ)*base91 + (11054521/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1209_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (689/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (188/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1007/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1209_s2_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10601559/50000000 : ℝ)*x 0 + (5498517151/10000000000 : ℝ)*x 1 + (5169765351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10601559/50000000 : ℝ)^4201 ≤ (12861367481903/100000000000000 : ℝ)^3177 := by
    have hnat : (10601559 : ℕ)^4201*100000000000000^3177 ≤ 12861367481903^3177*50000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10601559 50000000 12861367481903 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498517151/10000000000 : ℝ)^4201 ≤ (22672134795013/50000000000000 : ℝ)^3177 := by
    have hnat : (5498517151 : ℕ)^4201*50000000000000^3177 ≤ 22672134795013^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498517151 10000000000 22672134795013 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169765351/10000000000 : ℝ)^4201 ≤ (41794362910601/100000000000000 : ℝ)^3177 := by
    have hnat : (5169765351 : ℕ)^4201*100000000000000^3177 ≤ 41794362910601^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169765351 10000000000 41794362910601 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10601559/50000000 : ℝ), (5498517151/10000000000 : ℝ), (5169765351/10000000000 : ℝ)] ![(12861367481903/100000000000000 : ℝ), (22672134795013/50000000000000 : ℝ), (41794362910601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10601559/50000000 : ℝ)|^4201 ≤ (12861367481903/100000000000000 : ℝ)^3177
        have hw : |(-10601559/50000000 : ℝ)|=(10601559/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498517151/10000000000 : ℝ)|^4201 ≤ (22672134795013/50000000000000 : ℝ)^3177
        have hw : |(5498517151/10000000000 : ℝ)|=(5498517151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169765351/10000000000 : ℝ)|^4201 ≤ (41794362910601/100000000000000 : ℝ)^3177
        have hw : |(5169765351/10000000000 : ℝ)|=(5169765351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s2_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371036551/10000000000 : ℝ)*x 0 + (-458159609/2000000000 : ℝ)*x 1 + (5169770119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371036551/10000000000 : ℝ)^4201 ≤ (43959358003699/100000000000000 : ℝ)^3177 := by
    have hnat : (5371036551 : ℕ)^4201*100000000000000^3177 ≤ 43959358003699^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371036551 10000000000 43959358003699 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458159609/2000000000 : ℝ)^4201 ≤ (178077851331/1250000000000 : ℝ)^3177 := by
    have hnat : (458159609 : ℕ)^4201*1250000000000^3177 ≤ 178077851331^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458159609 2000000000 178077851331 1250000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169770119/10000000000 : ℝ)^4201 ≤ (41794413881073/100000000000000 : ℝ)^3177 := by
    have hnat : (5169770119 : ℕ)^4201*100000000000000^3177 ≤ 41794413881073^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169770119 10000000000 41794413881073 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371036551/10000000000 : ℝ), (-458159609/2000000000 : ℝ), (5169770119/10000000000 : ℝ)] ![(43959358003699/100000000000000 : ℝ), (178077851331/1250000000000 : ℝ), (41794413881073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371036551/10000000000 : ℝ)|^4201 ≤ (43959358003699/100000000000000 : ℝ)^3177
        have hw : |(5371036551/10000000000 : ℝ)|=(5371036551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458159609/2000000000 : ℝ)|^4201 ≤ (178077851331/1250000000000 : ℝ)^3177
        have hw : |(-458159609/2000000000 : ℝ)|=(458159609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169770119/10000000000 : ℝ)|^4201 ≤ (41794413881073/100000000000000 : ℝ)^3177
        have hw : |(5169770119/10000000000 : ℝ)|=(5169770119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s2_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537103873/1000000000 : ℝ)*x 0 + (1033953421/2000000000 : ℝ)*x 1 + (-1145399547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537103873/1000000000 : ℝ)^4201 ≤ (10989845396497/25000000000000 : ℝ)^3177 := by
    have hnat : (537103873 : ℕ)^4201*25000000000000^3177 ≤ 10989845396497^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537103873 1000000000 10989845396497 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033953421/2000000000 : ℝ)^4201 ≤ (20897190830531/50000000000000 : ℝ)^3177 := by
    have hnat : (1033953421 : ℕ)^4201*50000000000000^3177 ≤ 20897190830531^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033953421 2000000000 20897190830531 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145399547/5000000000 : ℝ)^4201 ≤ (1424623673277/10000000000000 : ℝ)^3177 := by
    have hnat : (1145399547 : ℕ)^4201*10000000000000^3177 ≤ 1424623673277^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145399547 5000000000 1424623673277 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537103873/1000000000 : ℝ), (1033953421/2000000000 : ℝ), (-1145399547/5000000000 : ℝ)] ![(10989845396497/25000000000000 : ℝ), (20897190830531/50000000000000 : ℝ), (1424623673277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537103873/1000000000 : ℝ)|^4201 ≤ (10989845396497/25000000000000 : ℝ)^3177
        have hw : |(537103873/1000000000 : ℝ)|=(537103873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033953421/2000000000 : ℝ)|^4201 ≤ (20897190830531/50000000000000 : ℝ)^3177
        have hw : |(1033953421/2000000000 : ℝ)|=(1033953421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1145399547/5000000000 : ℝ)|^4201 ≤ (1424623673277/10000000000000 : ℝ)^3177
        have hw : |(-1145399547/5000000000 : ℝ)|=(1145399547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s2_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2172987887/5000000000 : ℝ)*x 0 + (4026977371/10000000000 : ℝ)*x 1 + (4689623703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172987887/5000000000 : ℝ)^4201 ≤ (8305711097423/25000000000000 : ℝ)^3177 := by
    have hnat : (2172987887 : ℕ)^4201*25000000000000^3177 ≤ 8305711097423^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172987887 5000000000 8305711097423 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026977371/10000000000 : ℝ)^4201 ≤ (3003705877577/10000000000000 : ℝ)^3177 := by
    have hnat : (4026977371 : ℕ)^4201*10000000000000^3177 ≤ 3003705877577^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026977371 10000000000 3003705877577 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4689623703/10000000000 : ℝ)^4201 ≤ (36740096822751/100000000000000 : ℝ)^3177 := by
    have hnat : (4689623703 : ℕ)^4201*100000000000000^3177 ≤ 36740096822751^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4689623703 10000000000 36740096822751 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172987887/5000000000 : ℝ), (4026977371/10000000000 : ℝ), (4689623703/10000000000 : ℝ)] ![(8305711097423/25000000000000 : ℝ), (3003705877577/10000000000000 : ℝ), (36740096822751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172987887/5000000000 : ℝ)|^4201 ≤ (8305711097423/25000000000000 : ℝ)^3177
        have hw : |(2172987887/5000000000 : ℝ)|=(2172987887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026977371/10000000000 : ℝ)|^4201 ≤ (3003705877577/10000000000000 : ℝ)^3177
        have hw : |(4026977371/10000000000 : ℝ)|=(4026977371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4689623703/10000000000 : ℝ)|^4201 ≤ (36740096822751/100000000000000 : ℝ)^3177
        have hw : |(4689623703/10000000000 : ℝ)|=(4689623703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s2_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-26504951/125000000 : ℝ)*x 0 + (5171929647/10000000000 : ℝ)*x 1 + (5496333163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26504951/125000000 : ℝ)^4201 ≤ (6431021743673/50000000000000 : ℝ)^3177 := by
    have hnat : (26504951 : ℕ)^4201*50000000000000^3177 ≤ 6431021743673^3177*125000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26504951 125000000 6431021743673 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5171929647/10000000000 : ℝ)^4201 ≤ (20908750521419/50000000000000 : ℝ)^3177 := by
    have hnat : (5171929647 : ℕ)^4201*50000000000000^3177 ≤ 20908750521419^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171929647 10000000000 20908750521419 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496333163/10000000000 : ℝ)^4201 ≤ (45320455459049/100000000000000 : ℝ)^3177 := by
    have hnat : (5496333163 : ℕ)^4201*100000000000000^3177 ≤ 45320455459049^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496333163 10000000000 45320455459049 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26504951/125000000 : ℝ), (5171929647/10000000000 : ℝ), (5496333163/10000000000 : ℝ)] ![(6431021743673/50000000000000 : ℝ), (20908750521419/50000000000000 : ℝ), (45320455459049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26504951/125000000 : ℝ)|^4201 ≤ (6431021743673/50000000000000 : ℝ)^3177
        have hw : |(-26504951/125000000 : ℝ)|=(26504951/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5171929647/10000000000 : ℝ)|^4201 ≤ (20908750521419/50000000000000 : ℝ)^3177
        have hw : |(5171929647/10000000000 : ℝ)|=(5171929647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496333163/10000000000 : ℝ)|^4201 ≤ (45320455459049/100000000000000 : ℝ)^3177
        have hw : |(5496333163/10000000000 : ℝ)|=(5496333163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s2_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643629483/5000000000 : ℝ)*x 0 + (-19642333/100000000 : ℝ)*x 1 + (549633319/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643629483/5000000000 : ℝ)^4201 ≤ (21527480023791/50000000000000 : ℝ)^3177 := by
    have hnat : (2643629483 : ℕ)^4201*50000000000000^3177 ≤ 21527480023791^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643629483 5000000000 21527480023791 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19642333/100000000 : ℝ)^4201 ≤ (2906146044509/25000000000000 : ℝ)^3177 := by
    have hnat : (19642333 : ℕ)^4201*25000000000000^3177 ≤ 2906146044509^3177*100000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19642333 100000000 2906146044509 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549633319/1000000000 : ℝ)^4201 ≤ (45320455753437/100000000000000 : ℝ)^3177 := by
    have hnat : (549633319 : ℕ)^4201*100000000000000^3177 ≤ 45320455753437^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549633319 1000000000 45320455753437 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643629483/5000000000 : ℝ), (-19642333/100000000 : ℝ), (549633319/1000000000 : ℝ)] ![(21527480023791/50000000000000 : ℝ), (2906146044509/25000000000000 : ℝ), (45320455753437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643629483/5000000000 : ℝ)|^4201 ≤ (21527480023791/50000000000000 : ℝ)^3177
        have hw : |(2643629483/5000000000 : ℝ)|=(2643629483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19642333/100000000 : ℝ)|^4201 ≤ (2906146044509/25000000000000 : ℝ)^3177
        have hw : |(-19642333/100000000 : ℝ)|=(19642333/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549633319/1000000000 : ℝ)|^4201 ≤ (45320455753437/100000000000000 : ℝ)^3177
        have hw : |(549633319/1000000000 : ℝ)|=(549633319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s2_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643629573/5000000000 : ℝ)*x 0 + (274816661/500000000 : ℝ)*x 1 + (-491058253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643629573/5000000000 : ℝ)^4201 ≤ (43054961985791/100000000000000 : ℝ)^3177 := by
    have hnat : (2643629573 : ℕ)^4201*100000000000000^3177 ≤ 43054961985791^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643629573 5000000000 43054961985791 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274816661/500000000 : ℝ)^4201 ≤ (9064091216107/20000000000000 : ℝ)^3177 := by
    have hnat : (274816661 : ℕ)^4201*20000000000000^3177 ≤ 9064091216107^3177*500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274816661 500000000 9064091216107 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491058253/2500000000 : ℝ)^4201 ≤ (2906145481063/25000000000000 : ℝ)^3177 := by
    have hnat : (491058253 : ℕ)^4201*25000000000000^3177 ≤ 2906145481063^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491058253 2500000000 2906145481063 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643629573/5000000000 : ℝ), (274816661/500000000 : ℝ), (-491058253/2500000000 : ℝ)] ![(43054961985791/100000000000000 : ℝ), (9064091216107/20000000000000 : ℝ), (2906145481063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643629573/5000000000 : ℝ)|^4201 ≤ (43054961985791/100000000000000 : ℝ)^3177
        have hw : |(2643629573/5000000000 : ℝ)|=(2643629573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274816661/500000000 : ℝ)|^4201 ≤ (9064091216107/20000000000000 : ℝ)^3177
        have hw : |(274816661/500000000 : ℝ)|=(274816661/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491058253/2500000000 : ℝ)|^4201 ≤ (2906145481063/25000000000000 : ℝ)^3177
        have hw : |(-491058253/2500000000 : ℝ)|=(491058253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s2_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4346148127/10000000000 : ℝ)*x 0 + (46852639/100000000 : ℝ)*x 1 + (4031378483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346148127/10000000000 : ℝ)^4201 ≤ (8306146656039/25000000000000 : ℝ)^3177 := by
    have hnat : (4346148127 : ℕ)^4201*25000000000000^3177 ≤ 8306146656039^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346148127 10000000000 8306146656039 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46852639/100000000 : ℝ)^4201 ≤ (57335841123/156250000000 : ℝ)^3177 := by
    have hnat : (46852639 : ℕ)^4201*156250000000^3177 ≤ 57335841123^3177*100000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46852639 100000000 57335841123 156250000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031378483/10000000000 : ℝ)^4201 ≤ (15040237525901/50000000000000 : ℝ)^3177 := by
    have hnat : (4031378483 : ℕ)^4201*50000000000000^3177 ≤ 15040237525901^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031378483 10000000000 15040237525901 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346148127/10000000000 : ℝ), (46852639/100000000 : ℝ), (4031378483/10000000000 : ℝ)] ![(8306146656039/25000000000000 : ℝ), (57335841123/156250000000 : ℝ), (15040237525901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346148127/10000000000 : ℝ)|^4201 ≤ (8306146656039/25000000000000 : ℝ)^3177
        have hw : |(4346148127/10000000000 : ℝ)|=(4346148127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46852639/100000000 : ℝ)|^4201 ≤ (57335841123/156250000000 : ℝ)^3177
        have hw : |(46852639/100000000 : ℝ)|=(46852639/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031378483/10000000000 : ℝ)|^4201 ≤ (15040237525901/50000000000000 : ℝ)^3177
        have hw : |(4031378483/10000000000 : ℝ)|=(4031378483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1007/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (188/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (9363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16311/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1007/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (188/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1007/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (188/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1007/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (188/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1007/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (188/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1007/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (188/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1007/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (188/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (188/3125 : ℝ) ^ (8401/2048 : ℝ) ≤ (491619074415169/50000000000000000000 : ℝ) := by
    have hpowers : (188/3125 : ℝ)^8401 ≤ (491619074415169/50000000000000000000 : ℝ)^2048 := by
      have hnat : (188 : ℕ)^8401*50000000000000000000^2048 ≤ 491619074415169^2048*3125^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        188 3125 491619074415169 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (188/3125 : ℝ)) (X := (491619074415169/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1007/5000 : ℝ) ^ (8401/2048 : ℝ) ≤ (69853246313032053/50000000000000000000 : ℝ) := by
    have hpowers : (1007/5000 : ℝ)^8401 ≤ (69853246313032053/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1007 : ℕ)^8401*50000000000000000000^2048 ≤ 69853246313032053^2048*5000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1007 5000 69853246313032053 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1007/5000 : ℝ)) (X := (69853246313032053/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000491619074415169/25000000000000000000 : ℝ) ≤ (10000047938501523/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25000491619074415169/25000000000000000000 : ℝ)^2048 ≤ (10000047938501523/10000000000000000 : ℝ)^8401 := by
      have hnat : (25000491619074415169 : ℕ)^2048*10000000000000000^8401 ≤ 10000047938501523^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000491619074415169 25000000000000000000 10000047938501523 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000047938501523/10000000000000000 : ℝ)) (X := (25000491619074415169/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25035172432693723611/25000000000000000000 : ℝ) ≤ (10003427918334541/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25035172432693723611/25000000000000000000 : ℝ)^2048 ≤ (10003427918334541/10000000000000000 : ℝ)^8401 := by
      have hnat : (25035172432693723611 : ℕ)^2048*10000000000000000^8401 ≤ 10003427918334541^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035172432693723611 25000000000000000000 10003427918334541 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003427918334541/10000000000000000 : ℝ)) (X := (25035172432693723611/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25069853246313032053/25000000000000000000 : ℝ) ≤ (10006807898167559/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25069853246313032053/25000000000000000000 : ℝ)^2048 ≤ (10006807898167559/10000000000000000 : ℝ)^8401 := by
      have hnat : (25069853246313032053 : ℕ)^2048*10000000000000000^8401 ≤ 10006807898167559^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25069853246313032053 25000000000000000000 10006807898167559 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006807898167559/10000000000000000 : ℝ)) (X := (25069853246313032053/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(491619074415169/50000000000000000000 : ℝ) ≤ ((35300002291511159569/35310000000000000000 : ℝ)+2*(1689989916509/706200000000000 : ℝ)*(188/3125 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (35300002291511159569/35310000000000000000 : ℝ)+2*(1689989916509/706200000000000 : ℝ)*(188/3125 : ℝ)=(10000047938501523/10000000000000000 : ℝ) by norm_num, show 1+2*(491619074415169/50000000000000000000 : ℝ)=(25000491619074415169/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(69853246313032053/50000000000000000000 : ℝ)+(491619074415169/50000000000000000000 : ℝ) ≤ ((35300002291511159569/35310000000000000000 : ℝ)+(1689989916509/706200000000000 : ℝ)*((1007/5000 : ℝ)+(188/3125 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (35300002291511159569/35310000000000000000 : ℝ)+(1689989916509/706200000000000 : ℝ)*((1007/5000 : ℝ)+(188/3125 : ℝ))=(10003427918334541/10000000000000000 : ℝ) by norm_num, show 1+(69853246313032053/50000000000000000000 : ℝ)+(491619074415169/50000000000000000000 : ℝ)=(25035172432693723611/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(69853246313032053/50000000000000000000 : ℝ) ≤ ((35300002291511159569/35310000000000000000 : ℝ)+2*(1689989916509/706200000000000 : ℝ)*(1007/5000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (35300002291511159569/35310000000000000000 : ℝ)+2*(1689989916509/706200000000000 : ℝ)*(1007/5000 : ℝ)=(10006807898167559/10000000000000000 : ℝ) by norm_num, show 1+2*(69853246313032053/50000000000000000000 : ℝ)=(25069853246313032053/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35300002291511159569/35310000000000000000 : ℝ)*(X 1 0+X 2 0)+(1689989916509/706200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (188/3125 : ℝ)) (hi := (1007/5000 : ℝ)) (c := (35300002291511159569/35310000000000000000 : ℝ)) (alpha := (1689989916509/706200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35300002291511159569/35310000000000000000 : ℝ)*(X 0 1+X 2 1)+(1689989916509/706200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (188/3125 : ℝ)) (hi := (1007/5000 : ℝ)) (c := (35300002291511159569/35310000000000000000 : ℝ)) (alpha := (1689989916509/706200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35300002291511159569/35310000000000000000 : ℝ)*(X 0 2+X 1 2)+(1689989916509/706200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (188/3125 : ℝ)) (hi := (1007/5000 : ℝ)) (c := (35300002291511159569/35310000000000000000 : ℝ)) (alpha := (1689989916509/706200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10601559/50000000 : ℝ)*X 0 0+(5498517151/10000000000 : ℝ)*X 0 1+(5169765351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371036551/10000000000 : ℝ)*X 1 0+(-458159609/2000000000 : ℝ)*X 1 1+(5169770119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537103873/1000000000 : ℝ)*X 2 0+(1033953421/2000000000 : ℝ)*X 2 1+(-1145399547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2172987887/5000000000 : ℝ)*X 0 0+(4026977371/10000000000 : ℝ)*X 0 1+(4689623703/10000000000 : ℝ)*X 0 2+(2172987887/5000000000 : ℝ)*X 1 0+(4026977371/10000000000 : ℝ)*X 1 1+(4689623703/10000000000 : ℝ)*X 1 2+(2172987887/5000000000 : ℝ)*X 2 0+(4026977371/10000000000 : ℝ)*X 2 1+(4689623703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-26504951/125000000 : ℝ)*X 0 0+(5171929647/10000000000 : ℝ)*X 0 1+(5496333163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643629483/5000000000 : ℝ)*X 1 0+(-19642333/100000000 : ℝ)*X 1 1+(549633319/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643629573/5000000000 : ℝ)*X 2 0+(274816661/500000000 : ℝ)*X 2 1+(-491058253/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346148127/10000000000 : ℝ)*X 0 0+(46852639/100000000 : ℝ)*X 0 1+(4031378483/10000000000 : ℝ)*X 0 2+(4346148127/10000000000 : ℝ)*X 1 0+(46852639/100000000 : ℝ)*X 1 1+(4031378483/10000000000 : ℝ)*X 1 2+(4346148127/10000000000 : ℝ)*X 2 0+(46852639/100000000 : ℝ)*X 2 1+(4031378483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (553030543174816514382857461/294250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403586917/100000000000000 : ℝ)*(base19) + (1501164749/100000000000000 : ℝ)*(base23) + (178023913/100000000000000 : ℝ)*(upper2) + (176133/32000000000 : ℝ)*(upper3) + (251336179/100000000000000 : ℝ)*(upper4) + (1137752322510377/50000000000000 : ℝ)*(major0) + (1137752322510377/50000000000000 : ℝ)*(major1) + (1137752322510377/50000000000000 : ℝ)*(major2) + (190115406567713/6250000000000 : ℝ)*(sp0) + (1520939814411011/50000000000000 : ℝ)*(sp1) + (304187853124419/10000000000000 : ℝ)*(sp2) + (754555576393523/50000000000000 : ℝ)*(sp3) + (33527325531/100000000000000 : ℝ)*(sp4) + (2255274613/12500000000000 : ℝ)*(sp7) + (1509129194983951/100000000000000 : ℝ)*(f.failure) + (152094001620447/5000000000000 : ℝ)*(f.sum) + (7952121426433/17655000000000000000000000000 : ℝ)*base65 + (15011946539369497513/1765500000000000000000000000000000 : ℝ)*base67 + (12770293131419497513/1765500000000000000000000000000000 : ℝ)*base69 + (26045970729222997513/1765500000000000000000000000000000 : ℝ)*base71 + (40128974309113/17655000000000000000000000000 : ℝ)*base73 + (30902896443885997513/1765500000000000000000000000000000 : ℝ)*base75 + (14849606552763997513/1765500000000000000000000000000000 : ℝ)*base77 + (28761798627951997513/1765500000000000000000000000000000 : ℝ)*base79 + (29549121448157/17655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (45380723/10000000000000000000000 : ℝ)*base90 + (45380723/10000000000000000000000 : ℝ)*base92 + (45380723/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41341199757878249193153/11770000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51682417/5000000000000 : ℝ)*(base19) + (651762389/50000000000000 : ℝ)*(base23) + (45445007/100000000000000 : ℝ)*(upper2) + (74819691/50000000000000 : ℝ)*(upper3) + (7186507/10000000000000 : ℝ)*(upper5) + (2305950074991121/100000000000000 : ℝ)*(major0) + (2305950074991121/100000000000000 : ℝ)*(major1) + (2305950074991121/100000000000000 : ℝ)*(major2) + (2481942867/25000000000000 : ℝ)*(sp1) + (3727988293/25000000000000 : ℝ)*(sp2) + (770644808640929/25000000000000 : ℝ)*(sp4) + (770642068285977/25000000000000 : ℝ)*(sp5) + (1541281509542883/50000000000000 : ℝ)*(sp6) + (1529320798337809/100000000000000 : ℝ)*(sp7) + (1529320798337809/100000000000000 : ℝ)*(f.failure) + (770644808640929/25000000000000 : ℝ)*(f.sum) + (256889269968059/35310000000000000000000000000 : ℝ)*base65 + (14373068409993363151/3531000000000000000000000000000000 : ℝ)*base68 + (1454306812313636849/3531000000000000000000000000000000 : ℝ)*base69 + (1427604387509636849/3531000000000000000000000000000000 : ℝ)*base71 + (1107931538189/35310000000000000000000000000 : ℝ)*base73 + (7820067734310363151/3531000000000000000000000000000000 : ℝ)*base76 + (14082491584109636849/3531000000000000000000000000000000 : ℝ)*base77 + (13349309083161363151/3531000000000000000000000000000000 : ℝ)*base80 + (180569179351619/35310000000000000000000000000 : ℝ)*base81 + (25555757/10000000000000000000000 : ℝ)*base90 + (25555757/10000000000000000000000 : ℝ)*base92 + (25555757/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1209_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1007/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (188/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1209_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1209_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1209_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1209_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
