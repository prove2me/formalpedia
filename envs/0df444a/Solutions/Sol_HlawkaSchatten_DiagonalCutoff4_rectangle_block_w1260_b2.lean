-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1260_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:43.872989+00:00
-- url     : https://prove2.me/submissions/ad2d3aee-0c07-4ea8-abba-58f9ddcdae4c

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
theorem support_rectangle_w1260_s6_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-21116869/100000000 : ℝ)*x 0 + (539103681/1000000000 : ℝ)*x 1 + (5267285689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21116869/100000000 : ℝ)^8453 ≤ (401355950761/3125000000000 : ℝ)^6405 := by
    have hnat : (21116869 : ℕ)^8453*3125000000000^6405 ≤ 401355950761^6405*100000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21116869 100000000 401355950761 3125000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539103681/1000000000 : ℝ)^8453 ≤ (44246045526587/100000000000000 : ℝ)^6405 := by
    have hnat : (539103681 : ℕ)^8453*100000000000000^6405 ≤ 44246045526587^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539103681 1000000000 44246045526587 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267285689/10000000000 : ℝ)^8453 ≤ (10727641010199/25000000000000 : ℝ)^6405 := by
    have hnat : (5267285689 : ℕ)^8453*25000000000000^6405 ≤ 10727641010199^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267285689 10000000000 10727641010199 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21116869/100000000 : ℝ), (539103681/1000000000 : ℝ), (5267285689/10000000000 : ℝ)] ![(401355950761/3125000000000 : ℝ), (44246045526587/100000000000000 : ℝ), (10727641010199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21116869/100000000 : ℝ)|^8453 ≤ (401355950761/3125000000000 : ℝ)^6405
        have hw : |(-21116869/100000000 : ℝ)|=(21116869/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539103681/1000000000 : ℝ)|^8453 ≤ (44246045526587/100000000000000 : ℝ)^6405
        have hw : |(539103681/1000000000 : ℝ)|=(539103681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267285689/10000000000 : ℝ)|^8453 ≤ (10727641010199/25000000000000 : ℝ)^6405
        have hw : |(5267285689/10000000000 : ℝ)|=(5267285689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s6_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344256437/10000000000 : ℝ)*x 0 + (-217443017/1000000000 : ℝ)*x 1 + (1316821421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344256437/10000000000 : ℝ)^8453 ≤ (21870021042439/50000000000000 : ℝ)^6405 := by
    have hnat : (5344256437 : ℕ)^8453*50000000000000^6405 ≤ 21870021042439^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344256437 10000000000 21870021042439 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217443017/1000000000 : ℝ)^8453 ≤ (2669878782739/20000000000000 : ℝ)^6405 := by
    have hnat : (217443017 : ℕ)^8453*20000000000000^6405 ≤ 2669878782739^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217443017 1000000000 2669878782739 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316821421/2500000000 : ℝ)^8453 ≤ (21455281993519/50000000000000 : ℝ)^6405 := by
    have hnat : (1316821421 : ℕ)^8453*50000000000000^6405 ≤ 21455281993519^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316821421 2500000000 21455281993519 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344256437/10000000000 : ℝ), (-217443017/1000000000 : ℝ), (1316821421/2500000000 : ℝ)] ![(21870021042439/50000000000000 : ℝ), (2669878782739/20000000000000 : ℝ), (21455281993519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344256437/10000000000 : ℝ)|^8453 ≤ (21870021042439/50000000000000 : ℝ)^6405
        have hw : |(5344256437/10000000000 : ℝ)|=(5344256437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217443017/1000000000 : ℝ)|^8453 ≤ (2669878782739/20000000000000 : ℝ)^6405
        have hw : |(-217443017/1000000000 : ℝ)|=(217443017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316821421/2500000000 : ℝ)|^8453 ≤ (21455281993519/50000000000000 : ℝ)^6405
        have hw : |(1316821421/2500000000 : ℝ)|=(1316821421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s6_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344256443/10000000000 : ℝ)*x 0 + (5267285683/10000000000 : ℝ)*x 1 + (-1087215081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344256443/10000000000 : ℝ)^8453 ≤ (43740042149687/100000000000000 : ℝ)^6405 := by
    have hnat : (5344256443 : ℕ)^8453*100000000000000^6405 ≤ 43740042149687^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344256443 10000000000 43740042149687 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267285683/10000000000 : ℝ)^8453 ≤ (42910563976287/100000000000000 : ℝ)^6405 := by
    have hnat : (5267285683 : ℕ)^8453*100000000000000^6405 ≤ 42910563976287^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267285683 10000000000 42910563976287 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087215081/5000000000 : ℝ)^8453 ≤ (3337348462219/25000000000000 : ℝ)^6405 := by
    have hnat : (1087215081 : ℕ)^8453*25000000000000^6405 ≤ 3337348462219^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087215081 5000000000 3337348462219 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344256443/10000000000 : ℝ), (5267285683/10000000000 : ℝ), (-1087215081/5000000000 : ℝ)] ![(43740042149687/100000000000000 : ℝ), (42910563976287/100000000000000 : ℝ), (3337348462219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344256443/10000000000 : ℝ)|^8453 ≤ (43740042149687/100000000000000 : ℝ)^6405
        have hw : |(5344256443/10000000000 : ℝ)|=(5344256443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267285683/10000000000 : ℝ)|^8453 ≤ (42910563976287/100000000000000 : ℝ)^6405
        have hw : |(5267285683/10000000000 : ℝ)|=(5267285683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087215081/5000000000 : ℝ)|^8453 ≤ (3337348462219/25000000000000 : ℝ)^6405
        have hw : |(-1087215081/5000000000 : ℝ)|=(1087215081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s6_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348301777/10000000000 : ℝ)*x 0 + (2112056367/5000000000 : ℝ)*x 1 + (2238011709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348301777/10000000000 : ℝ)^8453 ≤ (6663498722209/20000000000000 : ℝ)^6405 := by
    have hnat : (4348301777 : ℕ)^8453*20000000000000^6405 ≤ 6663498722209^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348301777 10000000000 6663498722209 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112056367/5000000000 : ℝ)^8453 ≤ (6413488923783/20000000000000 : ℝ)^6405 := by
    have hnat : (2112056367 : ℕ)^8453*20000000000000^6405 ≤ 6413488923783^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112056367 5000000000 6413488923783 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238011709/5000000000 : ℝ)^8453 ≤ (17307530880629/50000000000000 : ℝ)^6405 := by
    have hnat : (2238011709 : ℕ)^8453*50000000000000^6405 ≤ 17307530880629^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238011709 5000000000 17307530880629 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348301777/10000000000 : ℝ), (2112056367/5000000000 : ℝ), (2238011709/5000000000 : ℝ)] ![(6663498722209/20000000000000 : ℝ), (6413488923783/20000000000000 : ℝ), (17307530880629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348301777/10000000000 : ℝ)|^8453 ≤ (6663498722209/20000000000000 : ℝ)^6405
        have hw : |(4348301777/10000000000 : ℝ)|=(4348301777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112056367/5000000000 : ℝ)|^8453 ≤ (6413488923783/20000000000000 : ℝ)^6405
        have hw : |(2112056367/5000000000 : ℝ)|=(2112056367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238011709/5000000000 : ℝ)|^8453 ≤ (17307530880629/50000000000000 : ℝ)^6405
        have hw : |(2238011709/5000000000 : ℝ)|=(2238011709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s6_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-527922947/2500000000 : ℝ)*x 0 + (5267598451/10000000000 : ℝ)*x 1 + (5390722733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527922947/2500000000 : ℝ)^8453 ≤ (2568685931863/20000000000000 : ℝ)^6405 := by
    have hnat : (527922947 : ℕ)^8453*20000000000000^6405 ≤ 2568685931863^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527922947 2500000000 2568685931863 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267598451/10000000000 : ℝ)^8453 ≤ (42913926733549/100000000000000 : ℝ)^6405 := by
    have hnat : (5267598451 : ℕ)^8453*100000000000000^6405 ≤ 42913926733549^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267598451 10000000000 42913926733549 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390722733/10000000000 : ℝ)^8453 ≤ (44242643591767/100000000000000 : ℝ)^6405 := by
    have hnat : (5390722733 : ℕ)^8453*100000000000000^6405 ≤ 44242643591767^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390722733 10000000000 44242643591767 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527922947/2500000000 : ℝ), (5267598451/10000000000 : ℝ), (5390722733/10000000000 : ℝ)] ![(2568685931863/20000000000000 : ℝ), (42913926733549/100000000000000 : ℝ), (44242643591767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527922947/2500000000 : ℝ)|^8453 ≤ (2568685931863/20000000000000 : ℝ)^6405
        have hw : |(-527922947/2500000000 : ℝ)|=(527922947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267598451/10000000000 : ℝ)|^8453 ≤ (42913926733549/100000000000000 : ℝ)^6405
        have hw : |(5267598451/10000000000 : ℝ)|=(5267598451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390722733/10000000000 : ℝ)|^8453 ≤ (44242643591767/100000000000000 : ℝ)^6405
        have hw : |(5390722733/10000000000 : ℝ)|=(5390722733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s6_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312643077/10000000000 : ℝ)*x 0 + (-410198627/2000000000 : ℝ)*x 1 + (2695361117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312643077/10000000000 : ℝ)^8453 ≤ (43398894084737/100000000000000 : ℝ)^6405 := by
    have hnat : (5312643077 : ℕ)^8453*100000000000000^6405 ≤ 43398894084737^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312643077 10000000000 43398894084737 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410198627/2000000000 : ℝ)^8453 ≤ (6179233859863/50000000000000 : ℝ)^6405 := by
    have hnat : (410198627 : ℕ)^8453*50000000000000^6405 ≤ 6179233859863^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410198627 2000000000 6179233859863 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695361117/5000000000 : ℝ)^8453 ≤ (44242638186883/100000000000000 : ℝ)^6405 := by
    have hnat : (2695361117 : ℕ)^8453*100000000000000^6405 ≤ 44242638186883^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695361117 5000000000 44242638186883 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312643077/10000000000 : ℝ), (-410198627/2000000000 : ℝ), (2695361117/5000000000 : ℝ)] ![(43398894084737/100000000000000 : ℝ), (6179233859863/50000000000000 : ℝ), (44242638186883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312643077/10000000000 : ℝ)|^8453 ≤ (43398894084737/100000000000000 : ℝ)^6405
        have hw : |(5312643077/10000000000 : ℝ)|=(5312643077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410198627/2000000000 : ℝ)|^8453 ≤ (6179233859863/50000000000000 : ℝ)^6405
        have hw : |(-410198627/2000000000 : ℝ)|=(410198627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695361117/5000000000 : ℝ)|^8453 ≤ (44242638186883/100000000000000 : ℝ)^6405
        have hw : |(2695361117/5000000000 : ℝ)|=(2695361117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s6_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312643349/10000000000 : ℝ)*x 0 + (1347680463/2500000000 : ℝ)*x 1 + (-410198657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312643349/10000000000 : ℝ)^8453 ≤ (21699448508587/50000000000000 : ℝ)^6405 := by
    have hnat : (5312643349 : ℕ)^8453*50000000000000^6405 ≤ 21699448508587^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312643349 10000000000 21699448508587 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347680463/2500000000 : ℝ)^8453 ≤ (44242634049277/100000000000000 : ℝ)^6405 := by
    have hnat : (1347680463 : ℕ)^8453*100000000000000^6405 ≤ 44242634049277^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347680463 2500000000 44242634049277 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410198657/2000000000 : ℝ)^8453 ≤ (12358468912569/100000000000000 : ℝ)^6405 := by
    have hnat : (410198657 : ℕ)^8453*100000000000000^6405 ≤ 12358468912569^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410198657 2000000000 12358468912569 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312643349/10000000000 : ℝ), (1347680463/2500000000 : ℝ), (-410198657/2000000000 : ℝ)] ![(21699448508587/50000000000000 : ℝ), (44242634049277/100000000000000 : ℝ), (12358468912569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312643349/10000000000 : ℝ)|^8453 ≤ (21699448508587/50000000000000 : ℝ)^6405
        have hw : |(5312643349/10000000000 : ℝ)|=(5312643349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347680463/2500000000 : ℝ)|^8453 ≤ (44242634049277/100000000000000 : ℝ)^6405
        have hw : |(1347680463/2500000000 : ℝ)|=(1347680463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410198657/2000000000 : ℝ)|^8453 ≤ (12358468912569/100000000000000 : ℝ)^6405
        have hw : |(-410198657/2000000000 : ℝ)|=(410198657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s6_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348311097/10000000000 : ℝ)*x 0 + (4475386131/10000000000 : ℝ)*x 1 + (264047031/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348311097/10000000000 : ℝ)^8453 ≤ (16658793928253/50000000000000 : ℝ)^6405 := by
    have hnat : (4348311097 : ℕ)^8453*50000000000000^6405 ≤ 16658793928253^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348311097 10000000000 16658793928253 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475386131/10000000000 : ℝ)^8453 ≤ (3460855762443/10000000000000 : ℝ)^6405 := by
    have hnat : (4475386131 : ℕ)^8453*10000000000000^6405 ≤ 3460855762443^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475386131 10000000000 3460855762443 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264047031/625000000 : ℝ)^8453 ≤ (8018463623419/25000000000000 : ℝ)^6405 := by
    have hnat : (264047031 : ℕ)^8453*25000000000000^6405 ≤ 8018463623419^6405*625000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264047031 625000000 8018463623419 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348311097/10000000000 : ℝ), (4475386131/10000000000 : ℝ), (264047031/625000000 : ℝ)] ![(16658793928253/50000000000000 : ℝ), (3460855762443/10000000000000 : ℝ), (8018463623419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348311097/10000000000 : ℝ)|^8453 ≤ (16658793928253/50000000000000 : ℝ)^6405
        have hw : |(4348311097/10000000000 : ℝ)|=(4348311097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475386131/10000000000 : ℝ)|^8453 ≤ (3460855762443/10000000000000 : ℝ)^6405
        have hw : |(4475386131/10000000000 : ℝ)|=(4475386131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264047031/625000000 : ℝ)|^8453 ≤ (8018463623419/25000000000000 : ℝ)^6405
        have hw : |(264047031/625000000 : ℝ)|=(264047031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1437/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7059/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11477/100000 : ℝ) ^ (2113/512 : ℝ) ≤ (13181225855640809/100000000000000000000 : ℝ) := by
    have hpowers : (11477/100000 : ℝ)^2113 ≤ (13181225855640809/100000000000000000000 : ℝ)^512 := by
      have hnat : (11477 : ℕ)^2113*100000000000000000000^512 ≤ 13181225855640809^512*100000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11477 100000 13181225855640809 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11477/100000 : ℝ)) (X := (13181225855640809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7069/50000 : ℝ) ^ (2113/512 : ℝ) ≤ (31166713444719537/100000000000000000000 : ℝ) := by
    have hpowers : (7069/50000 : ℝ)^2113 ≤ (31166713444719537/100000000000000000000 : ℝ)^512 := by
      have hnat : (7069 : ℕ)^2113*100000000000000000000^512 ≤ 31166713444719537^512*50000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7069 50000 31166713444719537 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7069/50000 : ℝ)) (X := (31166713444719537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013181225855640809/50000000000000000000 : ℝ) ≤ (5000319361747337/5000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50013181225855640809/50000000000000000000 : ℝ)^512 ≤ (5000319361747337/5000000000000000 : ℝ)^2113 := by
      have hnat : (50013181225855640809 : ℕ)^512*5000000000000000^2113 ≤ 5000319361747337^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013181225855640809 50000000000000000000 5000319361747337 5000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000319361747337/5000000000000000 : ℝ)) (X := (50013181225855640809/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022173969650180173/50000000000000000000 : ℝ) ≤ (5000537206129957/5000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50022173969650180173/50000000000000000000 : ℝ)^512 ≤ (5000537206129957/5000000000000000 : ℝ)^2113 := by
      have hnat : (50022173969650180173 : ℕ)^512*5000000000000000^2113 ≤ 5000537206129957^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022173969650180173 50000000000000000000 5000537206129957 5000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000537206129957/5000000000000000 : ℝ)) (X := (50022173969650180173/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031166713444719537/50000000000000000000 : ℝ) ≤ (5000755050512577/5000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50031166713444719537/50000000000000000000 : ℝ)^512 ≤ (5000755050512577/5000000000000000 : ℝ)^2113 := by
      have hnat : (50031166713444719537 : ℕ)^512*5000000000000000^2113 ≤ 5000755050512577^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031166713444719537 50000000000000000000 5000755050512577 5000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000755050512577/5000000000000000 : ℝ)) (X := (50031166713444719537/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13181225855640809/100000000000000000000 : ℝ) ≤ ((13300849421651004277/13305000000000000000 : ℝ)+2*(10892219131/6652500000000 : ℝ)*(11477/100000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (13300849421651004277/13305000000000000000 : ℝ)+2*(10892219131/6652500000000 : ℝ)*(11477/100000 : ℝ)=(5000319361747337/5000000000000000 : ℝ) by norm_num, show 1+2*(13181225855640809/100000000000000000000 : ℝ)=(50013181225855640809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31166713444719537/100000000000000000000 : ℝ)+(13181225855640809/100000000000000000000 : ℝ) ≤ ((13300849421651004277/13305000000000000000 : ℝ)+(10892219131/6652500000000 : ℝ)*((7069/50000 : ℝ)+(11477/100000 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (13300849421651004277/13305000000000000000 : ℝ)+(10892219131/6652500000000 : ℝ)*((7069/50000 : ℝ)+(11477/100000 : ℝ))=(5000537206129957/5000000000000000 : ℝ) by norm_num, show 1+(31166713444719537/100000000000000000000 : ℝ)+(13181225855640809/100000000000000000000 : ℝ)=(50022173969650180173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31166713444719537/100000000000000000000 : ℝ) ≤ ((13300849421651004277/13305000000000000000 : ℝ)+2*(10892219131/6652500000000 : ℝ)*(7069/50000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (13300849421651004277/13305000000000000000 : ℝ)+2*(10892219131/6652500000000 : ℝ)*(7069/50000 : ℝ)=(5000755050512577/5000000000000000 : ℝ) by norm_num, show 1+2*(31166713444719537/100000000000000000000 : ℝ)=(50031166713444719537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13300849421651004277/13305000000000000000 : ℝ)*(X 1 0+X 2 0)+(10892219131/6652500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (13300849421651004277/13305000000000000000 : ℝ)) (alpha := (10892219131/6652500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13300849421651004277/13305000000000000000 : ℝ)*(X 0 1+X 2 1)+(10892219131/6652500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (13300849421651004277/13305000000000000000 : ℝ)) (alpha := (10892219131/6652500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13300849421651004277/13305000000000000000 : ℝ)*(X 0 2+X 1 2)+(10892219131/6652500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (13300849421651004277/13305000000000000000 : ℝ)) (alpha := (10892219131/6652500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21116869/100000000 : ℝ)*X 0 0+(539103681/1000000000 : ℝ)*X 0 1+(5267285689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344256437/10000000000 : ℝ)*X 1 0+(-217443017/1000000000 : ℝ)*X 1 1+(1316821421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344256443/10000000000 : ℝ)*X 2 0+(5267285683/10000000000 : ℝ)*X 2 1+(-1087215081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348301777/10000000000 : ℝ)*X 0 0+(2112056367/5000000000 : ℝ)*X 0 1+(2238011709/5000000000 : ℝ)*X 0 2+(4348301777/10000000000 : ℝ)*X 1 0+(2112056367/5000000000 : ℝ)*X 1 1+(2238011709/5000000000 : ℝ)*X 1 2+(4348301777/10000000000 : ℝ)*X 2 0+(2112056367/5000000000 : ℝ)*X 2 1+(2238011709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527922947/2500000000 : ℝ)*X 0 0+(5267598451/10000000000 : ℝ)*X 0 1+(5390722733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312643077/10000000000 : ℝ)*X 1 0+(-410198627/2000000000 : ℝ)*X 1 1+(2695361117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312643349/10000000000 : ℝ)*X 2 0+(1347680463/2500000000 : ℝ)*X 2 1+(-410198657/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348311097/10000000000 : ℝ)*X 0 0+(4475386131/10000000000 : ℝ)*X 0 1+(264047031/625000000 : ℝ)*X 0 2+(4348311097/10000000000 : ℝ)*X 1 0+(4475386131/10000000000 : ℝ)*X 1 1+(264047031/625000000 : ℝ)*X 1 2+(4348311097/10000000000 : ℝ)*X 2 0+(4475386131/10000000000 : ℝ)*X 2 1+(264047031/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (447783220117264368403528657/55437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157035067/10000000000000 : ℝ)*(base19) + (1468155487/100000000000000 : ℝ)*(base23) + (2973211/5000000000000 : ℝ)*(lower2) + (200684623/100000000000000 : ℝ)*(upper3) + (66505219/50000000000000 : ℝ)*(upper5) + (3012632108897059/50000000000000 : ℝ)*(major0) + (3012632108897059/50000000000000 : ℝ)*(major1) + (3012632108897059/50000000000000 : ℝ)*(major2) + (4040389889184789/50000000000000 : ℝ)*(sp0) + (16161643663279/200000000000 : ℝ)*(sp1) + (8080821933834683/100000000000000 : ℝ)*(sp2) + (1984840879074021/50000000000000 : ℝ)*(sp3) + (2726476287/6250000000000 : ℝ)*(sp4) + (11503103973/50000000000000 : ℝ)*(sp7) + (992426191088997/25000000000000 : ℝ)*(f.failure) + (808082340199017/10000000000000 : ℝ)*(f.sum) + (4014183977759/665250000000000000000000000 : ℝ)*base66 + (469334676133926219/221750000000000000000000000000000 : ℝ)*base68 + (634706457294073781/221750000000000000000000000000000 : ℝ)*base69 + (757369477518573781/221750000000000000000000000000000 : ℝ)*base71 + (264416523727/266100000000000000000000000 : ℝ)*base73 + (6048681522515573781/221750000000000000000000000000000 : ℝ)*base75 + (1604199227967823781/221750000000000000000000000000000 : ℝ)*base77 + (674524044071323781/221750000000000000000000000000000 : ℝ)*base79 + (8109064677811/1330500000000000000000000000 : ℝ)*base82 + (15519499/2500000000000000000000 : ℝ)*base89 + (15519499/2500000000000000000000 : ℝ)*base91 + (15519499/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69413338489844474202758541/27718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2337209071/100000000000000 : ℝ)*(base19) + (3157541661/100000000000000 : ℝ)*(base23) + (115580539/50000000000000 : ℝ)*(upper2) + (121468401/50000000000000 : ℝ)*(upper5) + (1513972427337483/25000000000000 : ℝ)*(major0) + (1513972427337483/25000000000000 : ℝ)*(major1) + (1513972427337483/25000000000000 : ℝ)*(major2) + (1662734509/25000000000000 : ℝ)*(sp0) + (61092044901/100000000000000 : ℝ)*(sp1) + (55948118029/100000000000000 : ℝ)*(sp2) + (2030472630252321/25000000000000 : ℝ)*(sp4) + (8121833742693349/100000000000000 : ℝ)*(sp5) + (812183806628763/10000000000000 : ℝ)*(sp6) + (1994941081639573/50000000000000 : ℝ)*(sp7) + (1994941081639573/50000000000000 : ℝ)*(f.failure) + (203047429298683/2500000000000 : ℝ)*(f.sum) + (726528003739/443500000000000000000000000 : ℝ)*base66 + (2668472066123278403/110875000000000000000000000000000 : ℝ)*base68 + (659241886062528403/110875000000000000000000000000000 : ℝ)*base70 + (1797871299320028403/110875000000000000000000000000000 : ℝ)*base72 + (1340589800411/177400000000000000000000000 : ℝ)*base74 + (438522909804778403/110875000000000000000000000000000 : ℝ)*base76 + (1497079743308653403/110875000000000000000000000000000 : ℝ)*base78 + (1096394408689096597/110875000000000000000000000000000 : ℝ)*base79 + (178024631819/55437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (63321691/5000000000000000000000 : ℝ)*base89 + (63321691/5000000000000000000000 : ℝ)*base91 + (63321691/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1260_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1260_s7_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16893621/80000000 : ℝ)*x 0 + (43126849/80000000 : ℝ)*x 1 + (5267455979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16893621/80000000 : ℝ)^8453 ≤ (12843516645773/100000000000000 : ℝ)^6405 := by
    have hnat : (16893621 : ℕ)^8453*100000000000000^6405 ≤ 12843516645773^6405*80000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16893621 80000000 12843516645773 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43126849/80000000 : ℝ)^8453 ≤ (2765255526477/6250000000000 : ℝ)^6405 := by
    have hnat : (43126849 : ℕ)^8453*6250000000000^6405 ≤ 2765255526477^6405*80000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43126849 80000000 2765255526477 6250000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267455979/10000000000 : ℝ)^8453 ≤ (42912394923297/100000000000000 : ℝ)^6405 := by
    have hnat : (5267455979 : ℕ)^8453*100000000000000^6405 ≤ 42912394923297^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267455979 10000000000 42912394923297 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16893621/80000000 : ℝ), (43126849/80000000 : ℝ), (5267455979/10000000000 : ℝ)] ![(12843516645773/100000000000000 : ℝ), (2765255526477/6250000000000 : ℝ), (42912394923297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16893621/80000000 : ℝ)|^8453 ≤ (12843516645773/100000000000000 : ℝ)^6405
        have hw : |(-16893621/80000000 : ℝ)|=(16893621/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43126849/80000000 : ℝ)|^8453 ≤ (2765255526477/6250000000000 : ℝ)^6405
        have hw : |(43126849/80000000 : ℝ)|=(43126849/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267455979/10000000000 : ℝ)|^8453 ≤ (42912394923297/100000000000000 : ℝ)^6405
        have hw : |(5267455979/10000000000 : ℝ)|=(5267455979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344210377/10000000000 : ℝ)*x 0 + (-434853021/2000000000 : ℝ)*x 1 + (1316864087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344210377/10000000000 : ℝ)^8453 ≤ (43739544568963/100000000000000 : ℝ)^6405 := by
    have hnat : (5344210377 : ℕ)^8453*100000000000000^6405 ≤ 43739544568963^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344210377 10000000000 43739544568963 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434853021/2000000000 : ℝ)^8453 ≤ (13348056525321/100000000000000 : ℝ)^6405 := by
    have hnat : (434853021 : ℕ)^8453*100000000000000^6405 ≤ 13348056525321^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434853021 2000000000 13348056525321 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316864087/2500000000 : ℝ)^8453 ≤ (21456199445321/50000000000000 : ℝ)^6405 := by
    have hnat : (1316864087 : ℕ)^8453*50000000000000^6405 ≤ 21456199445321^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316864087 2500000000 21456199445321 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344210377/10000000000 : ℝ), (-434853021/2000000000 : ℝ), (1316864087/2500000000 : ℝ)] ![(43739544568963/100000000000000 : ℝ), (13348056525321/100000000000000 : ℝ), (21456199445321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344210377/10000000000 : ℝ)|^8453 ≤ (43739544568963/100000000000000 : ℝ)^6405
        have hw : |(5344210377/10000000000 : ℝ)|=(5344210377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434853021/2000000000 : ℝ)|^8453 ≤ (13348056525321/100000000000000 : ℝ)^6405
        have hw : |(-434853021/2000000000 : ℝ)|=(434853021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316864087/2500000000 : ℝ)|^8453 ≤ (21456199445321/50000000000000 : ℝ)^6405
        have hw : |(1316864087/2500000000 : ℝ)|=(1316864087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336052627/2500000000 : ℝ)*x 0 + (5267456283/10000000000 : ℝ)*x 1 + (-2174265017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336052627/2500000000 : ℝ)^8453 ≤ (21869772991977/50000000000000 : ℝ)^6405 := by
    have hnat : (1336052627 : ℕ)^8453*50000000000000^6405 ≤ 21869772991977^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336052627 2500000000 21869772991977 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267456283/10000000000 : ℝ)^8453 ≤ (42912398191787/100000000000000 : ℝ)^6405 := by
    have hnat : (5267456283 : ℕ)^8453*100000000000000^6405 ≤ 42912398191787^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267456283 10000000000 42912398191787 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174265017/10000000000 : ℝ)^8453 ≤ (13348055812337/100000000000000 : ℝ)^6405 := by
    have hnat : (2174265017 : ℕ)^8453*100000000000000^6405 ≤ 13348055812337^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174265017 10000000000 13348055812337 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336052627/2500000000 : ℝ), (5267456283/10000000000 : ℝ), (-2174265017/10000000000 : ℝ)] ![(21869772991977/50000000000000 : ℝ), (42912398191787/100000000000000 : ℝ), (13348055812337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336052627/2500000000 : ℝ)|^8453 ≤ (21869772991977/50000000000000 : ℝ)^6405
        have hw : |(1336052627/2500000000 : ℝ)|=(1336052627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267456283/10000000000 : ℝ)|^8453 ≤ (42912398191787/100000000000000 : ℝ)^6405
        have hw : |(5267456283/10000000000 : ℝ)|=(5267456283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174265017/10000000000 : ℝ)|^8453 ≤ (13348055812337/100000000000000 : ℝ)^6405
        have hw : |(-2174265017/10000000000 : ℝ)|=(2174265017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543538877/1250000000 : ℝ)*x 0 + (2112234589/5000000000 : ℝ)*x 1 + (4475664351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543538877/1250000000 : ℝ)^8453 ≤ (1665879351871/5000000000000 : ℝ)^6405 := by
    have hnat : (543538877 : ℕ)^8453*5000000000000^6405 ≤ 1665879351871^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543538877 1250000000 1665879351871 5000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112234589/5000000000 : ℝ)^8453 ≤ (256568126787/800000000000 : ℝ)^6405 := by
    have hnat : (2112234589 : ℕ)^8453*800000000000^6405 ≤ 256568126787^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112234589 5000000000 256568126787 800000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475664351/10000000000 : ℝ)^8453 ≤ (3461139709509/10000000000000 : ℝ)^6405 := by
    have hnat : (4475664351 : ℕ)^8453*10000000000000^6405 ≤ 3461139709509^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475664351 10000000000 3461139709509 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543538877/1250000000 : ℝ), (2112234589/5000000000 : ℝ), (4475664351/10000000000 : ℝ)] ![(1665879351871/5000000000000 : ℝ), (256568126787/800000000000 : ℝ), (3461139709509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543538877/1250000000 : ℝ)|^8453 ≤ (1665879351871/5000000000000 : ℝ)^6405
        have hw : |(543538877/1250000000 : ℝ)|=(543538877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112234589/5000000000 : ℝ)|^8453 ≤ (256568126787/800000000000 : ℝ)^6405
        have hw : |(2112234589/5000000000 : ℝ)|=(2112234589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475664351/10000000000 : ℝ)|^8453 ≤ (3461139709509/10000000000000 : ℝ)^6405
        have hw : |(4475664351/10000000000 : ℝ)|=(4475664351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-105585379/500000000 : ℝ)*x 0 + (5267767351/10000000000 : ℝ)*x 1 + (1347635843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105585379/500000000 : ℝ)^8453 ≤ (6421778209313/50000000000000 : ℝ)^6405 := by
    have hnat : (105585379 : ℕ)^8453*50000000000000^6405 ≤ 6421778209313^6405*500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105585379 500000000 6421778209313 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267767351/10000000000 : ℝ)^8453 ≤ (42915742705787/100000000000000 : ℝ)^6405 := by
    have hnat : (5267767351 : ℕ)^8453*100000000000000^6405 ≤ 42915742705787^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267767351 10000000000 42915742705787 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347635843/2500000000 : ℝ)^8453 ≤ (11060175216483/25000000000000 : ℝ)^6405 := by
    have hnat : (1347635843 : ℕ)^8453*25000000000000^6405 ≤ 11060175216483^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347635843 2500000000 11060175216483 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105585379/500000000 : ℝ), (5267767351/10000000000 : ℝ), (1347635843/2500000000 : ℝ)] ![(6421778209313/50000000000000 : ℝ), (42915742705787/100000000000000 : ℝ), (11060175216483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105585379/500000000 : ℝ)|^8453 ≤ (6421778209313/50000000000000 : ℝ)^6405
        have hw : |(-105585379/500000000 : ℝ)|=(105585379/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267767351/10000000000 : ℝ)|^8453 ≤ (42915742705787/100000000000000 : ℝ)^6405
        have hw : |(5267767351/10000000000 : ℝ)|=(5267767351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347635843/2500000000 : ℝ)|^8453 ≤ (11060175216483/25000000000000 : ℝ)^6405
        have hw : |(1347635843/2500000000 : ℝ)|=(1347635843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312686899/10000000000 : ℝ)*x 0 + (-2051177949/10000000000 : ℝ)*x 1 + (1347635731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312686899/10000000000 : ℝ)^8453 ≤ (43399366531117/100000000000000 : ℝ)^6405 := by
    have hnat : (5312686899 : ℕ)^8453*100000000000000^6405 ≤ 43399366531117^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312686899 10000000000 43399366531117 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051177949/10000000000 : ℝ)^8453 ≤ (12359937435241/100000000000000 : ℝ)^6405 := by
    have hnat : (2051177949 : ℕ)^8453*100000000000000^6405 ≤ 12359937435241^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051177949 10000000000 12359937435241 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347635731/2500000000 : ℝ)^8453 ≤ (44240696013503/100000000000000 : ℝ)^6405 := by
    have hnat : (1347635731 : ℕ)^8453*100000000000000^6405 ≤ 44240696013503^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347635731 2500000000 44240696013503 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312686899/10000000000 : ℝ), (-2051177949/10000000000 : ℝ), (1347635731/2500000000 : ℝ)] ![(43399366531117/100000000000000 : ℝ), (12359937435241/100000000000000 : ℝ), (44240696013503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312686899/10000000000 : ℝ)|^8453 ≤ (43399366531117/100000000000000 : ℝ)^6405
        have hw : |(5312686899/10000000000 : ℝ)|=(5312686899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051177949/10000000000 : ℝ)|^8453 ≤ (12359937435241/100000000000000 : ℝ)^6405
        have hw : |(-2051177949/10000000000 : ℝ)|=(2051177949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347635731/2500000000 : ℝ)|^8453 ≤ (44240696013503/100000000000000 : ℝ)^6405
        have hw : |(1347635731/2500000000 : ℝ)|=(1347635731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664085861/1250000000 : ℝ)*x 0 + (5390543023/10000000000 : ℝ)*x 1 + (-205117783/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664085861/1250000000 : ℝ)^8453 ≤ (1735974656501/4000000000000 : ℝ)^6405 := by
    have hnat : (664085861 : ℕ)^8453*4000000000000^6405 ≤ 1735974656501^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664085861 1250000000 1735974656501 4000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390543023/10000000000 : ℝ)^8453 ≤ (44240697085803/100000000000000 : ℝ)^6405 := by
    have hnat : (5390543023 : ℕ)^8453*100000000000000^6405 ≤ 44240697085803^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390543023 10000000000 44240697085803 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205117783/1000000000 : ℝ)^8453 ≤ (12359936488891/100000000000000 : ℝ)^6405 := by
    have hnat : (205117783 : ℕ)^8453*100000000000000^6405 ≤ 12359936488891^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205117783 1000000000 12359936488891 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664085861/1250000000 : ℝ), (5390543023/10000000000 : ℝ), (-205117783/1000000000 : ℝ)] ![(1735974656501/4000000000000 : ℝ), (44240697085803/100000000000000 : ℝ), (12359936488891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664085861/1250000000 : ℝ)|^8453 ≤ (1735974656501/4000000000000 : ℝ)^6405
        have hw : |(664085861/1250000000 : ℝ)|=(664085861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390543023/10000000000 : ℝ)|^8453 ≤ (44240697085803/100000000000000 : ℝ)^6405
        have hw : |(5390543023/10000000000 : ℝ)|=(5390543023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-205117783/1000000000 : ℝ)|^8453 ≤ (12359936488891/100000000000000 : ℝ)^6405
        have hw : |(-205117783/1000000000 : ℝ)|=(205117783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174159987/5000000000 : ℝ)*x 0 + (1118757663/2500000000 : ℝ)*x 1 + (211255281/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174159987/5000000000 : ℝ)^8453 ≤ (16658838811167/50000000000000 : ℝ)^6405 := by
    have hnat : (2174159987 : ℕ)^8453*50000000000000^6405 ≤ 16658838811167^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174159987 5000000000 16658838811167 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118757663/2500000000 : ℝ)^8453 ≤ (34604929742391/100000000000000 : ℝ)^6405 := by
    have hnat : (1118757663 : ℕ)^8453*100000000000000^6405 ≤ 34604929742391^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118757663 2500000000 34604929742391 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211255281/500000000 : ℝ)^8453 ≤ (8019348157693/25000000000000 : ℝ)^6405 := by
    have hnat : (211255281 : ℕ)^8453*25000000000000^6405 ≤ 8019348157693^6405*500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211255281 500000000 8019348157693 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174159987/5000000000 : ℝ), (1118757663/2500000000 : ℝ), (211255281/500000000 : ℝ)] ![(16658838811167/50000000000000 : ℝ), (34604929742391/100000000000000 : ℝ), (8019348157693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174159987/5000000000 : ℝ)|^8453 ≤ (16658838811167/50000000000000 : ℝ)^6405
        have hw : |(2174159987/5000000000 : ℝ)|=(2174159987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118757663/2500000000 : ℝ)|^8453 ≤ (34604929742391/100000000000000 : ℝ)^6405
        have hw : |(1118757663/2500000000 : ℝ)|=(1118757663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211255281/500000000 : ℝ)|^8453 ≤ (8019348157693/25000000000000 : ℝ)^6405
        have hw : |(211255281/500000000 : ℝ)|=(211255281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s7_8 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-38607993/10000000000 : ℝ)*x 0 + (5911349709/10000000000 : ℝ)*x 1 + (5911408179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38607993/10000000000 : ℝ)^8453 ≤ (16328895379/25000000000000 : ℝ)^6405 := by
    have hnat : (38607993 : ℕ)^8453*25000000000000^6405 ≤ 16328895379^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38607993 10000000000 16328895379 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5911349709/10000000000 : ℝ)^8453 ≤ (49967016076147/100000000000000 : ℝ)^6405 := by
    have hnat : (5911349709 : ℕ)^8453*100000000000000^6405 ≤ 49967016076147^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911349709 10000000000 49967016076147 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5911408179/10000000000 : ℝ)^8453 ≤ (3122979271153/6250000000000 : ℝ)^6405 := by
    have hnat : (5911408179 : ℕ)^8453*6250000000000^6405 ≤ 3122979271153^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911408179 10000000000 3122979271153 6250000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38607993/10000000000 : ℝ), (5911349709/10000000000 : ℝ), (5911408179/10000000000 : ℝ)] ![(16328895379/25000000000000 : ℝ), (49967016076147/100000000000000 : ℝ), (3122979271153/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38607993/10000000000 : ℝ)|^8453 ≤ (16328895379/25000000000000 : ℝ)^6405
        have hw : |(-38607993/10000000000 : ℝ)|=(38607993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5911349709/10000000000 : ℝ)|^8453 ≤ (49967016076147/100000000000000 : ℝ)^6405
        have hw : |(5911349709/10000000000 : ℝ)|=(5911349709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5911408179/10000000000 : ℝ)|^8453 ≤ (3122979271153/6250000000000 : ℝ)^6405
        have hw : |(5911408179/10000000000 : ℝ)|=(5911408179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (23/200 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1437/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1437/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1437/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1437/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1437/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1437/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1437/12500 : ℝ) ^ (2113/512 : ℝ) ≤ (6635757393291099/50000000000000000000 : ℝ) := by
    have hpowers : (1437/12500 : ℝ)^2113 ≤ (6635757393291099/50000000000000000000 : ℝ)^512 := by
      have hnat : (1437 : ℕ)^2113*50000000000000000000^512 ≤ 6635757393291099^512*12500^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1437 12500 6635757393291099 50000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1437/12500 : ℝ)) (X := (6635757393291099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7059/50000 : ℝ) ^ (2113/512 : ℝ) ≤ (1936572567270747/6250000000000000000 : ℝ) := by
    have hpowers : (7059/50000 : ℝ)^2113 ≤ (1936572567270747/6250000000000000000 : ℝ)^512 := by
      have hnat : (7059 : ℕ)^2113*6250000000000000000^512 ≤ 1936572567270747^512*50000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7059 50000 1936572567270747 6250000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7059/50000 : ℝ)) (X := (1936572567270747/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006635757393291099/25000000000000000000 : ℝ) ≤ (10000643098191251/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (25006635757393291099/25000000000000000000 : ℝ)^512 ≤ (10000643098191251/10000000000000000 : ℝ)^2113 := by
      have hnat : (25006635757393291099 : ℕ)^512*10000000000000000^2113 ≤ 10000643098191251^2113*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006635757393291099 25000000000000000000 10000643098191251 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000643098191251/10000000000000000 : ℝ)) (X := (25006635757393291099/25000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000885133517258283/2000000000000000000 : ℝ) ≤ (10001072201602031/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (2000885133517258283/2000000000000000000 : ℝ)^512 ≤ (10001072201602031/10000000000000000 : ℝ)^2113 := by
      have hnat : (2000885133517258283 : ℕ)^512*10000000000000000^2113 ≤ 10001072201602031^2113*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000885133517258283 2000000000000000000 10001072201602031 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001072201602031/10000000000000000 : ℝ)) (X := (2000885133517258283/2000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126936572567270747/3125000000000000000 : ℝ) ≤ (10001501305012811/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (3126936572567270747/3125000000000000000 : ℝ)^512 ≤ (10001501305012811/10000000000000000 : ℝ)^2113 := by
      have hnat : (3126936572567270747 : ℕ)^512*10000000000000000^2113 ≤ 10001501305012811^2113*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126936572567270747 3125000000000000000 10001501305012811 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001501305012811/10000000000000000 : ℝ)) (X := (3126936572567270747/3125000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6635757393291099/50000000000000000000 : ℝ) ≤ ((4368636709639467727/4370000000000000000 : ℝ)+2*(7151723513/4370000000000 : ℝ)*(1437/12500 : ℝ))^(2113/512 : ℝ) := by
    rw [show (4368636709639467727/4370000000000000000 : ℝ)+2*(7151723513/4370000000000 : ℝ)*(1437/12500 : ℝ)=(10000643098191251/10000000000000000 : ℝ) by norm_num, show 1+2*(6635757393291099/50000000000000000000 : ℝ)=(25006635757393291099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1936572567270747/6250000000000000000 : ℝ)+(6635757393291099/50000000000000000000 : ℝ) ≤ ((4368636709639467727/4370000000000000000 : ℝ)+(7151723513/4370000000000 : ℝ)*((7059/50000 : ℝ)+(1437/12500 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (4368636709639467727/4370000000000000000 : ℝ)+(7151723513/4370000000000 : ℝ)*((7059/50000 : ℝ)+(1437/12500 : ℝ))=(10001072201602031/10000000000000000 : ℝ) by norm_num, show 1+(1936572567270747/6250000000000000000 : ℝ)+(6635757393291099/50000000000000000000 : ℝ)=(2000885133517258283/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1936572567270747/6250000000000000000 : ℝ) ≤ ((4368636709639467727/4370000000000000000 : ℝ)+2*(7151723513/4370000000000 : ℝ)*(7059/50000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (4368636709639467727/4370000000000000000 : ℝ)+2*(7151723513/4370000000000 : ℝ)*(7059/50000 : ℝ)=(10001501305012811/10000000000000000 : ℝ) by norm_num, show 1+2*(1936572567270747/6250000000000000000 : ℝ)=(3126936572567270747/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4368636709639467727/4370000000000000000 : ℝ)*(X 1 0+X 2 0)+(7151723513/4370000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (4368636709639467727/4370000000000000000 : ℝ)) (alpha := (7151723513/4370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4368636709639467727/4370000000000000000 : ℝ)*(X 0 1+X 2 1)+(7151723513/4370000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (4368636709639467727/4370000000000000000 : ℝ)) (alpha := (7151723513/4370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4368636709639467727/4370000000000000000 : ℝ)*(X 0 2+X 1 2)+(7151723513/4370000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (4368636709639467727/4370000000000000000 : ℝ)) (alpha := (7151723513/4370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16893621/80000000 : ℝ)*X 0 0+(43126849/80000000 : ℝ)*X 0 1+(5267455979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344210377/10000000000 : ℝ)*X 1 0+(-434853021/2000000000 : ℝ)*X 1 1+(1316864087/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336052627/2500000000 : ℝ)*X 2 0+(5267456283/10000000000 : ℝ)*X 2 1+(-2174265017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543538877/1250000000 : ℝ)*X 0 0+(2112234589/5000000000 : ℝ)*X 0 1+(4475664351/10000000000 : ℝ)*X 0 2+(543538877/1250000000 : ℝ)*X 1 0+(2112234589/5000000000 : ℝ)*X 1 1+(4475664351/10000000000 : ℝ)*X 1 2+(543538877/1250000000 : ℝ)*X 2 0+(2112234589/5000000000 : ℝ)*X 2 1+(4475664351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105585379/500000000 : ℝ)*X 0 0+(5267767351/10000000000 : ℝ)*X 0 1+(1347635843/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312686899/10000000000 : ℝ)*X 1 0+(-2051177949/10000000000 : ℝ)*X 1 1+(1347635731/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664085861/1250000000 : ℝ)*X 2 0+(5390543023/10000000000 : ℝ)*X 2 1+(-205117783/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174159987/5000000000 : ℝ)*X 0 0+(1118757663/2500000000 : ℝ)*X 0 1+(211255281/500000000 : ℝ)*X 0 2+(2174159987/5000000000 : ℝ)*X 1 0+(1118757663/2500000000 : ℝ)*X 1 1+(211255281/500000000 : ℝ)*X 1 2+(2174159987/5000000000 : ℝ)*X 2 0+(1118757663/2500000000 : ℝ)*X 2 1+(211255281/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-38607993/10000000000 : ℝ)*X 0 0+(5911349709/10000000000 : ℝ)*X 0 1+(5911408179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60153373854262739820173271/9500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15124387/2500000000000 : ℝ)*(lower2) + (141907219/100000000000000 : ℝ)*(lower3) + (493567221/100000000000000 : ℝ)*(lower4) + (38173257/25000000000000 : ℝ)*(lower5) + (6042356295542507/100000000000000 : ℝ)*(major0) + (6042356295542507/100000000000000 : ℝ)*(major1) + (6042356295542507/100000000000000 : ℝ)*(major2) + (8103727622122783/100000000000000 : ℝ)*(sp0) + (8103744950148891/100000000000000 : ℝ)*(sp1) + (8103746615313703/100000000000000 : ℝ)*(sp2) + (1990482882353417/50000000000000 : ℝ)*(sp3) + (7311295411/50000000000000 : ℝ)*(sp4) + (416291203/25000000000000 : ℝ)*(sp5) + (2185300049/50000000000000 : ℝ)*(sp8) + (1990482882353417/50000000000000 : ℝ)*(f.failure) + (8103746615313703/100000000000000 : ℝ)*(f.sum) + (6143440187933/437000000000000000000000000 : ℝ)*base66 + (3120230258627171589/437000000000000000000000000000000 : ℝ)*base67 + (3221861281354828411/437000000000000000000000000000000 : ℝ)*base70 + (5488927181831171589/437000000000000000000000000000000 : ℝ)*base71 + (1266323328149/437000000000000000000000000 : ℝ)*base73 + (871892677055828411/437000000000000000000000000000000 : ℝ)*base76 + (4211335294758171589/437000000000000000000000000000000 : ℝ)*base77 + (2240013466037171589/437000000000000000000000000000000 : ℝ)*base79 + (554815890011/437000000000000000000000000 : ℝ)*base81 + (11302361/5000000000000000000000 : ℝ)*base90 + (11302361/5000000000000000000000 : ℝ)*base92 + (11302361/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316747563981279911412268653/54625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (803510179/100000000000000 : ℝ)*(lower2) + (36495617/6250000000000 : ℝ)*(lower3) + (812469649/100000000000000 : ℝ)*(lower4) + (192234739/50000000000000 : ℝ)*(lower5) + (3036547793116687/50000000000000 : ℝ)*(major0) + (3036547793116687/50000000000000 : ℝ)*(major1) + (3036547793116687/50000000000000 : ℝ)*(major2) + (20539992029/100000000000000 : ℝ)*(sp0) + (5584375391/50000000000000 : ℝ)*(sp3) + (8144943240667351/100000000000000 : ℝ)*(sp4) + (8144972839756701/100000000000000 : ℝ)*(sp5) + (8144972839756701/100000000000000 : ℝ)*(sp6) + (2000603485336589/50000000000000 : ℝ)*(sp7) + (9059097321/100000000000000 : ℝ)*(sp8) + (100030453485599/2500000000000 : ℝ)*(f.failure) + (8144972839756701/100000000000000 : ℝ)*(f.sum) + (194972051781/218500000000000000000000000 : ℝ)*base65 + (1780522177273160449/218500000000000000000000000000000 : ℝ)*base67 + (2265681929171339551/218500000000000000000000000000000 : ℝ)*base70 + (1060506028377160449/218500000000000000000000000000000 : ℝ)*base71 + (1496530086587/437000000000000000000000000 : ℝ)*base74 + (1845940443841660449/218500000000000000000000000000000 : ℝ)*base75 + (1330861259230660449/218500000000000000000000000000000 : ℝ)*base77 + (630833580575160449/218500000000000000000000000000000 : ℝ)*base79 + (4584212031/5462500000000000000000000 : ℝ)*base81 + (1085967/250000000000000000000 : ℝ)*base90 + (1085967/250000000000000000000 : ℝ)*base92 + (1085967/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1260_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (23/200 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1260_s8_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055852607/5000000000 : ℝ)*x 0 + (1347704829/2500000000 : ℝ)*x 1 + (658436391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055852607/5000000000 : ℝ)^8453 ≤ (2568707485437/20000000000000 : ℝ)^6405 := by
    have hnat : (1055852607 : ℕ)^8453*20000000000000^6405 ≤ 2568707485437^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055852607 5000000000 2568707485437 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347704829/2500000000 : ℝ)^8453 ≤ (8848737945359/20000000000000 : ℝ)^6405 := by
    have hnat : (1347704829 : ℕ)^8453*20000000000000^6405 ≤ 8848737945359^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347704829 2500000000 8848737945359 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658436391/1250000000 : ℝ)^8453 ≤ (42912772832101/100000000000000 : ℝ)^6405 := by
    have hnat : (658436391 : ℕ)^8453*100000000000000^6405 ≤ 42912772832101^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658436391 1250000000 42912772832101 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055852607/5000000000 : ℝ), (1347704829/2500000000 : ℝ), (658436391/1250000000 : ℝ)] ![(2568707485437/20000000000000 : ℝ), (8848737945359/20000000000000 : ℝ), (42912772832101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055852607/5000000000 : ℝ)|^8453 ≤ (2568707485437/20000000000000 : ℝ)^6405
        have hw : |(-1055852607/5000000000 : ℝ)|=(1055852607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347704829/2500000000 : ℝ)|^8453 ≤ (8848737945359/20000000000000 : ℝ)^6405
        have hw : |(1347704829/2500000000 : ℝ)|=(1347704829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658436391/1250000000 : ℝ)|^8453 ≤ (42912772832101/100000000000000 : ℝ)^6405
        have hw : |(658436391/1250000000 : ℝ)|=(658436391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s8_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344201267/10000000000 : ℝ)*x 0 + (-271778887/1250000000 : ℝ)*x 1 + (5267491129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344201267/10000000000 : ℝ)^8453 ≤ (43739446167693/100000000000000 : ℝ)^6405 := by
    have hnat : (5344201267 : ℕ)^8453*100000000000000^6405 ≤ 43739446167693^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344201267 10000000000 43739446167693 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271778887/1250000000 : ℝ)^8453 ≤ (1668472622737/12500000000000 : ℝ)^6405 := by
    have hnat : (271778887 : ℕ)^8453*12500000000000^6405 ≤ 1668472622737^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271778887 1250000000 1668472622737 12500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267491129/10000000000 : ℝ)^8453 ≤ (42912772842853/100000000000000 : ℝ)^6405 := by
    have hnat : (5267491129 : ℕ)^8453*100000000000000^6405 ≤ 42912772842853^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267491129 10000000000 42912772842853 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344201267/10000000000 : ℝ), (-271778887/1250000000 : ℝ), (5267491129/10000000000 : ℝ)] ![(43739446167693/100000000000000 : ℝ), (1668472622737/12500000000000 : ℝ), (42912772842853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344201267/10000000000 : ℝ)|^8453 ≤ (43739446167693/100000000000000 : ℝ)^6405
        have hw : |(5344201267/10000000000 : ℝ)|=(5344201267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271778887/1250000000 : ℝ)|^8453 ≤ (1668472622737/12500000000000 : ℝ)^6405
        have hw : |(-271778887/1250000000 : ℝ)|=(271778887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267491129/10000000000 : ℝ)|^8453 ≤ (42912772842853/100000000000000 : ℝ)^6405
        have hw : |(5267491129/10000000000 : ℝ)|=(5267491129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s8_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334012579/625000000 : ℝ)*x 0 + (1316872781/2500000000 : ℝ)*x 1 + (-1087115553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334012579/625000000 : ℝ)^8453 ≤ (5467430766911/12500000000000 : ℝ)^6405 := by
    have hnat : (334012579 : ℕ)^8453*12500000000000^6405 ≤ 5467430766911^6405*625000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334012579 625000000 5467430766911 12500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316872781/2500000000 : ℝ)^8453 ≤ (8582554557819/20000000000000 : ℝ)^6405 := by
    have hnat : (1316872781 : ℕ)^8453*20000000000000^6405 ≤ 8582554557819^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316872781 2500000000 8582554557819 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087115553/5000000000 : ℝ)^8453 ≤ (13347781062917/100000000000000 : ℝ)^6405 := by
    have hnat : (1087115553 : ℕ)^8453*100000000000000^6405 ≤ 13347781062917^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087115553 5000000000 13347781062917 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334012579/625000000 : ℝ), (1316872781/2500000000 : ℝ), (-1087115553/5000000000 : ℝ)] ![(5467430766911/12500000000000 : ℝ), (8582554557819/20000000000000 : ℝ), (13347781062917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334012579/625000000 : ℝ)|^8453 ≤ (5467430766911/12500000000000 : ℝ)^6405
        have hw : |(334012579/625000000 : ℝ)|=(334012579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316872781/2500000000 : ℝ)|^8453 ≤ (8582554557819/20000000000000 : ℝ)^6405
        have hw : |(1316872781/2500000000 : ℝ)|=(1316872781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087115553/5000000000 : ℝ)|^8453 ≤ (13347781062917/100000000000000 : ℝ)^6405
        have hw : |(-1087115553/5000000000 : ℝ)|=(1087115553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s8_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543539057/1250000000 : ℝ)*x 0 + (4224541847/10000000000 : ℝ)*x 1 + (2237795793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543539057/1250000000 : ℝ)^8453 ≤ (8329400399739/25000000000000 : ℝ)^6405 := by
    have hnat : (543539057 : ℕ)^8453*25000000000000^6405 ≤ 8329400399739^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543539057 1250000000 8329400399739 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224541847/10000000000 : ℝ)^8453 ≤ (1603587196719/5000000000000 : ℝ)^6405 := by
    have hnat : (4224541847 : ℕ)^8453*5000000000000^6405 ≤ 1603587196719^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224541847 10000000000 1603587196719 5000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237795793/5000000000 : ℝ)^8453 ≤ (34610654461207/100000000000000 : ℝ)^6405 := by
    have hnat : (2237795793 : ℕ)^8453*100000000000000^6405 ≤ 34610654461207^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237795793 5000000000 34610654461207 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543539057/1250000000 : ℝ), (4224541847/10000000000 : ℝ), (2237795793/5000000000 : ℝ)] ![(8329400399739/25000000000000 : ℝ), (1603587196719/5000000000000 : ℝ), (34610654461207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543539057/1250000000 : ℝ)|^8453 ≤ (8329400399739/25000000000000 : ℝ)^6405
        have hw : |(543539057/1250000000 : ℝ)|=(543539057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224541847/10000000000 : ℝ)|^8453 ≤ (1603587196719/5000000000000 : ℝ)^6405
        have hw : |(4224541847/10000000000 : ℝ)|=(4224541847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237795793/5000000000 : ℝ)|^8453 ≤ (34610654461207/100000000000000 : ℝ)^6405
        have hw : |(2237795793/5000000000 : ℝ)|=(2237795793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s8_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211170967/1000000000 : ℝ)*x 0 + (5267802277/10000000000 : ℝ)*x 1 + (5390507153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211170967/1000000000 : ℝ)^8453 ≤ (802723324667/6250000000000 : ℝ)^6405 := by
    have hnat : (211170967 : ℕ)^8453*6250000000000^6405 ≤ 802723324667^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211170967 1000000000 802723324667 6250000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267802277/10000000000 : ℝ)^8453 ≤ (21458059112037/50000000000000 : ℝ)^6405 := by
    have hnat : (5267802277 : ℕ)^8453*50000000000000^6405 ≤ 21458059112037^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267802277 10000000000 21458059112037 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390507153/10000000000 : ℝ)^8453 ≤ (44240308566953/100000000000000 : ℝ)^6405 := by
    have hnat : (5390507153 : ℕ)^8453*100000000000000^6405 ≤ 44240308566953^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390507153 10000000000 44240308566953 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211170967/1000000000 : ℝ), (5267802277/10000000000 : ℝ), (5390507153/10000000000 : ℝ)] ![(802723324667/6250000000000 : ℝ), (21458059112037/50000000000000 : ℝ), (44240308566953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211170967/1000000000 : ℝ)|^8453 ≤ (802723324667/6250000000000 : ℝ)^6405
        have hw : |(-211170967/1000000000 : ℝ)|=(211170967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267802277/10000000000 : ℝ)|^8453 ≤ (21458059112037/50000000000000 : ℝ)^6405
        have hw : |(5267802277/10000000000 : ℝ)|=(5267802277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390507153/10000000000 : ℝ)|^8453 ≤ (44240308566953/100000000000000 : ℝ)^6405
        have hw : |(5390507153/10000000000 : ℝ)|=(5390507153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s8_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328173827/2500000000 : ℝ)*x 0 + (-2051215183/10000000000 : ℝ)*x 1 + (336906701/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328173827/2500000000 : ℝ)^8453 ≤ (10849864297239/25000000000000 : ℝ)^6405 := by
    have hnat : (1328173827 : ℕ)^8453*25000000000000^6405 ≤ 10849864297239^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328173827 2500000000 10849864297239 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051215183/10000000000 : ℝ)^8453 ≤ (12360233540161/100000000000000 : ℝ)^6405 := by
    have hnat : (2051215183 : ℕ)^8453*100000000000000^6405 ≤ 12360233540161^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051215183 10000000000 12360233540161 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336906701/625000000 : ℝ)^8453 ≤ (1769612369973/4000000000000 : ℝ)^6405 := by
    have hnat : (336906701 : ℕ)^8453*4000000000000^6405 ≤ 1769612369973^6405*625000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336906701 625000000 1769612369973 4000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328173827/2500000000 : ℝ), (-2051215183/10000000000 : ℝ), (336906701/625000000 : ℝ)] ![(10849864297239/25000000000000 : ℝ), (12360233540161/100000000000000 : ℝ), (1769612369973/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328173827/2500000000 : ℝ)|^8453 ≤ (10849864297239/25000000000000 : ℝ)^6405
        have hw : |(1328173827/2500000000 : ℝ)|=(1328173827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051215183/10000000000 : ℝ)|^8453 ≤ (12360233540161/100000000000000 : ℝ)^6405
        have hw : |(-2051215183/10000000000 : ℝ)|=(2051215183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336906701/625000000 : ℝ)|^8453 ≤ (1769612369973/4000000000000 : ℝ)^6405
        have hw : |(336906701/625000000 : ℝ)|=(336906701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s8_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062539037/2000000000 : ℝ)*x 0 + (1347626849/2500000000 : ℝ)*x 1 + (-1025607553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062539037/2000000000 : ℝ)^8453 ≤ (43399455862887/100000000000000 : ℝ)^6405 := by
    have hnat : (1062539037 : ℕ)^8453*100000000000000^6405 ≤ 43399455862887^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062539037 2000000000 43399455862887 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347626849/2500000000 : ℝ)^8453 ≤ (44240311198957/100000000000000 : ℝ)^6405 := by
    have hnat : (1347626849 : ℕ)^8453*100000000000000^6405 ≤ 44240311198957^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347626849 2500000000 44240311198957 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025607553/5000000000 : ℝ)^8453 ≤ (12360232927813/100000000000000 : ℝ)^6405 := by
    have hnat : (1025607553 : ℕ)^8453*100000000000000^6405 ≤ 12360232927813^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025607553 5000000000 12360232927813 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062539037/2000000000 : ℝ), (1347626849/2500000000 : ℝ), (-1025607553/5000000000 : ℝ)] ![(43399455862887/100000000000000 : ℝ), (44240311198957/100000000000000 : ℝ), (12360232927813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062539037/2000000000 : ℝ)|^8453 ≤ (43399455862887/100000000000000 : ℝ)^6405
        have hw : |(1062539037/2000000000 : ℝ)|=(1062539037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347626849/2500000000 : ℝ)|^8453 ≤ (44240311198957/100000000000000 : ℝ)^6405
        have hw : |(1347626849/2500000000 : ℝ)|=(1347626849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025607553/5000000000 : ℝ)|^8453 ≤ (12360232927813/100000000000000 : ℝ)^6405
        have hw : |(-1025607553/5000000000 : ℝ)|=(1025607553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s8_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543540223/1250000000 : ℝ)*x 0 + (4474958433/10000000000 : ℝ)*x 1 + (84503547/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543540223/1250000000 : ℝ)^8453 ≤ (8329423981347/25000000000000 : ℝ)^6405 := by
    have hnat : (543540223 : ℕ)^8453*25000000000000^6405 ≤ 8329423981347^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543540223 1250000000 8329423981347 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474958433/10000000000 : ℝ)^8453 ≤ (34604192714297/100000000000000 : ℝ)^6405 := by
    have hnat : (4474958433 : ℕ)^8453*100000000000000^6405 ≤ 34604192714297^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474958433 10000000000 34604192714297 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84503547/200000000 : ℝ)^8453 ≤ (8019527835833/25000000000000 : ℝ)^6405 := by
    have hnat : (84503547 : ℕ)^8453*25000000000000^6405 ≤ 8019527835833^6405*200000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84503547 200000000 8019527835833 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543540223/1250000000 : ℝ), (4474958433/10000000000 : ℝ), (84503547/200000000 : ℝ)] ![(8329423981347/25000000000000 : ℝ), (34604192714297/100000000000000 : ℝ), (8019527835833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543540223/1250000000 : ℝ)|^8453 ≤ (8329423981347/25000000000000 : ℝ)^6405
        have hw : |(543540223/1250000000 : ℝ)|=(543540223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474958433/10000000000 : ℝ)|^8453 ≤ (34604192714297/100000000000000 : ℝ)^6405
        have hw : |(4474958433/10000000000 : ℝ)|=(4474958433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84503547/200000000 : ℝ)|^8453 ≤ (8019527835833/25000000000000 : ℝ)^6405
        have hw : |(84503547/200000000 : ℝ)|=(84503547/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/200 : ℝ)*pair X i i ≤ pair X i h) :
    (11501/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14113/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (23/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (23/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (23/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (23/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (23/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (23/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (23/200 : ℝ) ^ (2113/512 : ℝ) ≤ (1661322817466173/12500000000000000000 : ℝ) := by
    have hpowers : (23/200 : ℝ)^2113 ≤ (1661322817466173/12500000000000000000 : ℝ)^512 := by
      have hnat : (23 : ℕ)^2113*12500000000000000000^512 ≤ 1661322817466173^512*200^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23 200 1661322817466173 12500000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23/200 : ℝ)) (X := (1661322817466173/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (2113/512 : ℝ) ≤ (3868618371766209/12500000000000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^2113 ≤ (3868618371766209/12500000000000000000 : ℝ)^512 := by
      have hnat : (7057 : ℕ)^2113*12500000000000000000^512 ≤ 3868618371766209^512*50000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 3868618371766209 12500000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (3868618371766209/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251661322817466173/6250000000000000000 : ℝ) ≤ (10000644022064913/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (6251661322817466173/6250000000000000000 : ℝ)^512 ≤ (10000644022064913/10000000000000000 : ℝ)^2113 := by
      have hnat : (6251661322817466173 : ℕ)^512*10000000000000000^2113 ≤ 10000644022064913^2113*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251661322817466173 6250000000000000000 10000644022064913 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000644022064913/10000000000000000 : ℝ)) (X := (6251661322817466173/6250000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252764970594616191/6250000000000000000 : ℝ) ≤ (5000535893134461/5000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (6252764970594616191/6250000000000000000 : ℝ)^512 ≤ (5000535893134461/5000000000000000 : ℝ)^2113 := by
      have hnat : (6252764970594616191 : ℕ)^512*5000000000000000^2113 ≤ 5000535893134461^2113*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252764970594616191 6250000000000000000 5000535893134461 5000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000535893134461/5000000000000000 : ℝ)) (X := (6252764970594616191/6250000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253868618371766209/6250000000000000000 : ℝ) ≤ (10001499550472931/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (6253868618371766209/6250000000000000000 : ℝ)^512 ≤ (10001499550472931/10000000000000000 : ℝ)^2113 := by
      have hnat : (6253868618371766209 : ℕ)^512*10000000000000000^2113 ≤ 10001499550472931^2113*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253868618371766209 6250000000000000000 10001499550472931 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001499550472931/10000000000000000 : ℝ)) (X := (6253868618371766209/6250000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1661322817466173/12500000000000000000 : ℝ) ≤ ((13065922448492737791/13070000000000000000 : ℝ)+2*(427764204009/261400000000000 : ℝ)*(23/200 : ℝ))^(2113/512 : ℝ) := by
    rw [show (13065922448492737791/13070000000000000000 : ℝ)+2*(427764204009/261400000000000 : ℝ)*(23/200 : ℝ)=(10000644022064913/10000000000000000 : ℝ) by norm_num, show 1+2*(1661322817466173/12500000000000000000 : ℝ)=(6251661322817466173/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3868618371766209/12500000000000000000 : ℝ)+(1661322817466173/12500000000000000000 : ℝ) ≤ ((13065922448492737791/13070000000000000000 : ℝ)+(427764204009/261400000000000 : ℝ)*((7057/50000 : ℝ)+(23/200 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (13065922448492737791/13070000000000000000 : ℝ)+(427764204009/261400000000000 : ℝ)*((7057/50000 : ℝ)+(23/200 : ℝ))=(5000535893134461/5000000000000000 : ℝ) by norm_num, show 1+(3868618371766209/12500000000000000000 : ℝ)+(1661322817466173/12500000000000000000 : ℝ)=(6252764970594616191/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3868618371766209/12500000000000000000 : ℝ) ≤ ((13065922448492737791/13070000000000000000 : ℝ)+2*(427764204009/261400000000000 : ℝ)*(7057/50000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (13065922448492737791/13070000000000000000 : ℝ)+2*(427764204009/261400000000000 : ℝ)*(7057/50000 : ℝ)=(10001499550472931/10000000000000000 : ℝ) by norm_num, show 1+2*(3868618371766209/12500000000000000000 : ℝ)=(6253868618371766209/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13065922448492737791/13070000000000000000 : ℝ)*(X 1 0+X 2 0)+(427764204009/261400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (23/200 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (13065922448492737791/13070000000000000000 : ℝ)) (alpha := (427764204009/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13065922448492737791/13070000000000000000 : ℝ)*(X 0 1+X 2 1)+(427764204009/261400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (23/200 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (13065922448492737791/13070000000000000000 : ℝ)) (alpha := (427764204009/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13065922448492737791/13070000000000000000 : ℝ)*(X 0 2+X 1 2)+(427764204009/261400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (23/200 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (13065922448492737791/13070000000000000000 : ℝ)) (alpha := (427764204009/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1055852607/5000000000 : ℝ)*X 0 0+(1347704829/2500000000 : ℝ)*X 0 1+(658436391/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344201267/10000000000 : ℝ)*X 1 0+(-271778887/1250000000 : ℝ)*X 1 1+(5267491129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334012579/625000000 : ℝ)*X 2 0+(1316872781/2500000000 : ℝ)*X 2 1+(-1087115553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543539057/1250000000 : ℝ)*X 0 0+(4224541847/10000000000 : ℝ)*X 0 1+(2237795793/5000000000 : ℝ)*X 0 2+(543539057/1250000000 : ℝ)*X 1 0+(4224541847/10000000000 : ℝ)*X 1 1+(2237795793/5000000000 : ℝ)*X 1 2+(543539057/1250000000 : ℝ)*X 2 0+(4224541847/10000000000 : ℝ)*X 2 1+(2237795793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-211170967/1000000000 : ℝ)*X 0 0+(5267802277/10000000000 : ℝ)*X 0 1+(5390507153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328173827/2500000000 : ℝ)*X 1 0+(-2051215183/10000000000 : ℝ)*X 1 1+(336906701/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062539037/2000000000 : ℝ)*X 2 0+(1347626849/2500000000 : ℝ)*X 2 1+(-1025607553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543540223/1250000000 : ℝ)*X 0 0+(4474958433/10000000000 : ℝ)*X 0 1+(84503547/200000000 : ℝ)*X 0 2+(543540223/1250000000 : ℝ)*X 1 0+(4474958433/10000000000 : ℝ)*X 1 1+(84503547/200000000 : ℝ)*X 1 2+(543540223/1250000000 : ℝ)*X 2 0+(4474958433/10000000000 : ℝ)*X 2 1+(84503547/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89742331185113285760465633/40843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (428629863/100000000000000 : ℝ)*(base19) + (379226569/100000000000000 : ℝ)*(base23) + (11984787/50000000000000 : ℝ)*(lower2) + (34740311/50000000000000 : ℝ)*(upper3) + (75199/400000000000 : ℝ)*(upper5) + (755734760973629/12500000000000 : ℝ)*(major0) + (755734760973629/12500000000000 : ℝ)*(major1) + (755734760973629/12500000000000 : ℝ)*(major2) + (4054229560511667/50000000000000 : ℝ)*(sp0) + (8108469599890101/100000000000000 : ℝ)*(sp1) + (2027117412323349/25000000000000 : ℝ)*(sp2) + (1991639794791989/50000000000000 : ℝ)*(sp3) + (10907496631/100000000000000 : ℝ)*(sp4) + (6484233753/100000000000000 : ℝ)*(sp7) + (398328607381773/10000000000000 : ℝ)*(f.failure) + (1621694005703993/20000000000000 : ℝ)*(f.sum) + (7955624434473/3267500000000000000000000000 : ℝ)*base66 + (1033995097981986461/163375000000000000000000000000000 : ℝ)*base68 + (718018599824388539/163375000000000000000000000000000 : ℝ)*base69 + (1244874002882138539/163375000000000000000000000000000 : ℝ)*base71 + (26502625609021/6535000000000000000000000000 : ℝ)*base74 + (1447074352782138539/163375000000000000000000000000000 : ℝ)*base75 + (789859176364763539/163375000000000000000000000000000 : ℝ)*base77 + (1165641991229138539/163375000000000000000000000000000 : ℝ)*base79 + (9393022543613/3267500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (469091/1000000000000000000000 : ℝ)*base89 + (469091/1000000000000000000000 : ℝ)*base91 + (469091/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (432084213056263634784061323/81687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26365949/100000000000000 : ℝ)*(base8) + (5673689/20000000000000 : ℝ)*(lower2) + (16388813/25000000000000 : ℝ)*(upper3) + (99606069/100000000000000 : ℝ)*(lower4) + (7235559/20000000000000 : ℝ)*(upper5) + (1519142072408349/25000000000000 : ℝ)*(major0) + (1519142072408349/25000000000000 : ℝ)*(major1) + (1519142072408349/25000000000000 : ℝ)*(major2) + (9205471029/100000000000000 : ℝ)*(sp2) + (301746073/50000000000000 : ℝ)*(sp3) + (4074815134953039/50000000000000 : ℝ)*(sp4) + (4074815148136013/50000000000000 : ℝ)*(sp5) + (8149621090800997/100000000000000 : ℝ)*(sp6) + (2001752751593343/50000000000000 : ℝ)*(sp7) + (250219131667427/6250000000000 : ℝ)*(f.failure) + (4074815148136013/50000000000000 : ℝ)*(f.sum) + (47178589543691/3267500000000000000000000000 : ℝ)*base65 + (1990248545492232941/326750000000000000000000000000000 : ℝ)*base68 + (8595136192960767059/326750000000000000000000000000000 : ℝ)*base69 + (4289626328179267059/326750000000000000000000000000000 : ℝ)*base71 + (1117313368043/408437500000000000000000000 : ℝ)*base74 + (2074917159867267059/326750000000000000000000000000000 : ℝ)*base75 + (685434602291517059/326750000000000000000000000000000 : ℝ)*base77 + (2216729327454267059/326750000000000000000000000000000 : ℝ)*base79 + (10434268700391/3267500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (947309/625000000000000000000 : ℝ)*base89 + (947309/625000000000000000000 : ℝ)*base91 + (947309/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1260_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/200 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1260_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1260_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1260_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1260_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1260_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
