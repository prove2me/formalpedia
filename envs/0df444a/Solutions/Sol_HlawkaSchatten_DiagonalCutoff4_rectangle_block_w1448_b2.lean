-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1448_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:53.507979+00:00
-- url     : https://prove2.me/submissions/16cbca54-3456-46c1-935b-ac9ab291c1aa

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
theorem support_rectangle_w1448_s6_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955817153/10000000000 : ℝ)*x 0 + (2703622083/5000000000 : ℝ)*x 1 + (5247311449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955817153/10000000000 : ℝ)^551 ≤ (5968344024711/50000000000000 : ℝ)^423 := by
    have hnat : (1955817153 : ℕ)^551*50000000000000^423 ≤ 5968344024711^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955817153 10000000000 5968344024711 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703622083/5000000000 : ℝ)^551 ≤ (44892561497657/100000000000000 : ℝ)^423 := by
    have hnat : (2703622083 : ℕ)^551*100000000000000^423 ≤ 44892561497657^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703622083 5000000000 44892561497657 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247311449/10000000000 : ℝ)^551 ≤ (1349085951219/3125000000000 : ℝ)^423 := by
    have hnat : (5247311449 : ℕ)^551*3125000000000^423 ≤ 1349085951219^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247311449 10000000000 1349085951219 3125000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955817153/10000000000 : ℝ), (2703622083/5000000000 : ℝ), (5247311449/10000000000 : ℝ)] ![(5968344024711/50000000000000 : ℝ), (44892561497657/100000000000000 : ℝ), (1349085951219/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955817153/10000000000 : ℝ)|^551 ≤ (5968344024711/50000000000000 : ℝ)^423
        have hw : |(-1955817153/10000000000 : ℝ)|=(1955817153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703622083/5000000000 : ℝ)|^551 ≤ (44892561497657/100000000000000 : ℝ)^423
        have hw : |(2703622083/5000000000 : ℝ)|=(2703622083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247311449/10000000000 : ℝ)|^551 ≤ (1349085951219/3125000000000 : ℝ)^423
        have hw : |(5247311449/10000000000 : ℝ)|=(5247311449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s6_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668365189/1250000000 : ℝ)*x 0 + (-40744579/200000000 : ℝ)*x 1 + (5247311393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668365189/1250000000 : ℝ)^551 ≤ (44241301349103/100000000000000 : ℝ)^423 := by
    have hnat : (668365189 : ℕ)^551*100000000000000^423 ≤ 44241301349103^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668365189 1250000000 44241301349103 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40744579/200000000 : ℝ)^551 ≤ (6293974398383/50000000000000 : ℝ)^423 := by
    have hnat : (40744579 : ℕ)^551*50000000000000^423 ≤ 6293974398383^423*200000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40744579 200000000 6293974398383 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247311393/10000000000 : ℝ)^551 ≤ (43170749838869/100000000000000 : ℝ)^423 := by
    have hnat : (5247311393 : ℕ)^551*100000000000000^423 ≤ 43170749838869^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247311393 10000000000 43170749838869 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668365189/1250000000 : ℝ), (-40744579/200000000 : ℝ), (5247311393/10000000000 : ℝ)] ![(44241301349103/100000000000000 : ℝ), (6293974398383/50000000000000 : ℝ), (43170749838869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668365189/1250000000 : ℝ)|^551 ≤ (44241301349103/100000000000000 : ℝ)^423
        have hw : |(668365189/1250000000 : ℝ)|=(668365189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40744579/200000000 : ℝ)|^551 ≤ (6293974398383/50000000000000 : ℝ)^423
        have hw : |(-40744579/200000000 : ℝ)|=(40744579/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247311393/10000000000 : ℝ)|^551 ≤ (43170749838869/100000000000000 : ℝ)^423
        have hw : |(5247311393/10000000000 : ℝ)|=(5247311393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s6_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2673460811/5000000000 : ℝ)*x 0 + (262365561/500000000 : ℝ)*x 1 + (-1018614517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673460811/5000000000 : ℝ)^551 ≤ (11060325633669/25000000000000 : ℝ)^423 := by
    have hnat : (2673460811 : ℕ)^551*25000000000000^423 ≤ 11060325633669^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673460811 5000000000 11060325633669 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262365561/500000000 : ℝ)^551 ≤ (43170747984867/100000000000000 : ℝ)^423 := by
    have hnat : (262365561 : ℕ)^551*100000000000000^423 ≤ 43170747984867^423*500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262365561 500000000 43170747984867 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018614517/5000000000 : ℝ)^551 ≤ (6293974736429/50000000000000 : ℝ)^423 := by
    have hnat : (1018614517 : ℕ)^551*50000000000000^423 ≤ 6293974736429^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018614517 5000000000 6293974736429 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673460811/5000000000 : ℝ), (262365561/500000000 : ℝ), (-1018614517/5000000000 : ℝ)] ![(11060325633669/25000000000000 : ℝ), (43170747984867/100000000000000 : ℝ), (6293974736429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673460811/5000000000 : ℝ)|^551 ≤ (11060325633669/25000000000000 : ℝ)^423
        have hw : |(2673460811/5000000000 : ℝ)|=(2673460811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262365561/500000000 : ℝ)|^551 ≤ (43170747984867/100000000000000 : ℝ)^423
        have hw : |(262365561/500000000 : ℝ)|=(262365561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1018614517/5000000000 : ℝ)|^551 ≤ (6293974736429/50000000000000 : ℝ)^423
        have hw : |(-1018614517/5000000000 : ℝ)|=(1018614517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s6_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2149822337/5000000000 : ℝ)*x 0 + (4128593947/10000000000 : ℝ)*x 1 + (2238496017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149822337/5000000000 : ℝ)^551 ≤ (33304973157601/100000000000000 : ℝ)^423 := by
    have hnat : (2149822337 : ℕ)^551*100000000000000^423 ≤ 33304973157601^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149822337 5000000000 33304973157601 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128593947/10000000000 : ℝ)^551 ≤ (15794785460311/50000000000000 : ℝ)^423 := by
    have hnat : (4128593947 : ℕ)^551*50000000000000^423 ≤ 15794785460311^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128593947 10000000000 15794785460311 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238496017/5000000000 : ℝ)^551 ≤ (17552727955429/50000000000000 : ℝ)^423 := by
    have hnat : (2238496017 : ℕ)^551*50000000000000^423 ≤ 17552727955429^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238496017 5000000000 17552727955429 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149822337/5000000000 : ℝ), (4128593947/10000000000 : ℝ), (2238496017/5000000000 : ℝ)] ![(33304973157601/100000000000000 : ℝ), (15794785460311/50000000000000 : ℝ), (17552727955429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149822337/5000000000 : ℝ)|^551 ≤ (33304973157601/100000000000000 : ℝ)^423
        have hw : |(2149822337/5000000000 : ℝ)|=(2149822337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128593947/10000000000 : ℝ)|^551 ≤ (15794785460311/50000000000000 : ℝ)^423
        have hw : |(4128593947/10000000000 : ℝ)|=(4128593947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238496017/5000000000 : ℝ)|^551 ≤ (17552727955429/50000000000000 : ℝ)^423
        have hw : |(2238496017/5000000000 : ℝ)|=(2238496017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s6_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-122239281/625000000 : ℝ)*x 0 + (2623944439/5000000000 : ℝ)*x 1 + (2703331801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122239281/625000000 : ℝ)^551 ≤ (746048639143/6250000000000 : ℝ)^423 := by
    have hnat : (122239281 : ℕ)^551*6250000000000^423 ≤ 746048639143^423*625000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122239281 625000000 746048639143 6250000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623944439/5000000000 : ℝ)^551 ≤ (21588469358461/50000000000000 : ℝ)^423 := by
    have hnat : (2623944439 : ℕ)^551*50000000000000^423 ≤ 21588469358461^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623944439 5000000000 21588469358461 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703331801/5000000000 : ℝ)^551 ≤ (44886283044129/100000000000000 : ℝ)^423 := by
    have hnat : (2703331801 : ℕ)^551*100000000000000^423 ≤ 44886283044129^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703331801 5000000000 44886283044129 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122239281/625000000 : ℝ), (2623944439/5000000000 : ℝ), (2703331801/5000000000 : ℝ)] ![(746048639143/6250000000000 : ℝ), (21588469358461/50000000000000 : ℝ), (44886283044129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122239281/625000000 : ℝ)|^551 ≤ (746048639143/6250000000000 : ℝ)^423
        have hw : |(-122239281/625000000 : ℝ)|=(122239281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623944439/5000000000 : ℝ)|^551 ≤ (21588469358461/50000000000000 : ℝ)^423
        have hw : |(2623944439/5000000000 : ℝ)|=(2623944439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703331801/5000000000 : ℝ)|^551 ≤ (44886283044129/100000000000000 : ℝ)^423
        have hw : |(2703331801/5000000000 : ℝ)|=(2703331801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s6_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305267379/10000000000 : ℝ)*x 0 + (-75115067/400000000 : ℝ)*x 1 + (5406663407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305267379/10000000000 : ℝ)^551 ≤ (21896443092903/50000000000000 : ℝ)^423 := by
    have hnat : (5305267379 : ℕ)^551*50000000000000^423 ≤ 21896443092903^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305267379 10000000000 21896443092903 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75115067/400000000 : ℝ)^551 ≤ (5660416434243/50000000000000 : ℝ)^423 := by
    have hnat : (75115067 : ℕ)^551*50000000000000^423 ≤ 5660416434243^423*400000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75115067 400000000 5660416434243 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406663407/10000000000 : ℝ)^551 ≤ (22443140467677/50000000000000 : ℝ)^423 := by
    have hnat : (5406663407 : ℕ)^551*50000000000000^423 ≤ 22443140467677^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406663407 10000000000 22443140467677 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305267379/10000000000 : ℝ), (-75115067/400000000 : ℝ), (5406663407/10000000000 : ℝ)] ![(21896443092903/50000000000000 : ℝ), (5660416434243/50000000000000 : ℝ), (22443140467677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305267379/10000000000 : ℝ)|^551 ≤ (21896443092903/50000000000000 : ℝ)^423
        have hw : |(5305267379/10000000000 : ℝ)|=(5305267379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75115067/400000000 : ℝ)|^551 ≤ (5660416434243/50000000000000 : ℝ)^423
        have hw : |(-75115067/400000000 : ℝ)|=(75115067/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406663407/10000000000 : ℝ)|^551 ≤ (22443140467677/50000000000000 : ℝ)^423
        have hw : |(5406663407/10000000000 : ℝ)|=(5406663407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s6_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305267913/10000000000 : ℝ)*x 0 + (2703331333/5000000000 : ℝ)*x 1 + (-469469241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305267913/10000000000 : ℝ)^551 ≤ (8758578385523/20000000000000 : ℝ)^423 := by
    have hnat : (5305267913 : ℕ)^551*20000000000000^423 ≤ 8758578385523^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305267913 10000000000 8758578385523 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703331333/5000000000 : ℝ)^551 ≤ (11221568230503/25000000000000 : ℝ)^423 := by
    have hnat : (2703331333 : ℕ)^551*25000000000000^423 ≤ 11221568230503^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703331333 5000000000 11221568230503 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469469241/2500000000 : ℝ)^551 ≤ (5660417568967/50000000000000 : ℝ)^423 := by
    have hnat : (469469241 : ℕ)^551*50000000000000^423 ≤ 5660417568967^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469469241 2500000000 5660417568967 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305267913/10000000000 : ℝ), (2703331333/5000000000 : ℝ), (-469469241/2500000000 : ℝ)] ![(8758578385523/20000000000000 : ℝ), (11221568230503/25000000000000 : ℝ), (5660417568967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305267913/10000000000 : ℝ)|^551 ≤ (8758578385523/20000000000000 : ℝ)^423
        have hw : |(5305267913/10000000000 : ℝ)|=(5305267913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703331333/5000000000 : ℝ)|^551 ≤ (11221568230503/25000000000000 : ℝ)^423
        have hw : |(2703331333/5000000000 : ℝ)|=(2703331333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-469469241/2500000000 : ℝ)|^551 ≤ (5660417568967/50000000000000 : ℝ)^423
        have hw : |(-469469241/2500000000 : ℝ)|=(469469241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s6_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2149834653/5000000000 : ℝ)*x 0 + (895146593/2000000000 : ℝ)*x 1 + (4129859213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149834653/5000000000 : ℝ)^551 ≤ (33305221692743/100000000000000 : ℝ)^423 := by
    have hnat : (2149834653 : ℕ)^551*100000000000000^423 ≤ 33305221692743^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149834653 5000000000 33305221692743 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895146593/2000000000 : ℝ)^551 ≤ (17546298109273/50000000000000 : ℝ)^423 := by
    have hnat : (895146593 : ℕ)^551*50000000000000^423 ≤ 17546298109273^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895146593 2000000000 17546298109273 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4129859213/10000000000 : ℝ)^551 ≤ (15801091036313/50000000000000 : ℝ)^423 := by
    have hnat : (4129859213 : ℕ)^551*50000000000000^423 ≤ 15801091036313^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129859213 10000000000 15801091036313 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149834653/5000000000 : ℝ), (895146593/2000000000 : ℝ), (4129859213/10000000000 : ℝ)] ![(33305221692743/100000000000000 : ℝ), (17546298109273/50000000000000 : ℝ), (15801091036313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149834653/5000000000 : ℝ)|^551 ≤ (33305221692743/100000000000000 : ℝ)^423
        have hw : |(2149834653/5000000000 : ℝ)|=(2149834653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895146593/2000000000 : ℝ)|^551 ≤ (17546298109273/50000000000000 : ℝ)^423
        have hw : |(895146593/2000000000 : ℝ)|=(895146593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4129859213/10000000000 : ℝ)|^551 ≤ (15801091036313/50000000000000 : ℝ)^423
        have hw : |(4129859213/10000000000 : ℝ)|=(4129859213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    (5689/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/800 : ℝ) ^ (4407/1024 : ℝ) ≤ (8651426800598451/100000000000000000000 : ℝ) := by
    have hpowers : (91/800 : ℝ)^4407 ≤ (8651426800598451/100000000000000000000 : ℝ)^1024 := by
      have hnat : (91 : ℕ)^4407*100000000000000000000^1024 ≤ 8651426800598451^1024*800^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 800 8651426800598451 100000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/800 : ℝ)) (X := (8651426800598451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (4407/1024 : ℝ) ≤ (26622801420639677/100000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^4407 ≤ (26622801420639677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1477 : ℕ)^4407*100000000000000000000^1024 ≤ 26622801420639677^1024*10000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 26622801420639677 100000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (26622801420639677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008651426800598451/50000000000000000000 : ℝ) ≤ (10000402018277997/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50008651426800598451/50000000000000000000 : ℝ)^1024 ≤ (10000402018277997/10000000000000000 : ℝ)^4407 := by
      have hnat : (50008651426800598451 : ℕ)^1024*10000000000000000^4407 ≤ 10000402018277997^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008651426800598451 50000000000000000000 10000402018277997 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000402018277997/10000000000000000 : ℝ)) (X := (50008651426800598451/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252204639263827383/6250000000000000000 : ℝ) ≤ (5000409756300427/5000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (6252204639263827383/6250000000000000000 : ℝ)^1024 ≤ (5000409756300427/5000000000000000 : ℝ)^4407 := by
      have hnat : (6252204639263827383 : ℕ)^1024*5000000000000000^4407 ≤ 5000409756300427^4407*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252204639263827383 6250000000000000000 5000409756300427 5000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000409756300427/5000000000000000 : ℝ)) (X := (6252204639263827383/6250000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026622801420639677/50000000000000000000 : ℝ) ≤ (10001237006923711/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50026622801420639677/50000000000000000000 : ℝ)^1024 ≤ (10001237006923711/10000000000000000 : ℝ)^4407 := by
      have hnat : (50026622801420639677 : ℕ)^1024*10000000000000000^4407 ≤ 10001237006923711^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026622801420639677 50000000000000000000 10001237006923711 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001237006923711/10000000000000000 : ℝ)) (X := (50026622801420639677/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8651426800598451/100000000000000000000 : ℝ) ≤ ((969767624463108659/970000000000000000 : ℝ)+2*(417494322857/339500000000000 : ℝ)*(91/800 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (969767624463108659/970000000000000000 : ℝ)+2*(417494322857/339500000000000 : ℝ)*(91/800 : ℝ)=(10000402018277997/10000000000000000 : ℝ) by norm_num, show 1+2*(8651426800598451/100000000000000000000 : ℝ)=(50008651426800598451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26622801420639677/100000000000000000000 : ℝ)+(8651426800598451/100000000000000000000 : ℝ) ≤ ((969767624463108659/970000000000000000 : ℝ)+(417494322857/339500000000000 : ℝ)*((1477/10000 : ℝ)+(91/800 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (969767624463108659/970000000000000000 : ℝ)+(417494322857/339500000000000 : ℝ)*((1477/10000 : ℝ)+(91/800 : ℝ))=(5000409756300427/5000000000000000 : ℝ) by norm_num, show 1+(26622801420639677/100000000000000000000 : ℝ)+(8651426800598451/100000000000000000000 : ℝ)=(6252204639263827383/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26622801420639677/100000000000000000000 : ℝ) ≤ ((969767624463108659/970000000000000000 : ℝ)+2*(417494322857/339500000000000 : ℝ)*(1477/10000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (969767624463108659/970000000000000000 : ℝ)+2*(417494322857/339500000000000 : ℝ)*(1477/10000 : ℝ)=(10001237006923711/10000000000000000 : ℝ) by norm_num, show 1+2*(26622801420639677/100000000000000000000 : ℝ)=(50026622801420639677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (969767624463108659/970000000000000000 : ℝ)*(X 1 0+X 2 0)+(417494322857/339500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (969767624463108659/970000000000000000 : ℝ)) (alpha := (417494322857/339500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (969767624463108659/970000000000000000 : ℝ)*(X 0 1+X 2 1)+(417494322857/339500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (969767624463108659/970000000000000000 : ℝ)) (alpha := (417494322857/339500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (969767624463108659/970000000000000000 : ℝ)*(X 0 2+X 1 2)+(417494322857/339500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (969767624463108659/970000000000000000 : ℝ)) (alpha := (417494322857/339500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1955817153/10000000000 : ℝ)*X 0 0+(2703622083/5000000000 : ℝ)*X 0 1+(5247311449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668365189/1250000000 : ℝ)*X 1 0+(-40744579/200000000 : ℝ)*X 1 1+(5247311393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673460811/5000000000 : ℝ)*X 2 0+(262365561/500000000 : ℝ)*X 2 1+(-1018614517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149822337/5000000000 : ℝ)*X 0 0+(4128593947/10000000000 : ℝ)*X 0 1+(2238496017/5000000000 : ℝ)*X 0 2+(2149822337/5000000000 : ℝ)*X 1 0+(4128593947/10000000000 : ℝ)*X 1 1+(2238496017/5000000000 : ℝ)*X 1 2+(2149822337/5000000000 : ℝ)*X 2 0+(4128593947/10000000000 : ℝ)*X 2 1+(2238496017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-122239281/625000000 : ℝ)*X 0 0+(2623944439/5000000000 : ℝ)*X 0 1+(2703331801/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305267379/10000000000 : ℝ)*X 1 0+(-75115067/400000000 : ℝ)*X 1 1+(5406663407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305267913/10000000000 : ℝ)*X 2 0+(2703331333/5000000000 : ℝ)*X 2 1+(-469469241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149834653/5000000000 : ℝ)*X 0 0+(895146593/2000000000 : ℝ)*X 0 1+(4129859213/10000000000 : ℝ)*X 0 2+(2149834653/5000000000 : ℝ)*X 1 0+(895146593/2000000000 : ℝ)*X 1 1+(4129859213/10000000000 : ℝ)*X 1 2+(2149834653/5000000000 : ℝ)*X 2 0+(895146593/2000000000 : ℝ)*X 2 1+(4129859213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177858820481515721334189/16975000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145975333/10000000000000 : ℝ)*(base19) + (335768913/25000000000000 : ℝ)*(base23) + (38584449/25000000000000 : ℝ)*(lower2) + (263988031/100000000000000 : ℝ)*(upper3) + (23171637/100000000000000 : ℝ)*(lower4) + (1140374000738921/25000000000000 : ℝ)*(major0) + (1140374000738921/25000000000000 : ℝ)*(major1) + (1140374000738921/25000000000000 : ℝ)*(major2) + (6252660217426023/100000000000000 : ℝ)*(sp0) + (6252683531246659/100000000000000 : ℝ)*(sp1) + (390792727995271/6250000000000 : ℝ)*(sp2) + (717572623194411/25000000000000 : ℝ)*(sp3) + (4954714793/20000000000000 : ℝ)*(sp4) + (16172877331/100000000000000 : ℝ)*(sp7) + (114812266626199/4000000000000 : ℝ)*(f.failure) + (6252684990999989/100000000000000 : ℝ)*(f.sum) + (76041088562237/16975000000000000000000000000 : ℝ)*base66 + (307858414137391427/169750000000000000000000000000000 : ℝ)*base68 + (458848476733858573/169750000000000000000000000000000 : ℝ)*base69 + (1188278396472641427/169750000000000000000000000000000 : ℝ)*base72 + (2973356210987/16975000000000000000000000000 : ℝ)*base74 + (804961785683641427/169750000000000000000000000000000 : ℝ)*base76 + (102981915393358573/169750000000000000000000000000000 : ℝ)*base77 + (2345901588630608573/169750000000000000000000000000000 : ℝ)*base79 + (38641573618563/16975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1262119/200000000000000000000 : ℝ)*base89 + (1262119/200000000000000000000 : ℝ)*base91 + (1262119/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209383594144295589391292313/24250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2177420027/100000000000000 : ℝ)*(base19) + (2958022171/100000000000000 : ℝ)*(base23) + (15813939/2500000000000 : ℝ)*(lower1) + (143832427/100000000000000 : ℝ)*(lower4) + (202539651/50000000000000 : ℝ)*(upper5) + (2297353545591231/50000000000000 : ℝ)*(major0) + (2297353545591231/50000000000000 : ℝ)*(major1) + (2297353545591231/50000000000000 : ℝ)*(major2) + (48952063/10000000000000 : ℝ)*(sp0) + (1981386031/12500000000000 : ℝ)*(sp1) + (6298208769094867/100000000000000 : ℝ)*(sp4) + (6298191230107223/100000000000000 : ℝ)*(sp5) + (6298206300593327/100000000000000 : ℝ)*(sp6) + (2891204635936919/100000000000000 : ℝ)*(sp7) + (2891204635936919/100000000000000 : ℝ)*(f.failure) + (3149104629307749/50000000000000 : ℝ)*(f.sum) + (49033373017633/8487500000000000000000000000 : ℝ)*base66 + (2174628048173824603/339500000000000000000000000000000 : ℝ)*base67 + (4448279948728824603/339500000000000000000000000000000 : ℝ)*base69 + (2519862520266824603/339500000000000000000000000000000 : ℝ)*base71 + (12245967910829/4243750000000000000000000000 : ℝ)*base74 + (1745787017200675397/339500000000000000000000000000000 : ℝ)*base76 + (517068144075824603/339500000000000000000000000000000 : ℝ)*base77 + (1688642935678175397/339500000000000000000000000000000 : ℝ)*base80 + (33585349448909/16975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5369561/5000000000000000000000 : ℝ)*base90 + (5369561/5000000000000000000000 : ℝ)*base92 + (5369561/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1448_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1448_s7_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955821641/10000000000 : ℝ)*x 0 + (5407221609/10000000000 : ℝ)*x 1 + (5247330883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955821641/10000000000 : ℝ)^551 ≤ (11936723729009/100000000000000 : ℝ)^423 := by
    have hnat : (1955821641 : ℕ)^551*100000000000000^423 ≤ 11936723729009^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955821641 10000000000 11936723729009 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407221609/10000000000 : ℝ)^551 ≤ (22446158776671/50000000000000 : ℝ)^423 := by
    have hnat : (5407221609 : ℕ)^551*50000000000000^423 ≤ 22446158776671^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407221609 10000000000 22446158776671 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247330883/10000000000 : ℝ)^551 ≤ (4317095870887/10000000000000 : ℝ)^423 := by
    have hnat : (5247330883 : ℕ)^551*10000000000000^423 ≤ 4317095870887^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247330883 10000000000 4317095870887 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955821641/10000000000 : ℝ), (5407221609/10000000000 : ℝ), (5247330883/10000000000 : ℝ)] ![(11936723729009/100000000000000 : ℝ), (22446158776671/50000000000000 : ℝ), (4317095870887/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955821641/10000000000 : ℝ)|^551 ≤ (11936723729009/100000000000000 : ℝ)^423
        have hw : |(-1955821641/10000000000 : ℝ)|=(1955821641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407221609/10000000000 : ℝ)|^551 ≤ (22446158776671/50000000000000 : ℝ)^423
        have hw : |(5407221609/10000000000 : ℝ)|=(5407221609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247330883/10000000000 : ℝ)|^551 ≤ (4317095870887/10000000000000 : ℝ)^423
        have hw : |(5247330883/10000000000 : ℝ)|=(5247330883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5346917957/10000000000 : ℝ)*x 0 + (-509302793/2500000000 : ℝ)*x 1 + (16397901/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346917957/10000000000 : ℝ)^551 ≤ (4424126303357/10000000000000 : ℝ)^423 := by
    have hnat : (5346917957 : ℕ)^551*10000000000000^423 ≤ 4424126303357^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346917957 10000000000 4424126303357 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509302793/2500000000 : ℝ)^551 ≤ (6293902853481/50000000000000 : ℝ)^423 := by
    have hnat : (509302793 : ℕ)^551*50000000000000^423 ≤ 6293902853481^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509302793 2500000000 6293902853481 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16397901/31250000 : ℝ)^551 ≤ (8634186248351/20000000000000 : ℝ)^423 := by
    have hnat : (16397901 : ℕ)^551*20000000000000^423 ≤ 8634186248351^423*31250000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16397901 31250000 8634186248351 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346917957/10000000000 : ℝ), (-509302793/2500000000 : ℝ), (16397901/31250000 : ℝ)] ![(4424126303357/10000000000000 : ℝ), (6293902853481/50000000000000 : ℝ), (8634186248351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346917957/10000000000 : ℝ)|^551 ≤ (4424126303357/10000000000000 : ℝ)^423
        have hw : |(5346917957/10000000000 : ℝ)|=(5346917957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509302793/2500000000 : ℝ)|^551 ≤ (6293902853481/50000000000000 : ℝ)^423
        have hw : |(-509302793/2500000000 : ℝ)|=(509302793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16397901/31250000 : ℝ)|^551 ≤ (8634186248351/20000000000000 : ℝ)^423
        have hw : |(16397901/31250000 : ℝ)|=(16397901/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5346916509/10000000000 : ℝ)*x 0 + (2623665441/5000000000 : ℝ)*x 1 + (-2037209701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346916509/10000000000 : ℝ)^551 ≤ (44241247427133/100000000000000 : ℝ)^423 := by
    have hnat : (5346916509 : ℕ)^551*100000000000000^423 ≤ 44241247427133^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346916509 10000000000 44241247427133 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623665441/5000000000 : ℝ)^551 ≤ (43170958698153/100000000000000 : ℝ)^423 := by
    have hnat : (2623665441 : ℕ)^551*100000000000000^423 ≤ 43170958698153^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623665441 5000000000 43170958698153 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037209701/10000000000 : ℝ)^551 ≤ (629389693367/5000000000000 : ℝ)^423 := by
    have hnat : (2037209701 : ℕ)^551*5000000000000^423 ≤ 629389693367^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037209701 10000000000 629389693367 5000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346916509/10000000000 : ℝ), (2623665441/5000000000 : ℝ), (-2037209701/10000000000 : ℝ)] ![(44241247427133/100000000000000 : ℝ), (43170958698153/100000000000000 : ℝ), (629389693367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346916509/10000000000 : ℝ)|^551 ≤ (44241247427133/100000000000000 : ℝ)^423
        have hw : |(5346916509/10000000000 : ℝ)|=(5346916509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623665441/5000000000 : ℝ)|^551 ≤ (43170958698153/100000000000000 : ℝ)^423
        have hw : |(2623665441/5000000000 : ℝ)|=(2623665441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2037209701/10000000000 : ℝ)|^551 ≤ (629389693367/5000000000000 : ℝ)^423
        have hw : |(-2037209701/10000000000 : ℝ)|=(2037209701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1074911137/2500000000 : ℝ)*x 0 + (2064319993/5000000000 : ℝ)*x 1 + (4476947233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074911137/2500000000 : ℝ)^551 ≤ (33304971886271/100000000000000 : ℝ)^423 := by
    have hnat : (1074911137 : ℕ)^551*100000000000000^423 ≤ 33304971886271^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074911137 2500000000 33304971886271 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064319993/5000000000 : ℝ)^551 ≤ (15795014889889/50000000000000 : ℝ)^423 := by
    have hnat : (2064319993 : ℕ)^551*50000000000000^423 ≤ 15795014889889^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064319993 5000000000 15795014889889 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476947233/10000000000 : ℝ)^551 ≤ (17552499155133/50000000000000 : ℝ)^423 := by
    have hnat : (4476947233 : ℕ)^551*50000000000000^423 ≤ 17552499155133^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476947233 10000000000 17552499155133 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074911137/2500000000 : ℝ), (2064319993/5000000000 : ℝ), (4476947233/10000000000 : ℝ)] ![(33304971886271/100000000000000 : ℝ), (15795014889889/50000000000000 : ℝ), (17552499155133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074911137/2500000000 : ℝ)|^551 ≤ (33304971886271/100000000000000 : ℝ)^423
        have hw : |(1074911137/2500000000 : ℝ)|=(1074911137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064319993/5000000000 : ℝ)|^551 ≤ (15795014889889/50000000000000 : ℝ)^423
        have hw : |(2064319993/5000000000 : ℝ)|=(2064319993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476947233/10000000000 : ℝ)|^551 ≤ (17552499155133/50000000000000 : ℝ)^423
        have hw : |(4476947233/10000000000 : ℝ)|=(4476947233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-977915241/5000000000 : ℝ)*x 0 + (655988567/1250000000 : ℝ)*x 1 + (270332133/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977915241/5000000000 : ℝ)^551 ≤ (11936794015007/100000000000000 : ℝ)^423 := by
    have hnat : (977915241 : ℕ)^551*100000000000000^423 ≤ 11936794015007^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977915241 5000000000 11936794015007 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655988567/1250000000 : ℝ)^551 ≤ (43177149394359/100000000000000 : ℝ)^423 := by
    have hnat : (655988567 : ℕ)^551*100000000000000^423 ≤ 43177149394359^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655988567 1250000000 43177149394359 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270332133/500000000 : ℝ)^551 ≤ (5610757071587/12500000000000 : ℝ)^423 := by
    have hnat : (270332133 : ℕ)^551*12500000000000^423 ≤ 5610757071587^423*500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270332133 500000000 5610757071587 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977915241/5000000000 : ℝ), (655988567/1250000000 : ℝ), (270332133/500000000 : ℝ)] ![(11936794015007/100000000000000 : ℝ), (43177149394359/100000000000000 : ℝ), (5610757071587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977915241/5000000000 : ℝ)|^551 ≤ (11936794015007/100000000000000 : ℝ)^423
        have hw : |(-977915241/5000000000 : ℝ)|=(977915241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655988567/1250000000 : ℝ)|^551 ≤ (43177149394359/100000000000000 : ℝ)^423
        have hw : |(655988567/1250000000 : ℝ)|=(655988567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270332133/500000000 : ℝ)|^551 ≤ (5610757071587/12500000000000 : ℝ)^423
        have hw : |(270332133/500000000 : ℝ)|=(270332133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (132631813/250000000 : ℝ)*x 0 + (-1877898207/10000000000 : ℝ)*x 1 + (270332133/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132631813/250000000 : ℝ)^551 ≤ (43792941464171/100000000000000 : ℝ)^423 := by
    have hnat : (132631813 : ℕ)^551*100000000000000^423 ≤ 43792941464171^423*250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132631813 250000000 43792941464171 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877898207/10000000000 : ℝ)^551 ≤ (2830250488623/25000000000000 : ℝ)^423 := by
    have hnat : (1877898207 : ℕ)^551*25000000000000^423 ≤ 2830250488623^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877898207 10000000000 2830250488623 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270332133/500000000 : ℝ)^551 ≤ (5610757071587/12500000000000 : ℝ)^423 := by
    have hnat : (270332133 : ℕ)^551*12500000000000^423 ≤ 5610757071587^423*500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270332133 500000000 5610757071587 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132631813/250000000 : ℝ), (-1877898207/10000000000 : ℝ), (270332133/500000000 : ℝ)] ![(43792941464171/100000000000000 : ℝ), (2830250488623/25000000000000 : ℝ), (5610757071587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132631813/250000000 : ℝ)|^551 ≤ (43792941464171/100000000000000 : ℝ)^423
        have hw : |(132631813/250000000 : ℝ)|=(132631813/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1877898207/10000000000 : ℝ)|^551 ≤ (2830250488623/25000000000000 : ℝ)^423
        have hw : |(-1877898207/10000000000 : ℝ)|=(1877898207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270332133/500000000 : ℝ)|^551 ≤ (5610757071587/12500000000000 : ℝ)^423
        have hw : |(270332133/500000000 : ℝ)|=(270332133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305272501/10000000000 : ℝ)*x 0 + (2703321327/5000000000 : ℝ)*x 1 + (-1877898241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305272501/10000000000 : ℝ)^551 ≤ (21896470629937/50000000000000 : ℝ)^423 := by
    have hnat : (5305272501 : ℕ)^551*50000000000000^423 ≤ 21896470629937^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305272501 10000000000 21896470629937 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703321327/5000000000 : ℝ)^551 ≤ (44886056507811/100000000000000 : ℝ)^423 := by
    have hnat : (2703321327 : ℕ)^551*100000000000000^423 ≤ 44886056507811^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703321327 5000000000 44886056507811 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877898241/10000000000 : ℝ)^551 ≤ (11321002221487/100000000000000 : ℝ)^423 := by
    have hnat : (1877898241 : ℕ)^551*100000000000000^423 ≤ 11321002221487^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877898241 10000000000 11321002221487 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305272501/10000000000 : ℝ), (2703321327/5000000000 : ℝ), (-1877898241/10000000000 : ℝ)] ![(21896470629937/50000000000000 : ℝ), (44886056507811/100000000000000 : ℝ), (11321002221487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305272501/10000000000 : ℝ)|^551 ≤ (21896470629937/50000000000000 : ℝ)^423
        have hw : |(5305272501/10000000000 : ℝ)|=(5305272501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703321327/5000000000 : ℝ)|^551 ≤ (44886056507811/100000000000000 : ℝ)^423
        have hw : |(2703321327/5000000000 : ℝ)|=(2703321327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1877898241/10000000000 : ℝ)|^551 ≤ (11321002221487/100000000000000 : ℝ)^423
        have hw : |(-1877898241/10000000000 : ℝ)|=(1877898241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1074917619/2500000000 : ℝ)*x 0 + (4475689477/10000000000 : ℝ)*x 1 + (1032475647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074917619/2500000000 : ℝ)^551 ≤ (33305233497971/100000000000000 : ℝ)^423 := by
    have hnat : (1074917619 : ℕ)^551*100000000000000^423 ≤ 33305233497971^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074917619 2500000000 33305233497971 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475689477/10000000000 : ℝ)^551 ≤ (17546076033407/50000000000000 : ℝ)^423 := by
    have hnat : (4475689477 : ℕ)^551*50000000000000^423 ≤ 17546076033407^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475689477 10000000000 17546076033407 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032475647/2500000000 : ℝ)^551 ≤ (15801307210203/50000000000000 : ℝ)^423 := by
    have hnat : (1032475647 : ℕ)^551*50000000000000^423 ≤ 15801307210203^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032475647 2500000000 15801307210203 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074917619/2500000000 : ℝ), (4475689477/10000000000 : ℝ), (1032475647/2500000000 : ℝ)] ![(33305233497971/100000000000000 : ℝ), (17546076033407/50000000000000 : ℝ), (15801307210203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074917619/2500000000 : ℝ)|^551 ≤ (33305233497971/100000000000000 : ℝ)^423
        have hw : |(1074917619/2500000000 : ℝ)|=(1074917619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475689477/10000000000 : ℝ)|^551 ≤ (17546076033407/50000000000000 : ℝ)^423
        have hw : |(4475689477/10000000000 : ℝ)|=(4475689477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032475647/2500000000 : ℝ)|^551 ≤ (15801307210203/50000000000000 : ℝ)^423
        have hw : |(1032475647/2500000000 : ℝ)|=(1032475647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_8 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-25684903/10000000000 : ℝ)*x 0 + (733958863/1250000000 : ℝ)*x 1 + (5871620649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25684903/10000000000 : ℝ)^551 ≤ (42251803057/100000000000000 : ℝ)^423 := by
    have hnat : (25684903 : ℕ)^551*100000000000000^423 ≤ 42251803057^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25684903 10000000000 42251803057 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733958863/1250000000 : ℝ)^551 ≤ (24989576346959/50000000000000 : ℝ)^423 := by
    have hnat : (733958863 : ℕ)^551*50000000000000^423 ≤ 24989576346959^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733958863 1250000000 24989576346959 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5871620649/10000000000 : ℝ)^551 ≤ (3123662217887/6250000000000 : ℝ)^423 := by
    have hnat : (5871620649 : ℕ)^551*6250000000000^423 ≤ 3123662217887^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5871620649 10000000000 3123662217887 6250000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25684903/10000000000 : ℝ), (733958863/1250000000 : ℝ), (5871620649/10000000000 : ℝ)] ![(42251803057/100000000000000 : ℝ), (24989576346959/50000000000000 : ℝ), (3123662217887/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25684903/10000000000 : ℝ)|^551 ≤ (42251803057/100000000000000 : ℝ)^423
        have hw : |(-25684903/10000000000 : ℝ)|=(25684903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733958863/1250000000 : ℝ)|^551 ≤ (24989576346959/50000000000000 : ℝ)^423
        have hw : |(733958863/1250000000 : ℝ)|=(733958863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5871620649/10000000000 : ℝ)|^551 ≤ (3123662217887/6250000000000 : ℝ)^423
        have hw : |(5871620649/10000000000 : ℝ)|=(5871620649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_9 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (61521233/625000000 : ℝ)*x 0 + (-4376785817/10000000000 : ℝ)*x 1 + (855646949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61521233/625000000 : ℝ)^551 ≤ (610070790101/12500000000000 : ℝ)^423 := by
    have hnat : (61521233 : ℕ)^551*12500000000000^423 ≤ 610070790101^423*625000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61521233 625000000 610070790101 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4376785817/10000000000 : ℝ)^551 ≤ (17042712634381/50000000000000 : ℝ)^423 := by
    have hnat : (4376785817 : ℕ)^551*50000000000000^423 ≤ 17042712634381^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376785817 10000000000 17042712634381 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (855646949/1250000000 : ℝ)^551 ≤ (61034008403611/100000000000000 : ℝ)^423 := by
    have hnat : (855646949 : ℕ)^551*100000000000000^423 ≤ 61034008403611^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855646949 1250000000 61034008403611 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(61521233/625000000 : ℝ), (-4376785817/10000000000 : ℝ), (855646949/1250000000 : ℝ)] ![(610070790101/12500000000000 : ℝ), (17042712634381/50000000000000 : ℝ), (61034008403611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(61521233/625000000 : ℝ)|^551 ≤ (610070790101/12500000000000 : ℝ)^423
        have hw : |(61521233/625000000 : ℝ)|=(61521233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4376785817/10000000000 : ℝ)|^551 ≤ (17042712634381/50000000000000 : ℝ)^423
        have hw : |(-4376785817/10000000000 : ℝ)|=(4376785817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(855646949/1250000000 : ℝ)|^551 ≤ (61034008403611/100000000000000 : ℝ)^423
        have hw : |(855646949/1250000000 : ℝ)|=(855646949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s7_10 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1430619999/10000000000 : ℝ)*x 0 + (688924487/1250000000 : ℝ)*x 1 + (2756277531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1430619999/10000000000 : ℝ)^551 ≤ (1588603587487/20000000000000 : ℝ)^423 := by
    have hnat : (1430619999 : ℕ)^551*20000000000000^423 ≤ 1588603587487^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430619999 10000000000 1588603587487 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688924487/1250000000 : ℝ)^551 ≤ (46022186592641/100000000000000 : ℝ)^423 := by
    have hnat : (688924487 : ℕ)^551*100000000000000^423 ≤ 46022186592641^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688924487 1250000000 46022186592641 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2756277531/5000000000 : ℝ)^551 ≤ (4603479546723/10000000000000 : ℝ)^423 := by
    have hnat : (2756277531 : ℕ)^551*10000000000000^423 ≤ 4603479546723^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756277531 5000000000 4603479546723 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1430619999/10000000000 : ℝ), (688924487/1250000000 : ℝ), (2756277531/5000000000 : ℝ)] ![(1588603587487/20000000000000 : ℝ), (46022186592641/100000000000000 : ℝ), (4603479546723/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1430619999/10000000000 : ℝ)|^551 ≤ (1588603587487/20000000000000 : ℝ)^423
        have hw : |(1430619999/10000000000 : ℝ)|=(1430619999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688924487/1250000000 : ℝ)|^551 ≤ (46022186592641/100000000000000 : ℝ)^423
        have hw : |(688924487/1250000000 : ℝ)|=(688924487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2756277531/5000000000 : ℝ)|^551 ≤ (4603479546723/10000000000000 : ℝ)^423
        have hw : |(2756277531/5000000000 : ℝ)|=(2756277531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5689/50000 : ℝ) ^ (4407/1024 : ℝ) ≤ (8661250835125703/100000000000000000000 : ℝ) := by
    have hpowers : (5689/50000 : ℝ)^4407 ≤ (8661250835125703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5689 : ℕ)^4407*100000000000000000000^1024 ≤ 8661250835125703^1024*50000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5689 50000 8661250835125703 100000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5689/50000 : ℝ)) (X := (8661250835125703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (4407/1024 : ℝ) ≤ (26599537018744427/100000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^4407 ≤ (26599537018744427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14767 : ℕ)^4407*100000000000000000000^1024 ≤ 26599537018744427^1024*100000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 26599537018744427 100000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (26599537018744427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008661250835125703/50000000000000000000 : ℝ) ≤ (400016098990207/400000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50008661250835125703/50000000000000000000 : ℝ)^1024 ≤ (400016098990207/400000000000000 : ℝ)^4407 := by
      have hnat : (50008661250835125703 : ℕ)^1024*400000000000000^4407 ≤ 400016098990207^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008661250835125703 50000000000000000000 400016098990207 400000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400016098990207/400000000000000 : ℝ)) (X := (50008661250835125703/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003526078785387013/10000000000000000000 : ℝ) ≤ (10000819200388207/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (10003526078785387013/10000000000000000000 : ℝ)^1024 ≤ (10000819200388207/10000000000000000 : ℝ)^4407 := by
      have hnat : (10003526078785387013 : ℕ)^1024*10000000000000000^4407 ≤ 10000819200388207^4407*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003526078785387013 10000000000000000000 10000819200388207 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000819200388207/10000000000000000 : ℝ)) (X := (10003526078785387013/10000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026599537018744427/50000000000000000000 : ℝ) ≤ (10001235926021239/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50026599537018744427/50000000000000000000 : ℝ)^1024 ≤ (10001235926021239/10000000000000000 : ℝ)^4407 := by
      have hnat : (50026599537018744427 : ℕ)^1024*10000000000000000^4407 ≤ 10001235926021239^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026599537018744427 50000000000000000000 10001235926021239 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001235926021239/10000000000000000 : ℝ)) (X := (50026599537018744427/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8661250835125703/100000000000000000000 : ℝ) ≤ ((33881880978440011883/33890000000000000000 : ℝ)+2*(52090704129/42362500000000 : ℝ)*(5689/50000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (33881880978440011883/33890000000000000000 : ℝ)+2*(52090704129/42362500000000 : ℝ)*(5689/50000 : ℝ)=(400016098990207/400000000000000 : ℝ) by norm_num, show 1+2*(8661250835125703/100000000000000000000 : ℝ)=(50008661250835125703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26599537018744427/100000000000000000000 : ℝ)+(8661250835125703/100000000000000000000 : ℝ) ≤ ((33881880978440011883/33890000000000000000 : ℝ)+(52090704129/42362500000000 : ℝ)*((14767/100000 : ℝ)+(5689/50000 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (33881880978440011883/33890000000000000000 : ℝ)+(52090704129/42362500000000 : ℝ)*((14767/100000 : ℝ)+(5689/50000 : ℝ))=(10000819200388207/10000000000000000 : ℝ) by norm_num, show 1+(26599537018744427/100000000000000000000 : ℝ)+(8661250835125703/100000000000000000000 : ℝ)=(10003526078785387013/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26599537018744427/100000000000000000000 : ℝ) ≤ ((33881880978440011883/33890000000000000000 : ℝ)+2*(52090704129/42362500000000 : ℝ)*(14767/100000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (33881880978440011883/33890000000000000000 : ℝ)+2*(52090704129/42362500000000 : ℝ)*(14767/100000 : ℝ)=(10001235926021239/10000000000000000 : ℝ) by norm_num, show 1+2*(26599537018744427/100000000000000000000 : ℝ)=(50026599537018744427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33881880978440011883/33890000000000000000 : ℝ)*(X 1 0+X 2 0)+(52090704129/42362500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (33881880978440011883/33890000000000000000 : ℝ)) (alpha := (52090704129/42362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33881880978440011883/33890000000000000000 : ℝ)*(X 0 1+X 2 1)+(52090704129/42362500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (33881880978440011883/33890000000000000000 : ℝ)) (alpha := (52090704129/42362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33881880978440011883/33890000000000000000 : ℝ)*(X 0 2+X 1 2)+(52090704129/42362500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (33881880978440011883/33890000000000000000 : ℝ)) (alpha := (52090704129/42362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1955821641/10000000000 : ℝ)*X 0 0+(5407221609/10000000000 : ℝ)*X 0 1+(5247330883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346917957/10000000000 : ℝ)*X 1 0+(-509302793/2500000000 : ℝ)*X 1 1+(16397901/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346916509/10000000000 : ℝ)*X 2 0+(2623665441/5000000000 : ℝ)*X 2 1+(-2037209701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074911137/2500000000 : ℝ)*X 0 0+(2064319993/5000000000 : ℝ)*X 0 1+(4476947233/10000000000 : ℝ)*X 0 2+(1074911137/2500000000 : ℝ)*X 1 0+(2064319993/5000000000 : ℝ)*X 1 1+(4476947233/10000000000 : ℝ)*X 1 2+(1074911137/2500000000 : ℝ)*X 2 0+(2064319993/5000000000 : ℝ)*X 2 1+(4476947233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-977915241/5000000000 : ℝ)*X 0 0+(655988567/1250000000 : ℝ)*X 0 1+(270332133/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132631813/250000000 : ℝ)*X 1 0+(-1877898207/10000000000 : ℝ)*X 1 1+(270332133/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305272501/10000000000 : ℝ)*X 2 0+(2703321327/5000000000 : ℝ)*X 2 1+(-1877898241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074917619/2500000000 : ℝ)*X 0 0+(4475689477/10000000000 : ℝ)*X 0 1+(1032475647/2500000000 : ℝ)*X 0 2+(1074917619/2500000000 : ℝ)*X 1 0+(4475689477/10000000000 : ℝ)*X 1 1+(1032475647/2500000000 : ℝ)*X 1 2+(1074917619/2500000000 : ℝ)*X 2 0+(4475689477/10000000000 : ℝ)*X 2 1+(1032475647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-25684903/10000000000 : ℝ)*X 0 0+(733958863/1250000000 : ℝ)*X 0 1+(5871620649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((61521233/625000000 : ℝ)*X 1 0+(-4376785817/10000000000 : ℝ)*X 1 1+(855646949/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1430619999/10000000000 : ℝ)*X 0 0+(688924487/1250000000 : ℝ)*X 0 1+(2756277531/5000000000 : ℝ)*X 0 2+(1430619999/10000000000 : ℝ)*X 1 0+(688924487/1250000000 : ℝ)*X 1 1+(2756277531/5000000000 : ℝ)*X 1 2+(1430619999/10000000000 : ℝ)*X 2 0+(688924487/1250000000 : ℝ)*X 2 1+(2756277531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s7_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1447167011099521741670987493/847250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39588381/6250000000000 : ℝ)*(lower3) + (231861337/50000000000000 : ℝ)*(lower4) + (42241507/20000000000000 : ℝ)*(lower5) + (4562664699180443/100000000000000 : ℝ)*(major0) + (4562664699180443/100000000000000 : ℝ)*(major1) + (4562664699180443/100000000000000 : ℝ)*(major2) + (6254275072135611/100000000000000 : ℝ)*(sp0) + (6254181993386437/100000000000000 : ℝ)*(sp1) + (3127124505406137/50000000000000 : ℝ)*(sp2) + (179440128999351/6250000000000 : ℝ)*(sp3) + (104907288523/100000000000000 : ℝ)*(sp5) + (38266623133/100000000000000 : ℝ)*(sp6) + (3051324949/25000000000000 : ℝ)*(sp8) + (376760447/100000000000000 : ℝ)*(sp9) + (179440128999351/6250000000000 : ℝ)*(f.failure) + (6254287277435407/100000000000000 : ℝ)*(f.sum) + (50278429812729/16945000000000000000000000000 : ℝ)*base66 + (14815415917647804169/3389000000000000000000000000000000 : ℝ)*base67 + (8706893936693804169/3389000000000000000000000000000000 : ℝ)*base69 + (30337543949081804169/3389000000000000000000000000000000 : ℝ)*base71 + (1783395726317/2118125000000000000000000000 : ℝ)*base73 + (12108994024690804169/3389000000000000000000000000000000 : ℝ)*base75 + (26793254838135804169/3389000000000000000000000000000000 : ℝ)*base77 + (6663411893515195831/3389000000000000000000000000000000 : ℝ)*base80 + (2872712686769/16945000000000000000000000000 : ℝ)*base82 + (4967569/312500000000000000000 : ℝ)*base90 + (4967569/312500000000000000000 : ℝ)*base92 + (4967569/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3032179121194534512092797881/423625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61025891/100000000000000 : ℝ)*(lower1) + (1059789/625000000000 : ℝ)*(lower3) + (4622781/25000000000000 : ℝ)*(lower4) + (28814773/20000000000000 : ℝ)*(lower5) + (1148974335617677/25000000000000 : ℝ)*(major0) + (1148974335617677/25000000000000 : ℝ)*(major1) + (1148974335617677/25000000000000 : ℝ)*(major2) + (782970187/50000000000000 : ℝ)*(sp1) + (3149919525424367/50000000000000 : ℝ)*(sp4) + (3149919641342667/50000000000000 : ℝ)*(sp5) + (1574960212156427/25000000000000 : ℝ)*(sp6) + (578390449997429/20000000000000 : ℝ)*(sp7) + (898888487/50000000000000 : ℝ)*(sp8) + (1347738679/100000000000000 : ℝ)*(sp10) + (22593387482233/781250000000 : ℝ)*(f.failure) + (1574960212156427/25000000000000 : ℝ)*(f.sum) + (100871148653639/16945000000000000000000000000 : ℝ)*base66 + (4220505525331005791/847250000000000000000000000000000 : ℝ)*base67 + (10767705767332255791/847250000000000000000000000000000 : ℝ)*base69 + (24078418873505791/847250000000000000000000000000000 : ℝ)*base71 + (31434623279779/16945000000000000000000000000 : ℝ)*base74 + (1620954428205755791/847250000000000000000000000000000 : ℝ)*base75 + (6221764605176005791/847250000000000000000000000000000 : ℝ)*base77 + (3514414905689005791/847250000000000000000000000000000 : ℝ)*base79 + (39744598486597/8472500000000000000000000000 : ℝ)*base82 + (71627/39062500000000000000 : ℝ)*base90 + (71627/39062500000000000000 : ℝ)*base92 + (71627/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1448_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1448_box_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1796520241/10000000000 : ℝ)*x 0 + (215417603/400000000 : ℝ)*x 1 + (2692720151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1796520241/10000000000 : ℝ)^551 ≤ (1335773837353/12500000000000 : ℝ)^423 := by
    have hnat : (1796520241 : ℕ)^551*12500000000000^423 ≤ 1335773837353^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796520241 10000000000 1335773837353 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215417603/400000000 : ℝ)^551 ≤ (44656903420549/100000000000000 : ℝ)^423 := by
    have hnat : (215417603 : ℕ)^551*100000000000000^423 ≤ 44656903420549^423*400000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215417603 400000000 44656903420549 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692720151/5000000000 : ℝ)^551 ≤ (44656905872459/100000000000000 : ℝ)^423 := by
    have hnat : (2692720151 : ℕ)^551*100000000000000^423 ≤ 44656905872459^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692720151 5000000000 44656905872459 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1796520241/10000000000 : ℝ), (215417603/400000000 : ℝ), (2692720151/5000000000 : ℝ)] ![(1335773837353/12500000000000 : ℝ), (44656903420549/100000000000000 : ℝ), (44656905872459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1796520241/10000000000 : ℝ)|^551 ≤ (1335773837353/12500000000000 : ℝ)^423
        have hw : |(-1796520241/10000000000 : ℝ)|=(1796520241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215417603/400000000 : ℝ)|^551 ≤ (44656903420549/100000000000000 : ℝ)^423
        have hw : |(215417603/400000000 : ℝ)|=(215417603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692720151/5000000000 : ℝ)|^551 ≤ (44656905872459/100000000000000 : ℝ)^423
        have hw : |(2692720151/5000000000 : ℝ)|=(2692720151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5286187311/10000000000 : ℝ)*x 0 + (-96647707/500000000 : ℝ)*x 1 + (2692720343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286187311/10000000000 : ℝ)^551 ≤ (43587840393701/100000000000000 : ℝ)^423 := by
    have hnat : (5286187311 : ℕ)^551*100000000000000^423 ≤ 43587840393701^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286187311 10000000000 43587840393701 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96647707/500000000 : ℝ)^551 ≤ (11755249574537/100000000000000 : ℝ)^423 := by
    have hnat : (96647707 : ℕ)^551*100000000000000^423 ≤ 11755249574537^423*500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96647707 500000000 11755249574537 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692720343/5000000000 : ℝ)^551 ≤ (44656910020183/100000000000000 : ℝ)^423 := by
    have hnat : (2692720343 : ℕ)^551*100000000000000^423 ≤ 44656910020183^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692720343 5000000000 44656910020183 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286187311/10000000000 : ℝ), (-96647707/500000000 : ℝ), (2692720343/5000000000 : ℝ)] ![(43587840393701/100000000000000 : ℝ), (11755249574537/100000000000000 : ℝ), (44656910020183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286187311/10000000000 : ℝ)|^551 ≤ (43587840393701/100000000000000 : ℝ)^423
        have hw : |(5286187311/10000000000 : ℝ)|=(5286187311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96647707/500000000 : ℝ)|^551 ≤ (11755249574537/100000000000000 : ℝ)^423
        have hw : |(-96647707/500000000 : ℝ)|=(96647707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692720343/5000000000 : ℝ)|^551 ≤ (44656910020183/100000000000000 : ℝ)^423
        have hw : |(2692720343/5000000000 : ℝ)|=(2692720343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (660773489/1250000000 : ℝ)*x 0 + (5385440279/10000000000 : ℝ)*x 1 + (-48323847/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660773489/1250000000 : ℝ)^551 ≤ (43587846848883/100000000000000 : ℝ)^423 := by
    have hnat : (660773489 : ℕ)^551*100000000000000^423 ≤ 43587846848883^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660773489 1250000000 43587846848883 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385440279/10000000000 : ℝ)^551 ≤ (44656905624027/100000000000000 : ℝ)^423 := by
    have hnat : (5385440279 : ℕ)^551*100000000000000^423 ≤ 44656905624027^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385440279 10000000000 44656905624027 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48323847/250000000 : ℝ)^551 ≤ (9183787121/78125000000 : ℝ)^423 := by
    have hnat : (48323847 : ℕ)^551*78125000000^423 ≤ 9183787121^423*250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48323847 250000000 9183787121 78125000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660773489/1250000000 : ℝ), (5385440279/10000000000 : ℝ), (-48323847/250000000 : ℝ)] ![(43587846848883/100000000000000 : ℝ), (44656905624027/100000000000000 : ℝ), (9183787121/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660773489/1250000000 : ℝ)|^551 ≤ (43587846848883/100000000000000 : ℝ)^423
        have hw : |(660773489/1250000000 : ℝ)|=(660773489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385440279/10000000000 : ℝ)|^551 ≤ (44656905624027/100000000000000 : ℝ)^423
        have hw : |(5385440279/10000000000 : ℝ)|=(5385440279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48323847/250000000 : ℝ)|^551 ≤ (9183787121/78125000000 : ℝ)^423
        have hw : |(-48323847/250000000 : ℝ)|=(48323847/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2222784333/5000000000 : ℝ)*x 0 + (4230357279/10000000000 : ℝ)*x 1 + (846071537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2222784333/5000000000 : ℝ)^551 ≤ (17392418159423/50000000000000 : ℝ)^423 := by
    have hnat : (2222784333 : ℕ)^551*50000000000000^423 ≤ 17392418159423^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222784333 5000000000 17392418159423 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230357279/10000000000 : ℝ)^551 ≤ (8151894947691/25000000000000 : ℝ)^423 := by
    have hnat : (4230357279 : ℕ)^551*25000000000000^423 ≤ 8151894947691^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230357279 10000000000 8151894947691 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846071537/2000000000 : ℝ)^551 ≤ (32607583867183/100000000000000 : ℝ)^423 := by
    have hnat : (846071537 : ℕ)^551*100000000000000^423 ≤ 32607583867183^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846071537 2000000000 32607583867183 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2222784333/5000000000 : ℝ), (4230357279/10000000000 : ℝ), (846071537/2000000000 : ℝ)] ![(17392418159423/50000000000000 : ℝ), (8151894947691/25000000000000 : ℝ), (32607583867183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2222784333/5000000000 : ℝ)|^551 ≤ (17392418159423/50000000000000 : ℝ)^423
        have hw : |(2222784333/5000000000 : ℝ)|=(2222784333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230357279/10000000000 : ℝ)|^551 ≤ (8151894947691/25000000000000 : ℝ)^423
        have hw : |(4230357279/10000000000 : ℝ)|=(4230357279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846071537/2000000000 : ℝ)|^551 ≤ (32607583867183/100000000000000 : ℝ)^423
        have hw : |(846071537/2000000000 : ℝ)|=(846071537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-105892527/500000000 : ℝ)*x 0 + (5266793383/10000000000 : ℝ)*x 1 + (5266793287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105892527/500000000 : ℝ)^551 ≤ (13240698896713/100000000000000 : ℝ)^423 := by
    have hnat : (105892527 : ℕ)^551*100000000000000^423 ≤ 13240698896713^423*500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105892527 500000000 13240698896713 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266793383/10000000000 : ℝ)^551 ≤ (8675930212567/20000000000000 : ℝ)^423 := by
    have hnat : (5266793383 : ℕ)^551*20000000000000^423 ≤ 8675930212567^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266793383 10000000000 8675930212567 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266793287/10000000000 : ℝ)^551 ≤ (43379650032871/100000000000000 : ℝ)^423 := by
    have hnat : (5266793287 : ℕ)^551*100000000000000^423 ≤ 43379650032871^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266793287 10000000000 43379650032871 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105892527/500000000 : ℝ), (5266793383/10000000000 : ℝ), (5266793287/10000000000 : ℝ)] ![(13240698896713/100000000000000 : ℝ), (8675930212567/20000000000000 : ℝ), (43379650032871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105892527/500000000 : ℝ)|^551 ≤ (13240698896713/100000000000000 : ℝ)^423
        have hw : |(-105892527/500000000 : ℝ)|=(105892527/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266793383/10000000000 : ℝ)|^551 ≤ (8675930212567/20000000000000 : ℝ)^423
        have hw : |(5266793383/10000000000 : ℝ)|=(5266793383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266793287/10000000000 : ℝ)|^551 ≤ (43379650032871/100000000000000 : ℝ)^423
        have hw : |(5266793287/10000000000 : ℝ)|=(5266793287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5369158863/10000000000 : ℝ)*x 0 + (-1981243683/10000000000 : ℝ)*x 1 + (2633396649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369158863/10000000000 : ℝ)^551 ≤ (44481124604699/100000000000000 : ℝ)^423 := by
    have hnat : (5369158863 : ℕ)^551*100000000000000^423 ≤ 44481124604699^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369158863 10000000000 44481124604699 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981243683/10000000000 : ℝ)^551 ≤ (2427845046411/20000000000000 : ℝ)^423 := by
    have hnat : (1981243683 : ℕ)^551*20000000000000^423 ≤ 2427845046411^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981243683 10000000000 2427845046411 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633396649/5000000000 : ℝ)^551 ≤ (43379650150887/100000000000000 : ℝ)^423 := by
    have hnat : (2633396649 : ℕ)^551*100000000000000^423 ≤ 43379650150887^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633396649 5000000000 43379650150887 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369158863/10000000000 : ℝ), (-1981243683/10000000000 : ℝ), (2633396649/5000000000 : ℝ)] ![(44481124604699/100000000000000 : ℝ), (2427845046411/20000000000000 : ℝ), (43379650150887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369158863/10000000000 : ℝ)|^551 ≤ (44481124604699/100000000000000 : ℝ)^423
        have hw : |(5369158863/10000000000 : ℝ)|=(5369158863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1981243683/10000000000 : ℝ)|^551 ≤ (2427845046411/20000000000000 : ℝ)^423
        have hw : |(-1981243683/10000000000 : ℝ)|=(1981243683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633396649/5000000000 : ℝ)|^551 ≤ (43379650150887/100000000000000 : ℝ)^423
        have hw : |(2633396649/5000000000 : ℝ)|=(2633396649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (8389311/15625000 : ℝ)*x 0 + (658349151/1250000000 : ℝ)*x 1 + (-495310891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8389311/15625000 : ℝ)^551 ≤ (4448112651479/10000000000000 : ℝ)^423 := by
    have hnat : (8389311 : ℕ)^551*10000000000000^423 ≤ 4448112651479^423*15625000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8389311 15625000 4448112651479 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658349151/1250000000 : ℝ)^551 ≤ (2711228074081/6250000000000 : ℝ)^423 := by
    have hnat : (658349151 : ℕ)^551*6250000000000^423 ≤ 2711228074081^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658349151 1250000000 2711228074081 6250000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495310891/2500000000 : ℝ)^551 ≤ (12139224282301/100000000000000 : ℝ)^423 := by
    have hnat : (495310891 : ℕ)^551*100000000000000^423 ≤ 12139224282301^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495310891 2500000000 12139224282301 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8389311/15625000 : ℝ), (658349151/1250000000 : ℝ), (-495310891/2500000000 : ℝ)] ![(4448112651479/10000000000000 : ℝ), (2711228074081/6250000000000 : ℝ), (12139224282301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8389311/15625000 : ℝ)|^551 ≤ (4448112651479/10000000000000 : ℝ)^423
        have hw : |(8389311/15625000 : ℝ)|=(8389311/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658349151/1250000000 : ℝ)|^551 ≤ (2711228074081/6250000000000 : ℝ)^423
        have hw : |(658349151/1250000000 : ℝ)|=(658349151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495310891/2500000000 : ℝ)|^551 ≤ (12139224282301/100000000000000 : ℝ)^423
        have hw : |(-495310891/2500000000 : ℝ)|=(495310891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4152650251/10000000000 : ℝ)*x 0 + (2188383113/5000000000 : ℝ)*x 1 + (4376766441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152650251/10000000000 : ℝ)^551 ≤ (31829544745733/100000000000000 : ℝ)^423 := by
    have hnat : (4152650251 : ℕ)^551*100000000000000^423 ≤ 31829544745733^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152650251 10000000000 31829544745733 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188383113/5000000000 : ℝ)^551 ≤ (34085226530739/100000000000000 : ℝ)^423 := by
    have hnat : (2188383113 : ℕ)^551*100000000000000^423 ≤ 34085226530739^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188383113 5000000000 34085226530739 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4376766441/10000000000 : ℝ)^551 ≤ (17042614355887/50000000000000 : ℝ)^423 := by
    have hnat : (4376766441 : ℕ)^551*50000000000000^423 ≤ 17042614355887^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376766441 10000000000 17042614355887 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152650251/10000000000 : ℝ), (2188383113/5000000000 : ℝ), (4376766441/10000000000 : ℝ)] ![(31829544745733/100000000000000 : ℝ), (34085226530739/100000000000000 : ℝ), (17042614355887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152650251/10000000000 : ℝ)|^551 ≤ (31829544745733/100000000000000 : ℝ)^423
        have hw : |(4152650251/10000000000 : ℝ)|=(4152650251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2188383113/5000000000 : ℝ)|^551 ≤ (34085226530739/100000000000000 : ℝ)^423
        have hw : |(2188383113/5000000000 : ℝ)|=(2188383113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4376766441/10000000000 : ℝ)|^551 ≤ (17042614355887/50000000000000 : ℝ)^423
        have hw : |(4376766441/10000000000 : ℝ)|=(4376766441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_8 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-512532133/2500000000 : ℝ)*x 0 + (5184641639/10000000000 : ℝ)*x 1 + (2699701327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512532133/2500000000 : ℝ)^551 ≤ (793242070701/6250000000000 : ℝ)^423 := by
    have hnat : (512532133 : ℕ)^551*6250000000000^423 ≤ 793242070701^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512532133 2500000000 793242070701 6250000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184641639/10000000000 : ℝ)^551 ≤ (166016989799/390625000000 : ℝ)^423 := by
    have hnat : (5184641639 : ℕ)^551*390625000000^423 ≤ 166016989799^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184641639 10000000000 166016989799 390625000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699701327/5000000000 : ℝ)^551 ≤ (11201944363993/25000000000000 : ℝ)^423 := by
    have hnat : (2699701327 : ℕ)^551*25000000000000^423 ≤ 11201944363993^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699701327 5000000000 11201944363993 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512532133/2500000000 : ℝ), (5184641639/10000000000 : ℝ), (2699701327/5000000000 : ℝ)] ![(793242070701/6250000000000 : ℝ), (166016989799/390625000000 : ℝ), (11201944363993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512532133/2500000000 : ℝ)|^551 ≤ (793242070701/6250000000000 : ℝ)^423
        have hw : |(-512532133/2500000000 : ℝ)|=(512532133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184641639/10000000000 : ℝ)|^551 ≤ (166016989799/390625000000 : ℝ)^423
        have hw : |(5184641639/10000000000 : ℝ)|=(5184641639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699701327/5000000000 : ℝ)|^551 ≤ (11201944363993/25000000000000 : ℝ)^423
        have hw : |(2699701327/5000000000 : ℝ)|=(2699701327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_9 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5276420859/10000000000 : ℝ)*x 0 + (-1927146273/10000000000 : ℝ)*x 1 + (53994017/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276420859/10000000000 : ℝ)^551 ≤ (8696594169607/20000000000000 : ℝ)^423 := by
    have hnat : (5276420859 : ℕ)^551*20000000000000^423 ≤ 8696594169607^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276420859 10000000000 8696594169607 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927146273/10000000000 : ℝ)^551 ≤ (1170926199183/10000000000000 : ℝ)^423 := by
    have hnat : (1927146273 : ℕ)^551*10000000000000^423 ≤ 1170926199183^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927146273 10000000000 1170926199183 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53994017/100000000 : ℝ)^551 ≤ (44807767143393/100000000000000 : ℝ)^423 := by
    have hnat : (53994017 : ℕ)^551*100000000000000^423 ≤ 44807767143393^423*100000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53994017 100000000 44807767143393 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276420859/10000000000 : ℝ), (-1927146273/10000000000 : ℝ), (53994017/100000000 : ℝ)] ![(8696594169607/20000000000000 : ℝ), (1170926199183/10000000000000 : ℝ), (44807767143393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276420859/10000000000 : ℝ)|^551 ≤ (8696594169607/20000000000000 : ℝ)^423
        have hw : |(5276420859/10000000000 : ℝ)|=(5276420859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927146273/10000000000 : ℝ)|^551 ≤ (1170926199183/10000000000000 : ℝ)^423
        have hw : |(-1927146273/10000000000 : ℝ)|=(1927146273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53994017/100000000 : ℝ)|^551 ≤ (44807767143393/100000000000000 : ℝ)^423
        have hw : |(53994017/100000000 : ℝ)|=(53994017/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_10 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1319105109/2500000000 : ℝ)*x 0 + (67492521/125000000 : ℝ)*x 1 + (-616687/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319105109/2500000000 : ℝ)^551 ≤ (21741483153623/50000000000000 : ℝ)^423 := by
    have hnat : (1319105109 : ℕ)^551*50000000000000^423 ≤ 21741483153623^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319105109 2500000000 21741483153623 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67492521/125000000 : ℝ)^551 ≤ (11201941731799/25000000000000 : ℝ)^423 := by
    have hnat : (67492521 : ℕ)^551*25000000000000^423 ≤ 11201941731799^423*125000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67492521 125000000 11201941731799 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (616687/3200000 : ℝ)^551 ≤ (2927316689097/25000000000000 : ℝ)^423 := by
    have hnat : (616687 : ℕ)^551*25000000000000^423 ≤ 2927316689097^423*3200000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616687 3200000 2927316689097 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319105109/2500000000 : ℝ), (67492521/125000000 : ℝ), (-616687/3200000 : ℝ)] ![(21741483153623/50000000000000 : ℝ), (11201941731799/25000000000000 : ℝ), (2927316689097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319105109/2500000000 : ℝ)|^551 ≤ (21741483153623/50000000000000 : ℝ)^423
        have hw : |(1319105109/2500000000 : ℝ)|=(1319105109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67492521/125000000 : ℝ)|^551 ≤ (11201941731799/25000000000000 : ℝ)^423
        have hw : |(67492521/125000000 : ℝ)|=(67492521/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-616687/3200000 : ℝ)|^551 ≤ (2927316689097/25000000000000 : ℝ)^423
        have hw : |(-616687/3200000 : ℝ)|=(616687/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_11 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (223974087/500000000 : ℝ)*x 0 + (4213113883/10000000000 : ℝ)*x 1 + (2106556997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223974087/500000000 : ℝ)^551 ≤ (8782722030617/25000000000000 : ℝ)^423 := by
    have hnat : (223974087 : ℕ)^551*25000000000000^423 ≤ 8782722030617^423*500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223974087 500000000 8782722030617 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4213113883/10000000000 : ℝ)^551 ≤ (32434555380359/100000000000000 : ℝ)^423 := by
    have hnat : (4213113883 : ℕ)^551*100000000000000^423 ≤ 32434555380359^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213113883 10000000000 32434555380359 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106556997/5000000000 : ℝ)^551 ≤ (32434556493471/100000000000000 : ℝ)^423 := by
    have hnat : (2106556997 : ℕ)^551*100000000000000^423 ≤ 32434556493471^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106556997 5000000000 32434556493471 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223974087/500000000 : ℝ), (4213113883/10000000000 : ℝ), (2106556997/5000000000 : ℝ)] ![(8782722030617/25000000000000 : ℝ), (32434555380359/100000000000000 : ℝ), (32434556493471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223974087/500000000 : ℝ)|^551 ≤ (8782722030617/25000000000000 : ℝ)^423
        have hw : |(223974087/500000000 : ℝ)|=(223974087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4213113883/10000000000 : ℝ)|^551 ≤ (32434555380359/100000000000000 : ℝ)^423
        have hw : |(4213113883/10000000000 : ℝ)|=(4213113883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2106556997/5000000000 : ℝ)|^551 ≤ (32434556493471/100000000000000 : ℝ)^423
        have hw : |(2106556997/5000000000 : ℝ)|=(2106556997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_12 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1864391129/10000000000 : ℝ)*x 0 + (5465603847/10000000000 : ℝ)*x 1 + (525565853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1864391129/10000000000 : ℝ)^551 ≤ (11215049313809/100000000000000 : ℝ)^423 := by
    have hnat : (1864391129 : ℕ)^551*100000000000000^423 ≤ 11215049313809^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864391129 10000000000 11215049313809 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465603847/10000000000 : ℝ)^551 ≤ (4552472495379/10000000000000 : ℝ)^423 := by
    have hnat : (5465603847 : ℕ)^551*10000000000000^423 ≤ 4552472495379^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465603847 10000000000 4552472495379 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525565853/1000000000 : ℝ)^551 ≤ (10815056430959/25000000000000 : ℝ)^423 := by
    have hnat : (525565853 : ℕ)^551*25000000000000^423 ≤ 10815056430959^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525565853 1000000000 10815056430959 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1864391129/10000000000 : ℝ), (5465603847/10000000000 : ℝ), (525565853/1000000000 : ℝ)] ![(11215049313809/100000000000000 : ℝ), (4552472495379/10000000000000 : ℝ), (10815056430959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1864391129/10000000000 : ℝ)|^551 ≤ (11215049313809/100000000000000 : ℝ)^423
        have hw : |(-1864391129/10000000000 : ℝ)|=(1864391129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465603847/10000000000 : ℝ)|^551 ≤ (4552472495379/10000000000000 : ℝ)^423
        have hw : |(5465603847/10000000000 : ℝ)|=(5465603847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525565853/1000000000 : ℝ)|^551 ≤ (10815056430959/25000000000000 : ℝ)^423
        have hw : |(525565853/1000000000 : ℝ)|=(525565853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_13 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5376944099/10000000000 : ℝ)*x 0 + (-397135319/2000000000 : ℝ)*x 1 + (5255658551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376944099/10000000000 : ℝ)^551 ≤ (2228257859773/5000000000000 : ℝ)^423 := by
    have hnat : (5376944099 : ℕ)^551*5000000000000^423 ≤ 2228257859773^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376944099 10000000000 2228257859773 5000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397135319/2000000000 : ℝ)^551 ≤ (6087308421629/50000000000000 : ℝ)^423 := by
    have hnat : (397135319 : ℕ)^551*50000000000000^423 ≤ 6087308421629^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397135319 2000000000 6087308421629 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255658551/10000000000 : ℝ)^551 ≤ (10815056487249/25000000000000 : ℝ)^423 := by
    have hnat : (5255658551 : ℕ)^551*25000000000000^423 ≤ 10815056487249^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255658551 10000000000 10815056487249 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376944099/10000000000 : ℝ), (-397135319/2000000000 : ℝ), (5255658551/10000000000 : ℝ)] ![(2228257859773/5000000000000 : ℝ), (6087308421629/50000000000000 : ℝ), (10815056487249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376944099/10000000000 : ℝ)|^551 ≤ (2228257859773/5000000000000 : ℝ)^423
        have hw : |(5376944099/10000000000 : ℝ)|=(5376944099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397135319/2000000000 : ℝ)|^551 ≤ (6087308421629/50000000000000 : ℝ)^423
        have hw : |(-397135319/2000000000 : ℝ)|=(397135319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255658551/10000000000 : ℝ)|^551 ≤ (10815056487249/25000000000000 : ℝ)^423
        have hw : |(5255658551/10000000000 : ℝ)|=(5255658551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_14 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (336059003/625000000 : ℝ)*x 0 + (2627829289/5000000000 : ℝ)*x 1 + (-496419157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336059003/625000000 : ℝ)^551 ≤ (22282578322427/50000000000000 : ℝ)^423 := by
    have hnat : (336059003 : ℕ)^551*50000000000000^423 ≤ 22282578322427^423*625000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336059003 625000000 22282578322427 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627829289/5000000000 : ℝ)^551 ≤ (43260226238489/100000000000000 : ℝ)^423 := by
    have hnat : (2627829289 : ℕ)^551*100000000000000^423 ≤ 43260226238489^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627829289 5000000000 43260226238489 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496419157/2500000000 : ℝ)^551 ≤ (6087308553407/50000000000000 : ℝ)^423 := by
    have hnat : (496419157 : ℕ)^551*50000000000000^423 ≤ 6087308553407^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496419157 2500000000 6087308553407 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336059003/625000000 : ℝ), (2627829289/5000000000 : ℝ), (-496419157/2500000000 : ℝ)] ![(22282578322427/50000000000000 : ℝ), (43260226238489/100000000000000 : ℝ), (6087308553407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336059003/625000000 : ℝ)|^551 ≤ (22282578322427/50000000000000 : ℝ)^423
        have hw : |(336059003/625000000 : ℝ)|=(336059003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627829289/5000000000 : ℝ)|^551 ≤ (43260226238489/100000000000000 : ℝ)^423
        have hw : |(2627829289/5000000000 : ℝ)|=(2627829289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496419157/2500000000 : ℝ)|^551 ≤ (6087308553407/50000000000000 : ℝ)^423
        have hw : |(-496419157/2500000000 : ℝ)|=(496419157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_box_15 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4124710187/10000000000 : ℝ)*x 0 + (54881193/125000000 : ℝ)*x 1 + (219524767/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124710187/10000000000 : ℝ)^551 ≤ (31550868035463/100000000000000 : ℝ)^423 := by
    have hnat : (4124710187 : ℕ)^551*100000000000000^423 ≤ 31550868035463^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124710187 10000000000 31550868035463 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54881193/125000000 : ℝ)^551 ≤ (855614162091/2500000000000 : ℝ)^423 := by
    have hnat : (54881193 : ℕ)^551*2500000000000^423 ≤ 855614162091^423*125000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54881193 125000000 855614162091 2500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219524767/500000000 : ℝ)^551 ≤ (34224565468243/100000000000000 : ℝ)^423 := by
    have hnat : (219524767 : ℕ)^551*100000000000000^423 ≤ 34224565468243^423*500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219524767 500000000 34224565468243 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124710187/10000000000 : ℝ), (54881193/125000000 : ℝ), (219524767/500000000 : ℝ)] ![(31550868035463/100000000000000 : ℝ), (855614162091/2500000000000 : ℝ), (34224565468243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124710187/10000000000 : ℝ)|^551 ≤ (31550868035463/100000000000000 : ℝ)^423
        have hw : |(4124710187/10000000000 : ℝ)|=(4124710187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54881193/125000000 : ℝ)|^551 ≤ (855614162091/2500000000000 : ℝ)^423
        have hw : |(54881193/125000000 : ℝ)|=(54881193/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219524767/500000000 : ℝ)|^551 ≤ (34224565468243/100000000000000 : ℝ)^423
        have hw : |(219524767/500000000 : ℝ)|=(219524767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1966/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59151/100000 : ℝ) ∧ (80553/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21189/25000 : ℝ) := by
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
  have lower0 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11379/100000 : ℝ) ^ (4407/1024 : ℝ) ≤ (4332263707770637/50000000000000000000 : ℝ) := by
    have hpowers : (11379/100000 : ℝ)^4407 ≤ (4332263707770637/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11379 : ℕ)^4407*50000000000000000000^1024 ≤ 4332263707770637^1024*100000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11379 100000 4332263707770637 50000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11379/100000 : ℝ)) (X := (4332263707770637/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (4407/1024 : ℝ) ≤ (26591785687156829/100000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^4407 ≤ (26591785687156829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7383 : ℕ)^4407*100000000000000000000^1024 ≤ 26591785687156829^1024*50000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 26591785687156829 100000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (26591785687156829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004332263707770637/25000000000000000000 : ℝ) ≤ (10000402627002607/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (25004332263707770637/25000000000000000000 : ℝ)^1024 ≤ (10000402627002607/10000000000000000 : ℝ)^4407 := by
      have hnat : (25004332263707770637 : ℕ)^1024*10000000000000000^4407 ≤ 10000402627002607^4407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004332263707770637 25000000000000000000 10000402627002607 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000402627002607/10000000000000000 : ℝ)) (X := (25004332263707770637/25000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035256313102698103/100000000000000000000 : ℝ) ≤ (1000081909644209/1000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (100035256313102698103/100000000000000000000 : ℝ)^1024 ≤ (1000081909644209/1000000000000000 : ℝ)^4407 := by
      have hnat : (100035256313102698103 : ℕ)^1024*1000000000000000^4407 ≤ 1000081909644209^4407*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035256313102698103 100000000000000000000 1000081909644209 1000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000081909644209/1000000000000000 : ℝ)) (X := (100035256313102698103/100000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026591785687156829/50000000000000000000 : ℝ) ≤ (10001235565881573/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50026591785687156829/50000000000000000000 : ℝ)^1024 ≤ (10001235565881573/10000000000000000 : ℝ)^4407 := by
      have hnat : (50026591785687156829 : ℕ)^1024*10000000000000000^4407 ≤ 10001235565881573^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026591785687156829 50000000000000000000 10001235565881573 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001235565881573/10000000000000000 : ℝ)) (X := (50026591785687156829/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4332263707770637/50000000000000000000 : ℝ) ≤ ((2257459045743605053/2258000000000000000 : ℝ)+2*(416469439483/338700000000000 : ℝ)*(11379/100000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (2257459045743605053/2258000000000000000 : ℝ)+2*(416469439483/338700000000000 : ℝ)*(11379/100000 : ℝ)=(10000402627002607/10000000000000000 : ℝ) by norm_num, show 1+2*(4332263707770637/50000000000000000000 : ℝ)=(25004332263707770637/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26591785687156829/100000000000000000000 : ℝ)+(4332263707770637/50000000000000000000 : ℝ) ≤ ((2257459045743605053/2258000000000000000 : ℝ)+(416469439483/338700000000000 : ℝ)*((7383/50000 : ℝ)+(11379/100000 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (2257459045743605053/2258000000000000000 : ℝ)+(416469439483/338700000000000 : ℝ)*((7383/50000 : ℝ)+(11379/100000 : ℝ))=(1000081909644209/1000000000000000 : ℝ) by norm_num, show 1+(26591785687156829/100000000000000000000 : ℝ)+(4332263707770637/50000000000000000000 : ℝ)=(100035256313102698103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26591785687156829/100000000000000000000 : ℝ) ≤ ((2257459045743605053/2258000000000000000 : ℝ)+2*(416469439483/338700000000000 : ℝ)*(7383/50000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (2257459045743605053/2258000000000000000 : ℝ)+2*(416469439483/338700000000000 : ℝ)*(7383/50000 : ℝ)=(10001235565881573/10000000000000000 : ℝ) by norm_num, show 1+2*(26591785687156829/100000000000000000000 : ℝ)=(50026591785687156829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2257459045743605053/2258000000000000000 : ℝ)*(X 1 0+X 2 0)+(416469439483/338700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (2257459045743605053/2258000000000000000 : ℝ)) (alpha := (416469439483/338700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2257459045743605053/2258000000000000000 : ℝ)*(X 0 1+X 2 1)+(416469439483/338700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (2257459045743605053/2258000000000000000 : ℝ)) (alpha := (416469439483/338700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2257459045743605053/2258000000000000000 : ℝ)*(X 0 2+X 1 2)+(416469439483/338700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (2257459045743605053/2258000000000000000 : ℝ)) (alpha := (416469439483/338700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1796520241/10000000000 : ℝ)*X 0 0+(215417603/400000000 : ℝ)*X 0 1+(2692720151/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286187311/10000000000 : ℝ)*X 1 0+(-96647707/500000000 : ℝ)*X 1 1+(2692720343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660773489/1250000000 : ℝ)*X 2 0+(5385440279/10000000000 : ℝ)*X 2 1+(-48323847/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2222784333/5000000000 : ℝ)*X 0 0+(4230357279/10000000000 : ℝ)*X 0 1+(846071537/2000000000 : ℝ)*X 0 2+(2222784333/5000000000 : ℝ)*X 1 0+(4230357279/10000000000 : ℝ)*X 1 1+(846071537/2000000000 : ℝ)*X 1 2+(2222784333/5000000000 : ℝ)*X 2 0+(4230357279/10000000000 : ℝ)*X 2 1+(846071537/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105892527/500000000 : ℝ)*X 0 0+(5266793383/10000000000 : ℝ)*X 0 1+(5266793287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369158863/10000000000 : ℝ)*X 1 0+(-1981243683/10000000000 : ℝ)*X 1 1+(2633396649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((8389311/15625000 : ℝ)*X 2 0+(658349151/1250000000 : ℝ)*X 2 1+(-495310891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4152650251/10000000000 : ℝ)*X 0 0+(2188383113/5000000000 : ℝ)*X 0 1+(4376766441/10000000000 : ℝ)*X 0 2+(4152650251/10000000000 : ℝ)*X 1 0+(2188383113/5000000000 : ℝ)*X 1 1+(4376766441/10000000000 : ℝ)*X 1 2+(4152650251/10000000000 : ℝ)*X 2 0+(2188383113/5000000000 : ℝ)*X 2 1+(4376766441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-512532133/2500000000 : ℝ)*X 0 0+(5184641639/10000000000 : ℝ)*X 0 1+(2699701327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276420859/10000000000 : ℝ)*X 1 0+(-1927146273/10000000000 : ℝ)*X 1 1+(53994017/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319105109/2500000000 : ℝ)*X 2 0+(67492521/125000000 : ℝ)*X 2 1+(-616687/3200000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((223974087/500000000 : ℝ)*X 0 0+(4213113883/10000000000 : ℝ)*X 0 1+(2106556997/5000000000 : ℝ)*X 0 2+(223974087/500000000 : ℝ)*X 1 0+(4213113883/10000000000 : ℝ)*X 1 1+(2106556997/5000000000 : ℝ)*X 1 2+(223974087/500000000 : ℝ)*X 2 0+(4213113883/10000000000 : ℝ)*X 2 1+(2106556997/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1864391129/10000000000 : ℝ)*X 0 0+(5465603847/10000000000 : ℝ)*X 0 1+(525565853/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5376944099/10000000000 : ℝ)*X 1 0+(-397135319/2000000000 : ℝ)*X 1 1+(5255658551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((336059003/625000000 : ℝ)*X 2 0+(2627829289/5000000000 : ℝ)*X 2 1+(-496419157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4124710187/10000000000 : ℝ)*X 0 0+(54881193/125000000 : ℝ)*X 0 1+(219524767/500000000 : ℝ)*X 0 2+(4124710187/10000000000 : ℝ)*X 1 0+(54881193/125000000 : ℝ)*X 1 1+(219524767/500000000 : ℝ)*X 1 2+(4124710187/10000000000 : ℝ)*X 2 0+(54881193/125000000 : ℝ)*X 2 1+(219524767/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1966/3125 : ℝ) ≤ (-7102431951981265110475266715419/11290000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18581751/50000000000000 : ℝ)*(upper0) + (5927637/12500000000000 : ℝ)*(lower1) + (42450169/50000000000000 : ℝ)*(lower2) + (303746208932141/10000000000000 : ℝ)*(major0) + (303746208932141/10000000000000 : ℝ)*(major1) + (303746208932141/10000000000000 : ℝ)*(major2) + (1015923637/25000000000000 : ℝ)*(sp1) + (689512263/25000000000000 : ℝ)*(sp2) + (418458022067409/10000000000000 : ℝ)*(sp4) + (2092288281967757/50000000000000 : ℝ)*(sp5) + (4184577869581009/100000000000000 : ℝ)*(sp6) + (477826064273591/25000000000000 : ℝ)*(sp7) + (406955971/100000000000000 : ℝ)*(sp8) + (2244465707/25000000000000 : ℝ)*(sp15) + (238914154369649/12500000000000 : ℝ)*(f.failure) + (2092290313815031/50000000000000 : ℝ)*(f.sum) + (336827858437/338700000000000000000000000 : ℝ)*base65 + (6419423399165419/67740000000000000000000000000000 : ℝ)*base67 + (68309167699265419/67740000000000000000000000000000 : ℝ)*base69 + (220785799118214581/67740000000000000000000000000000 : ℝ)*base72 + (137719040599/105843750000000000000000000 : ℝ)*base74 + (81368068447374581/67740000000000000000000000000000 : ℝ)*base76 + (571833859591025419/67740000000000000000000000000000 : ℝ)*base77 + (371691831065825419/67740000000000000000000000000000 : ℝ)*base79 + (7603345229/338700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (981569/625000000000000000000 : ℝ)*base89 + (981569/625000000000000000000 : ℝ)*base91 + (981569/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59151/100000 : ℝ) ≤ (6678484001338375255960870906173/11290000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17010581/100000000000000 : ℝ)*(upper0) + (42456981/50000000000000 : ℝ)*(lower1) + (27018363/100000000000000 : ℝ)*(lower3) + (181549097/100000000000000 : ℝ)*(upper4) + (5178311/5000000000000 : ℝ)*(upper5) + (310970755501449/10000000000000 : ℝ)*(major0) + (310970755501449/10000000000000 : ℝ)*(major1) + (310970755501449/10000000000000 : ℝ)*(major2) + (265182728511579/6250000000000 : ℝ)*(sp0) + (2121457401839713/50000000000000 : ℝ)*(sp1) + (265182728511579/6250000000000 : ℝ)*(sp2) + (978382679235453/50000000000000 : ℝ)*(sp3) + (4426252919/50000000000000 : ℝ)*(sp5) + (1620609051/20000000000000 : ℝ)*(sp11) + (1956773461516161/100000000000000 : ℝ)*(f.failure) + (265182728511579/6250000000000 : ℝ)*(f.sum) + (461172452631/112900000000000000000000000 : ℝ)*base66 + (245792364575618203/22580000000000000000000000000000 : ℝ)*base68 + (304305410413638203/22580000000000000000000000000000 : ℝ)*base70 + (226489310491078203/22580000000000000000000000000000 : ℝ)*base72 + (18178362592327/1129000000000000000000000000 : ℝ)*base74 + (282666775852198203/22580000000000000000000000000000 : ℝ)*base76 + (201638283818118203/22580000000000000000000000000000 : ℝ)*base78 + (1055551669844098203/22580000000000000000000000000000 : ℝ)*base80 + (1698313655731/564500000000000000000000000 : ℝ)*base82 + (35869041/5000000000000000000000 : ℝ)*base89 + (35869041/5000000000000000000000 : ℝ)*base91 + (35869041/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80553/100000 : ℝ) ≤ (9094667991898099815732881686383/11290000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38513/12500000000000 : ℝ)*(upper1) + (132464619/50000000000000 : ℝ)*(upper2) + (43144611/20000000000000 : ℝ)*(lower5) + (341654152024537/10000000000000 : ℝ)*(major0) + (341654152024537/10000000000000 : ℝ)*(major1) + (341654152024537/10000000000000 : ℝ)*(major2) + (69589463723/100000000000000 : ℝ)*(sp1) + (54039030663/50000000000000 : ℝ)*(sp3) + (92770019/500000000000 : ℝ)*(sp4) + (931268904993507/20000000000000 : ℝ)*(sp8) + (4656314013572209/100000000000000 : ℝ)*(sp9) + (1164095900758983/25000000000000 : ℝ)*(sp10) + (2149739667654771/100000000000000 : ℝ)*(sp11) + (20524064597/100000000000000 : ℝ)*(sp12) + (2149847745716097/100000000000000 : ℝ)*(f.failure) + (1164095900758983/25000000000000 : ℝ)*(f.sum) + (2700831853159/3387000000000000000000000000 : ℝ)*base66 + (439674937866563617/67740000000000000000000000000000 : ℝ)*base68 + (537662129033183617/67740000000000000000000000000000 : ℝ)*base70 + (455796473202623617/67740000000000000000000000000000 : ℝ)*base72 + (180843206963/846750000000000000000000000 : ℝ)*base73 + (67716812841096383/67740000000000000000000000000000 : ℝ)*base75 + (2337843127765056383/67740000000000000000000000000000 : ℝ)*base77 + (292029906597203617/67740000000000000000000000000000 : ℝ)*base80 + (11065528162267/1693500000000000000000000000 : ℝ)*base81 + (29376143/5000000000000000000000 : ℝ)*base90 + (29376143/5000000000000000000000 : ℝ)*base92 + (29376143/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21189/25000 : ℝ) ≤ (-47843188809613859673810499068669/56450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16697717/100000000000000 : ℝ)*(lower0) + (25662511/100000000000000 : ℝ)*(upper3) + (3918567/25000000000000 : ℝ)*(lower4) + (1727114471388891/50000000000000 : ℝ)*(major0) + (1727114471388891/50000000000000 : ℝ)*(major1) + (1727114471388891/50000000000000 : ℝ)*(major2) + (1006954913/100000000000000 : ℝ)*(sp0) + (25800624407/100000000000000 : ℝ)*(sp5) + (7365834261/50000000000000 : ℝ)*(sp6) + (2591662321/25000000000000 : ℝ)*(sp7) + (2381572757351323/50000000000000 : ℝ)*(sp12) + (74423761266143/1562500000000 : ℝ)*(sp13) + (4763131789989037/100000000000000 : ℝ)*(sp14) + (2173552068290709/100000000000000 : ℝ)*(sp15) + (2173562434939993/100000000000000 : ℝ)*(f.failure) + (4763146521657559/100000000000000 : ℝ)*(f.sum) + (965415239299/2822500000000000000000000000 : ℝ)*base66 + (236435628589786223/112900000000000000000000000000000 : ℝ)*base67 + (382767392675686223/112900000000000000000000000000000 : ℝ)*base69 + (120553649247713777/112900000000000000000000000000000 : ℝ)*base72 + (6987709407567/5645000000000000000000000000 : ℝ)*base73 + (469075724652886223/112900000000000000000000000000000 : ℝ)*base75 + (126672983582013777/112900000000000000000000000000000 : ℝ)*base78 + (34910220897286223/112900000000000000000000000000000 : ℝ)*base79 + (7362503216601/2822500000000000000000000000 : ℝ)*base81 + (26080567/5000000000000000000000 : ℝ)*base90 + (26080567/5000000000000000000000 : ℝ)*base92 + (26080567/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1448_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1966/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(59151/100000 : ℝ) else (80553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21189/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1448_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1448_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1966/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(59151/100000 : ℝ) else (80553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21189/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1448_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1448_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1448_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1966/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(59151/100000 : ℝ) else (80553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21189/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1448_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
