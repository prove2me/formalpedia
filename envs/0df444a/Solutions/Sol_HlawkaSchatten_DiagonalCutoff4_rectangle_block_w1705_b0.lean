-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1705_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:55.134327+00:00
-- url     : https://prove2.me/submissions/54f4e87a-15e0-4561-8bfc-2298c69d724a

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
theorem support_rectangle_w1705_s0_0 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-675720867/5000000000 : ℝ)*x 0 + (1426991053/2500000000 : ℝ)*x 1 + (198193771/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675720867/5000000000 : ℝ)^5263 ≤ (1666698923661/20000000000000 : ℝ)^4239 := by
    have hnat : (675720867 : ℕ)^5263*20000000000000^4239 ≤ 1666698923661^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675720867 5000000000 1666698923661 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426991053/2500000000 : ℝ)^5263 ≤ (49848866783623/100000000000000 : ℝ)^4239 := by
    have hnat : (1426991053 : ℕ)^5263*100000000000000^4239 ≤ 49848866783623^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426991053 2500000000 49848866783623 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198193771/400000000 : ℝ)^5263 ≤ (2090881929051/5000000000000 : ℝ)^4239 := by
    have hnat : (198193771 : ℕ)^5263*5000000000000^4239 ≤ 2090881929051^4239*400000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198193771 400000000 2090881929051 5000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-675720867/5000000000 : ℝ), (1426991053/2500000000 : ℝ), (198193771/400000000 : ℝ)] ![(1666698923661/20000000000000 : ℝ), (49848866783623/100000000000000 : ℝ), (2090881929051/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-675720867/5000000000 : ℝ)|^5263 ≤ (1666698923661/20000000000000 : ℝ)^4239
        have hw : |(-675720867/5000000000 : ℝ)|=(675720867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426991053/2500000000 : ℝ)|^5263 ≤ (49848866783623/100000000000000 : ℝ)^4239
        have hw : |(1426991053/2500000000 : ℝ)|=(1426991053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198193771/400000000 : ℝ)|^5263 ≤ (2090881929051/5000000000000 : ℝ)^4239
        have hw : |(198193771/400000000 : ℝ)|=(198193771/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s0_1 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2703895477/5000000000 : ℝ)*x 0 + (-879963339/5000000000 : ℝ)*x 1 + (2477421813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703895477/5000000000 : ℝ)^5263 ≤ (9323016779937/20000000000000 : ℝ)^4239 := by
    have hnat : (2703895477 : ℕ)^5263*20000000000000^4239 ≤ 9323016779937^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703895477 5000000000 9323016779937 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879963339/5000000000 : ℝ)^5263 ≤ (5783642150751/50000000000000 : ℝ)^4239 := by
    have hnat : (879963339 : ℕ)^5263*50000000000000^4239 ≤ 5783642150751^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879963339 5000000000 5783642150751 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2477421813/5000000000 : ℝ)^5263 ≤ (10454407945117/25000000000000 : ℝ)^4239 := by
    have hnat : (2477421813 : ℕ)^5263*25000000000000^4239 ≤ 10454407945117^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2477421813 5000000000 10454407945117 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703895477/5000000000 : ℝ), (-879963339/5000000000 : ℝ), (2477421813/5000000000 : ℝ)] ![(9323016779937/20000000000000 : ℝ), (5783642150751/50000000000000 : ℝ), (10454407945117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703895477/5000000000 : ℝ)|^5263 ≤ (9323016779937/20000000000000 : ℝ)^4239
        have hw : |(2703895477/5000000000 : ℝ)|=(2703895477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-879963339/5000000000 : ℝ)|^5263 ≤ (5783642150751/50000000000000 : ℝ)^4239
        have hw : |(-879963339/5000000000 : ℝ)|=(879963339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2477421813/5000000000 : ℝ)|^5263 ≤ (10454407945117/25000000000000 : ℝ)^4239
        have hw : |(2477421813/5000000000 : ℝ)|=(2477421813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s0_2 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675973737/1250000000 : ℝ)*x 0 + (2477422193/5000000000 : ℝ)*x 1 + (-175992709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675973737/1250000000 : ℝ)^5263 ≤ (46615072576667/100000000000000 : ℝ)^4239 := by
    have hnat : (675973737 : ℕ)^5263*100000000000000^4239 ≤ 46615072576667^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675973737 1250000000 46615072576667 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2477422193/5000000000 : ℝ)^5263 ≤ (20908819872067/50000000000000 : ℝ)^4239 := by
    have hnat : (2477422193 : ℕ)^5263*50000000000000^4239 ≤ 20908819872067^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2477422193 5000000000 20908819872067 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175992709/1000000000 : ℝ)^5263 ≤ (231345753271/2000000000000 : ℝ)^4239 := by
    have hnat : (175992709 : ℕ)^5263*2000000000000^4239 ≤ 231345753271^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175992709 1000000000 231345753271 2000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675973737/1250000000 : ℝ), (2477422193/5000000000 : ℝ), (-175992709/1000000000 : ℝ)] ![(46615072576667/100000000000000 : ℝ), (20908819872067/50000000000000 : ℝ), (231345753271/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675973737/1250000000 : ℝ)|^5263 ≤ (46615072576667/100000000000000 : ℝ)^4239
        have hw : |(675973737/1250000000 : ℝ)|=(675973737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2477422193/5000000000 : ℝ)|^5263 ≤ (20908819872067/50000000000000 : ℝ)^4239
        have hw : |(2477422193/5000000000 : ℝ)|=(2477422193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175992709/1000000000 : ℝ)|^5263 ≤ (231345753271/2000000000000 : ℝ)^4239
        have hw : |(-175992709/1000000000 : ℝ)|=(175992709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s0_3 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (252736297/625000000 : ℝ)*x 0 + (611198413/2000000000 : ℝ)*x 1 + (1042914421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252736297/625000000 : ℝ)^5263 ≤ (32493814300691/100000000000000 : ℝ)^4239 := by
    have hnat : (252736297 : ℕ)^5263*100000000000000^4239 ≤ 32493814300691^4239*625000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252736297 625000000 32493814300691 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611198413/2000000000 : ℝ)^5263 ≤ (22949979097787/100000000000000 : ℝ)^4239 := by
    have hnat : (611198413 : ℕ)^5263*100000000000000^4239 ≤ 22949979097787^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611198413 2000000000 22949979097787 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042914421/2000000000 : ℝ)^5263 ≤ (44556206585637/100000000000000 : ℝ)^4239 := by
    have hnat : (1042914421 : ℕ)^5263*100000000000000^4239 ≤ 44556206585637^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042914421 2000000000 44556206585637 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252736297/625000000 : ℝ), (611198413/2000000000 : ℝ), (1042914421/2000000000 : ℝ)] ![(32493814300691/100000000000000 : ℝ), (22949979097787/100000000000000 : ℝ), (44556206585637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252736297/625000000 : ℝ)|^5263 ≤ (32493814300691/100000000000000 : ℝ)^4239
        have hw : |(252736297/625000000 : ℝ)|=(252736297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(611198413/2000000000 : ℝ)|^5263 ≤ (22949979097787/100000000000000 : ℝ)^4239
        have hw : |(611198413/2000000000 : ℝ)|=(611198413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042914421/2000000000 : ℝ)|^5263 ≤ (44556206585637/100000000000000 : ℝ)^4239
        have hw : |(1042914421/2000000000 : ℝ)|=(1042914421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s0_4 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1353190939/10000000000 : ℝ)*x 0 + (248672611/500000000 : ℝ)*x 1 + (1137746059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353190939/10000000000 : ℝ)^5263 ≤ (2086722139687/25000000000000 : ℝ)^4239 := by
    have hnat : (1353190939 : ℕ)^5263*25000000000000^4239 ≤ 2086722139687^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353190939 10000000000 2086722139687 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248672611/500000000 : ℝ)^5263 ≤ (10503177610579/25000000000000 : ℝ)^4239 := by
    have hnat : (248672611 : ℕ)^5263*25000000000000^4239 ≤ 10503177610579^4239*500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248672611 500000000 10503177610579 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137746059/2000000000 : ℝ)^5263 ≤ (49640400993861/100000000000000 : ℝ)^4239 := by
    have hnat : (1137746059 : ℕ)^5263*100000000000000^4239 ≤ 49640400993861^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137746059 2000000000 49640400993861 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1353190939/10000000000 : ℝ), (248672611/500000000 : ℝ), (1137746059/2000000000 : ℝ)] ![(2086722139687/25000000000000 : ℝ), (10503177610579/25000000000000 : ℝ), (49640400993861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1353190939/10000000000 : ℝ)|^5263 ≤ (2086722139687/25000000000000 : ℝ)^4239
        have hw : |(-1353190939/10000000000 : ℝ)|=(1353190939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(248672611/500000000 : ℝ)|^5263 ≤ (10503177610579/25000000000000 : ℝ)^4239
        have hw : |(248672611/500000000 : ℝ)|=(248672611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1137746059/2000000000 : ℝ)|^5263 ≤ (49640400993861/100000000000000 : ℝ)^4239
        have hw : |(1137746059/2000000000 : ℝ)|=(1137746059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s0_5 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203611857/10000000000 : ℝ)*x 0 + (-256510101/2500000000 : ℝ)*x 1 + (1422182573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203611857/10000000000 : ℝ)^5263 ≤ (44439962854793/100000000000000 : ℝ)^4239 := by
    have hnat : (5203611857 : ℕ)^5263*100000000000000^4239 ≤ 44439962854793^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203611857 10000000000 44439962854793 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256510101/2500000000 : ℝ)^5263 ≤ (5919636168901/100000000000000 : ℝ)^4239 := by
    have hnat : (256510101 : ℕ)^5263*100000000000000^4239 ≤ 5919636168901^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256510101 2500000000 5919636168901 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1422182573/2500000000 : ℝ)^5263 ≤ (49640400961359/100000000000000 : ℝ)^4239 := by
    have hnat : (1422182573 : ℕ)^5263*100000000000000^4239 ≤ 49640400961359^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422182573 2500000000 49640400961359 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203611857/10000000000 : ℝ), (-256510101/2500000000 : ℝ), (1422182573/2500000000 : ℝ)] ![(44439962854793/100000000000000 : ℝ), (5919636168901/100000000000000 : ℝ), (49640400961359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203611857/10000000000 : ℝ)|^5263 ≤ (44439962854793/100000000000000 : ℝ)^4239
        have hw : |(5203611857/10000000000 : ℝ)|=(5203611857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256510101/2500000000 : ℝ)|^5263 ≤ (5919636168901/100000000000000 : ℝ)^4239
        have hw : |(-256510101/2500000000 : ℝ)|=(256510101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1422182573/2500000000 : ℝ)|^5263 ≤ (49640400961359/100000000000000 : ℝ)^4239
        have hw : |(1422182573/2500000000 : ℝ)|=(1422182573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s0_6 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203611697/10000000000 : ℝ)*x 0 + (1422182711/2500000000 : ℝ)*x 1 + (-205207961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203611697/10000000000 : ℝ)^5263 ≤ (22219980579137/50000000000000 : ℝ)^4239 := by
    have hnat : (5203611697 : ℕ)^5263*50000000000000^4239 ≤ 22219980579137^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203611697 10000000000 22219980579137 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422182711/2500000000 : ℝ)^5263 ≤ (24820203470871/50000000000000 : ℝ)^4239 := by
    have hnat : (1422182711 : ℕ)^5263*50000000000000^4239 ≤ 24820203470871^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422182711 2500000000 24820203470871 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205207961/2000000000 : ℝ)^5263 ≤ (5919631878209/100000000000000 : ℝ)^4239 := by
    have hnat : (205207961 : ℕ)^5263*100000000000000^4239 ≤ 5919631878209^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205207961 2000000000 5919631878209 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203611697/10000000000 : ℝ), (1422182711/2500000000 : ℝ), (-205207961/2000000000 : ℝ)] ![(22219980579137/50000000000000 : ℝ), (24820203470871/50000000000000 : ℝ), (5919631878209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203611697/10000000000 : ℝ)|^5263 ≤ (22219980579137/50000000000000 : ℝ)^4239
        have hw : |(5203611697/10000000000 : ℝ)|=(5203611697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1422182711/2500000000 : ℝ)|^5263 ≤ (24820203470871/50000000000000 : ℝ)^4239
        have hw : |(1422182711/2500000000 : ℝ)|=(1422182711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-205207961/2000000000 : ℝ)|^5263 ≤ (5919631878209/100000000000000 : ℝ)^4239
        have hw : |(-205207961/2000000000 : ℝ)|=(205207961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s0_7 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4048790559/10000000000 : ℝ)*x 0 + (2580619327/5000000000 : ℝ)*x 1 + (622223591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4048790559/10000000000 : ℝ)^5263 ≤ (6508760534781/20000000000000 : ℝ)^4239 := by
    have hnat : (4048790559 : ℕ)^5263*20000000000000^4239 ≤ 6508760534781^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048790559 10000000000 6508760534781 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2580619327/5000000000 : ℝ)^5263 ≤ (43991112265919/100000000000000 : ℝ)^4239 := by
    have hnat : (2580619327 : ℕ)^5263*100000000000000^4239 ≤ 43991112265919^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580619327 5000000000 43991112265919 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622223591/2000000000 : ℝ)^5263 ≤ (4693017008751/20000000000000 : ℝ)^4239 := by
    have hnat : (622223591 : ℕ)^5263*20000000000000^4239 ≤ 4693017008751^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622223591 2000000000 4693017008751 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4048790559/10000000000 : ℝ), (2580619327/5000000000 : ℝ), (622223591/2000000000 : ℝ)] ![(6508760534781/20000000000000 : ℝ), (43991112265919/100000000000000 : ℝ), (4693017008751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4048790559/10000000000 : ℝ)|^5263 ≤ (6508760534781/20000000000000 : ℝ)^4239
        have hw : |(4048790559/10000000000 : ℝ)|=(4048790559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2580619327/5000000000 : ℝ)|^5263 ≤ (43991112265919/100000000000000 : ℝ)^4239
        have hw : |(2580619327/5000000000 : ℝ)|=(2580619327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622223591/2000000000 : ℝ)|^5263 ≤ (4693017008751/20000000000000 : ℝ)^4239
        have hw : |(622223591/2000000000 : ℝ)|=(622223591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1705_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5903/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11043/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5255/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5255 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5255*1^1024 ≤ 0^1024*1^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5255/1024 : ℝ) ≤ (181496041855088287/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5255 ≤ (181496041855088287/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5255*20000000000000000000^1024 ≤ 181496041855088287^1024*5^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 181496041855088287 20000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (181496041855088287/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5255 := by
      have hnat : (1 : ℕ)^1024*1^5255 ≤ 1^5255*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20181496041855088287/20000000000000000000 : ℝ) ≤ (5008809546632649/5000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (20181496041855088287/20000000000000000000 : ℝ)^1024 ≤ (5008809546632649/5000000000000000 : ℝ)^5255 := by
      have hnat : (20181496041855088287 : ℕ)^1024*5000000000000000^5255 ≤ 5008809546632649^5255*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20181496041855088287 20000000000000000000 5008809546632649 5000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008809546632649/5000000000000000 : ℝ)) (X := (20181496041855088287/20000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10181496041855088287/10000000000000000000 : ℝ) ≤ (2508809546632649/2500000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (10181496041855088287/10000000000000000000 : ℝ)^1024 ≤ (2508809546632649/2500000000000000 : ℝ)^5255 := by
      have hnat : (10181496041855088287 : ℕ)^1024*2500000000000000^5255 ≤ 2508809546632649^5255*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10181496041855088287 10000000000000000000 2508809546632649 2500000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508809546632649/2500000000000000 : ℝ)) (X := (10181496041855088287/10000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8809546632649/2000000000000000 : ℝ)*(0 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8809546632649/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(181496041855088287/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8809546632649/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5255/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8809546632649/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5008809546632649/5000000000000000 : ℝ) by norm_num, show 1+(181496041855088287/20000000000000000000 : ℝ)+(0 : ℝ)=(20181496041855088287/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(181496041855088287/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8809546632649/2000000000000000 : ℝ)*(2/5 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8809546632649/2000000000000000 : ℝ)*(2/5 : ℝ)=(2508809546632649/2500000000000000 : ℝ) by norm_num, show 1+2*(181496041855088287/20000000000000000000 : ℝ)=(10181496041855088287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8809546632649/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8809546632649/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8809546632649/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8809546632649/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8809546632649/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8809546632649/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-675720867/5000000000 : ℝ)*X 0 0+(1426991053/2500000000 : ℝ)*X 0 1+(198193771/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2703895477/5000000000 : ℝ)*X 1 0+(-879963339/5000000000 : ℝ)*X 1 1+(2477421813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((675973737/1250000000 : ℝ)*X 2 0+(2477422193/5000000000 : ℝ)*X 2 1+(-175992709/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((252736297/625000000 : ℝ)*X 0 0+(611198413/2000000000 : ℝ)*X 0 1+(1042914421/2000000000 : ℝ)*X 0 2+(252736297/625000000 : ℝ)*X 1 0+(611198413/2000000000 : ℝ)*X 1 1+(1042914421/2000000000 : ℝ)*X 1 2+(252736297/625000000 : ℝ)*X 2 0+(611198413/2000000000 : ℝ)*X 2 1+(1042914421/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1353190939/10000000000 : ℝ)*X 0 0+(248672611/500000000 : ℝ)*X 0 1+(1137746059/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5203611857/10000000000 : ℝ)*X 1 0+(-256510101/2500000000 : ℝ)*X 1 1+(1422182573/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5203611697/10000000000 : ℝ)*X 2 0+(1422182711/2500000000 : ℝ)*X 2 1+(-205207961/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4048790559/10000000000 : ℝ)*X 0 0+(2580619327/5000000000 : ℝ)*X 0 1+(622223591/2000000000 : ℝ)*X 0 2+(4048790559/10000000000 : ℝ)*X 1 0+(2580619327/5000000000 : ℝ)*X 1 1+(622223591/2000000000 : ℝ)*X 1 2+(4048790559/10000000000 : ℝ)*X 2 0+(2580619327/5000000000 : ℝ)*X 2 1+(622223591/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (254566674594098570402661/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170236989/100000000000000 : ℝ)*(base1) + (1111409227/100000000000000 : ℝ)*(base19) + (851630633/100000000000000 : ℝ)*(base23) + (2458463/1000000000000 : ℝ)*(upper3) + (5644751/20000000000000 : ℝ)*(upper5) + (895542755693937/100000000000000 : ℝ)*(major0) + (895542755693937/100000000000000 : ℝ)*(major1) + (895542755693937/100000000000000 : ℝ)*(major2) + (1327814113703829/100000000000000 : ℝ)*(sp0) + (1327814799011621/100000000000000 : ℝ)*(sp1) + (663907529395107/50000000000000 : ℝ)*(sp2) + (28954255276211/6250000000000 : ℝ)*(sp3) + (1966954007/100000000000000 : ℝ)*(sp4) + (1176599537/100000000000000 : ℝ)*(sp7) + (231634715627951/50000000000000 : ℝ)*(f.failure) + (1327815910420847/100000000000000 : ℝ)*(f.sum) + (192201627949113/100000000000000000000000000000 : ℝ)*base65 + (472256030349113/200000000000000000000000000000 : ℝ)*base67 + (73716744549113/200000000000000000000000000000 : ℝ)*base69 + (113029941749113/200000000000000000000000000000 : ℝ)*base71 + (328646655549113/100000000000000000000000000000 : ℝ)*base73 + (1276884596650887/200000000000000000000000000000 : ℝ)*base76 + (1499389679749113/200000000000000000000000000000 : ℝ)*base77 + (395389032850887/200000000000000000000000000000 : ℝ)*base80 + (108329989950887/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5059423/500000000000000000000 : ℝ)*base90 + (5059423/500000000000000000000 : ℝ)*base92 + (5059423/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181853927557794200998509/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403874727/20000000000000 : ℝ)*(base19) + (43769409/2000000000000 : ℝ)*(base23) + (19315527/25000000000000 : ℝ)*(upper2) + (43357699/12500000000000 : ℝ)*(upper3) + (158702207/50000000000000 : ℝ)*(upper5) + (471458320678349/50000000000000 : ℝ)*(major0) + (471458320678349/50000000000000 : ℝ)*(major1) + (471458320678349/50000000000000 : ℝ)*(major2) + (713087529/10000000000000 : ℝ)*(sp1) + (8751950711/100000000000000 : ℝ)*(sp2) + (279611364954503/20000000000000 : ℝ)*(sp4) + (139804767452359/10000000000000 : ℝ)*(sp5) + (699022942175677/50000000000000 : ℝ)*(sp6) + (487776215468973/100000000000000 : ℝ)*(sp7) + (487776215468973/100000000000000 : ℝ)*(f.failure) + (279611364954503/20000000000000 : ℝ)*(f.sum) + (178440825283499/50000000000000000000000000000 : ℝ)*base66 + (888863173383499/100000000000000000000000000000 : ℝ)*base68 + (419116823183499/100000000000000000000000000000 : ℝ)*base70 + (173577528883499/100000000000000000000000000000 : ℝ)*base72 + (249769877283499/50000000000000000000000000000 : ℝ)*base74 + (318631612683499/100000000000000000000000000000 : ℝ)*base76 + (478944579283499/100000000000000000000000000000 : ℝ)*base78 + (454691965583499/100000000000000000000000000000 : ℝ)*base80 + (108281771933499/50000000000000000000000000000 : ℝ)*base82 + (7827971/1000000000000000000000 : ℝ)*base89 + (7827971/1000000000000000000000 : ℝ)*base91 + (7827971/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1705_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5903/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1705_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1705_s1_0 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426299281/10000000000 : ℝ)*x 0 + (2744860393/5000000000 : ℝ)*x 1 + (2561939099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426299281/10000000000 : ℝ)^5263 ≤ (4455191500213/50000000000000 : ℝ)^4239 := by
    have hnat : (1426299281 : ℕ)^5263*50000000000000^4239 ≤ 4455191500213^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426299281 10000000000 4455191500213 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744860393/5000000000 : ℝ)^5263 ≤ (47493518768489/100000000000000 : ℝ)^4239 := by
    have hnat : (2744860393 : ℕ)^5263*100000000000000^4239 ≤ 47493518768489^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744860393 5000000000 47493518768489 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2561939099/5000000000 : ℝ)^5263 ≤ (8719219641523/20000000000000 : ℝ)^4239 := by
    have hnat : (2561939099 : ℕ)^5263*20000000000000^4239 ≤ 8719219641523^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561939099 5000000000 8719219641523 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426299281/10000000000 : ℝ), (2744860393/5000000000 : ℝ), (2561939099/5000000000 : ℝ)] ![(4455191500213/50000000000000 : ℝ), (47493518768489/100000000000000 : ℝ), (8719219641523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426299281/10000000000 : ℝ)|^5263 ≤ (4455191500213/50000000000000 : ℝ)^4239
        have hw : |(-1426299281/10000000000 : ℝ)|=(1426299281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744860393/5000000000 : ℝ)|^5263 ≤ (47493518768489/100000000000000 : ℝ)^4239
        have hw : |(2744860393/5000000000 : ℝ)|=(2744860393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2561939099/5000000000 : ℝ)|^5263 ≤ (8719219641523/20000000000000 : ℝ)^4239
        have hw : |(2561939099/5000000000 : ℝ)|=(2561939099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s1_1 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337413313/2500000000 : ℝ)*x 0 + (-8083487/50000000 : ℝ)*x 1 + (5123877359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337413313/2500000000 : ℝ)^5263 ≤ (22996843882823/50000000000000 : ℝ)^4239 := by
    have hnat : (1337413313 : ℕ)^5263*50000000000000^4239 ≤ 22996843882823^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337413313 2500000000 22996843882823 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8083487/50000000 : ℝ)^5263 ≤ (2602555720567/25000000000000 : ℝ)^4239 := by
    have hnat : (8083487 : ℕ)^5263*25000000000000^4239 ≤ 2602555720567^4239*50000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8083487 50000000 2602555720567 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123877359/10000000000 : ℝ)^5263 ≤ (8719217868923/20000000000000 : ℝ)^4239 := by
    have hnat : (5123877359 : ℕ)^5263*20000000000000^4239 ≤ 8719217868923^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123877359 10000000000 8719217868923 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337413313/2500000000 : ℝ), (-8083487/50000000 : ℝ), (5123877359/10000000000 : ℝ)] ![(22996843882823/50000000000000 : ℝ), (2602555720567/25000000000000 : ℝ), (8719217868923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337413313/2500000000 : ℝ)|^5263 ≤ (22996843882823/50000000000000 : ℝ)^4239
        have hw : |(1337413313/2500000000 : ℝ)|=(1337413313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8083487/50000000 : ℝ)|^5263 ≤ (2602555720567/25000000000000 : ℝ)^4239
        have hw : |(-8083487/50000000 : ℝ)|=(8083487/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123877359/10000000000 : ℝ)|^5263 ≤ (8719217868923/20000000000000 : ℝ)^4239
        have hw : |(5123877359/10000000000 : ℝ)|=(5123877359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s1_2 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349651903/10000000000 : ℝ)*x 0 + (5123878537/10000000000 : ℝ)*x 1 + (-404174411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349651903/10000000000 : ℝ)^5263 ≤ (5749209170739/12500000000000 : ℝ)^4239 := by
    have hnat : (5349651903 : ℕ)^5263*12500000000000^4239 ≤ 5749209170739^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349651903 10000000000 5749209170739 12500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5123878537/10000000000 : ℝ)^5263 ≤ (43596101788731/100000000000000 : ℝ)^4239 := by
    have hnat : (5123878537 : ℕ)^5263*100000000000000^4239 ≤ 43596101788731^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123878537 10000000000 43596101788731 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404174411/2500000000 : ℝ)^5263 ≤ (10410224832971/100000000000000 : ℝ)^4239 := by
    have hnat : (404174411 : ℕ)^5263*100000000000000^4239 ≤ 10410224832971^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404174411 2500000000 10410224832971 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349651903/10000000000 : ℝ), (5123878537/10000000000 : ℝ), (-404174411/2500000000 : ℝ)] ![(5749209170739/12500000000000 : ℝ), (43596101788731/100000000000000 : ℝ), (10410224832971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349651903/10000000000 : ℝ)|^5263 ≤ (5749209170739/12500000000000 : ℝ)^4239
        have hw : |(5349651903/10000000000 : ℝ)|=(5349651903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5123878537/10000000000 : ℝ)|^5263 ≤ (43596101788731/100000000000000 : ℝ)^4239
        have hw : |(5123878537/10000000000 : ℝ)|=(5123878537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404174411/2500000000 : ℝ)|^5263 ≤ (10410224832971/100000000000000 : ℝ)^4239
        have hw : |(-404174411/2500000000 : ℝ)|=(404174411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s1_3 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2054030021/5000000000 : ℝ)*x 0 + (144208129/400000000 : ℝ)*x 1 + (581721909/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054030021/5000000000 : ℝ)^5263 ≤ (33136330114571/100000000000000 : ℝ)^4239 := by
    have hnat : (2054030021 : ℕ)^5263*100000000000000^4239 ≤ 33136330114571^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054030021 5000000000 33136330114571 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144208129/400000000 : ℝ)^5263 ≤ (28177266703553/100000000000000 : ℝ)^4239 := by
    have hnat : (144208129 : ℕ)^5263*100000000000000^4239 ≤ 28177266703553^4239*400000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144208129 400000000 28177266703553 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (581721909/1250000000 : ℝ)^5263 ≤ (38686403168301/100000000000000 : ℝ)^4239 := by
    have hnat : (581721909 : ℕ)^5263*100000000000000^4239 ≤ 38686403168301^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581721909 1250000000 38686403168301 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2054030021/5000000000 : ℝ), (144208129/400000000 : ℝ), (581721909/1250000000 : ℝ)] ![(33136330114571/100000000000000 : ℝ), (28177266703553/100000000000000 : ℝ), (38686403168301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2054030021/5000000000 : ℝ)|^5263 ≤ (33136330114571/100000000000000 : ℝ)^4239
        have hw : |(2054030021/5000000000 : ℝ)|=(2054030021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(144208129/400000000 : ℝ)|^5263 ≤ (28177266703553/100000000000000 : ℝ)^4239
        have hw : |(144208129/400000000 : ℝ)|=(144208129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(581721909/1250000000 : ℝ)|^5263 ≤ (38686403168301/100000000000000 : ℝ)^4239
        have hw : |(581721909/1250000000 : ℝ)|=(581721909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s1_4 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-713248681/5000000000 : ℝ)*x 0 + (5128272681/10000000000 : ℝ)*x 1 + (685656873/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (713248681/5000000000 : ℝ)^5263 ≤ (445595970281/5000000000000 : ℝ)^4239 := by
    have hnat : (713248681 : ℕ)^5263*5000000000000^4239 ≤ 445595970281^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713248681 5000000000 445595970281 5000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128272681/10000000000 : ℝ)^5263 ≤ (21821262653077/50000000000000 : ℝ)^4239 := by
    have hnat : (5128272681 : ℕ)^5263*50000000000000^4239 ≤ 21821262653077^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128272681 10000000000 21821262653077 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685656873/1250000000 : ℝ)^5263 ≤ (11861388818257/25000000000000 : ℝ)^4239 := by
    have hnat : (685656873 : ℕ)^5263*25000000000000^4239 ≤ 11861388818257^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685656873 1250000000 11861388818257 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-713248681/5000000000 : ℝ), (5128272681/10000000000 : ℝ), (685656873/1250000000 : ℝ)] ![(445595970281/5000000000000 : ℝ), (21821262653077/50000000000000 : ℝ), (11861388818257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-713248681/5000000000 : ℝ)|^5263 ≤ (445595970281/5000000000000 : ℝ)^4239
        have hw : |(-713248681/5000000000 : ℝ)|=(713248681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128272681/10000000000 : ℝ)|^5263 ≤ (21821262653077/50000000000000 : ℝ)^4239
        have hw : |(5128272681/10000000000 : ℝ)|=(5128272681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685656873/1250000000 : ℝ)|^5263 ≤ (11861388818257/25000000000000 : ℝ)^4239
        have hw : |(685656873/1250000000 : ℝ)|=(685656873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s1_5 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525169971/1000000000 : ℝ)*x 0 + (-627659977/5000000000 : ℝ)*x 1 + (5485254759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525169971/1000000000 : ℝ)^5263 ≤ (44950417887959/100000000000000 : ℝ)^4239 := by
    have hnat : (525169971 : ℕ)^5263*100000000000000^4239 ≤ 44950417887959^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525169971 1000000000 44950417887959 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627659977/5000000000 : ℝ)^5263 ≤ (7604029244223/100000000000000 : ℝ)^4239 := by
    have hnat : (627659977 : ℕ)^5263*100000000000000^4239 ≤ 7604029244223^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627659977 5000000000 7604029244223 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485254759/10000000000 : ℝ)^5263 ≤ (23722776428363/50000000000000 : ℝ)^4239 := by
    have hnat : (5485254759 : ℕ)^5263*50000000000000^4239 ≤ 23722776428363^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485254759 10000000000 23722776428363 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525169971/1000000000 : ℝ), (-627659977/5000000000 : ℝ), (5485254759/10000000000 : ℝ)] ![(44950417887959/100000000000000 : ℝ), (7604029244223/100000000000000 : ℝ), (23722776428363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525169971/1000000000 : ℝ)|^5263 ≤ (44950417887959/100000000000000 : ℝ)^4239
        have hw : |(525169971/1000000000 : ℝ)|=(525169971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627659977/5000000000 : ℝ)|^5263 ≤ (7604029244223/100000000000000 : ℝ)^4239
        have hw : |(-627659977/5000000000 : ℝ)|=(627659977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485254759/10000000000 : ℝ)|^5263 ≤ (23722776428363/50000000000000 : ℝ)^4239
        have hw : |(5485254759/10000000000 : ℝ)|=(5485254759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s1_6 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625850047/5000000000 : ℝ)*x 0 + (2742627507/5000000000 : ℝ)*x 1 + (-627659523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625850047/5000000000 : ℝ)^5263 ≤ (44950421968663/100000000000000 : ℝ)^4239 := by
    have hnat : (2625850047 : ℕ)^5263*100000000000000^4239 ≤ 44950421968663^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625850047 5000000000 44950421968663 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742627507/5000000000 : ℝ)^5263 ≤ (23722777797601/50000000000000 : ℝ)^4239 := by
    have hnat : (2742627507 : ℕ)^5263*50000000000000^4239 ≤ 23722777797601^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742627507 5000000000 23722777797601 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627659523/5000000000 : ℝ)^5263 ≤ (1901005603853/25000000000000 : ℝ)^4239 := by
    have hnat : (627659523 : ℕ)^5263*25000000000000^4239 ≤ 1901005603853^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627659523 5000000000 1901005603853 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625850047/5000000000 : ℝ), (2742627507/5000000000 : ℝ), (-627659523/5000000000 : ℝ)] ![(44950421968663/100000000000000 : ℝ), (23722777797601/50000000000000 : ℝ), (1901005603853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625850047/5000000000 : ℝ)|^5263 ≤ (44950421968663/100000000000000 : ℝ)^4239
        have hw : |(2625850047/5000000000 : ℝ)|=(2625850047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742627507/5000000000 : ℝ)|^5263 ≤ (23722777797601/50000000000000 : ℝ)^4239
        have hw : |(2742627507/5000000000 : ℝ)|=(2742627507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-627659523/5000000000 : ℝ)|^5263 ≤ (1901005603853/25000000000000 : ℝ)^4239
        have hw : |(-627659523/5000000000 : ℝ)|=(627659523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s1_7 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4108629179/10000000000 : ℝ)*x 0 + (4641180777/10000000000 : ℝ)*x 1 + (72360033/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4108629179/10000000000 : ℝ)^5263 ≤ (8285507485367/25000000000000 : ℝ)^4239 := by
    have hnat : (4108629179 : ℕ)^5263*25000000000000^4239 ≤ 8285507485367^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108629179 10000000000 8285507485367 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4641180777/10000000000 : ℝ)^5263 ≤ (48195571961/125000000000 : ℝ)^4239 := by
    have hnat : (4641180777 : ℕ)^5263*125000000000^4239 ≤ 48195571961^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4641180777 10000000000 48195571961 125000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72360033/200000000 : ℝ)^5263 ≤ (28301512470887/100000000000000 : ℝ)^4239 := by
    have hnat : (72360033 : ℕ)^5263*100000000000000^4239 ≤ 28301512470887^4239*200000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72360033 200000000 28301512470887 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4108629179/10000000000 : ℝ), (4641180777/10000000000 : ℝ), (72360033/200000000 : ℝ)] ![(8285507485367/25000000000000 : ℝ), (48195571961/125000000000 : ℝ), (28301512470887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4108629179/10000000000 : ℝ)|^5263 ≤ (8285507485367/25000000000000 : ℝ)^4239
        have hw : |(4108629179/10000000000 : ℝ)|=(4108629179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4641180777/10000000000 : ℝ)|^5263 ≤ (48195571961/125000000000 : ℝ)^4239
        have hw : |(4641180777/10000000000 : ℝ)|=(4641180777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(72360033/200000000 : ℝ)|^5263 ≤ (28301512470887/100000000000000 : ℝ)^4239
        have hw : |(72360033/200000000 : ℝ)|=(72360033/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1705_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9669/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8737/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5903/100000 : ℝ) ^ (5255/1024 : ℝ) ≤ (49356816988597/100000000000000000000 : ℝ) := by
    have hpowers : (5903/100000 : ℝ)^5255 ≤ (49356816988597/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5903 : ℕ)^5255*100000000000000000000^1024 ≤ 49356816988597^1024*100000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5903 100000 49356816988597 100000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5903/100000 : ℝ)) (X := (49356816988597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11043/50000 : ℝ) ^ (5255/1024 : ℝ) ≤ (43064201400465471/100000000000000000000 : ℝ) := by
    have hpowers : (11043/50000 : ℝ)^5255 ≤ (43064201400465471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11043 : ℕ)^5255*100000000000000000000^1024 ≤ 43064201400465471^1024*50000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11043 50000 43064201400465471 100000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11043/50000 : ℝ)) (X := (43064201400465471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000049356816988597/50000000000000000000 : ℝ) ≤ (10000001923553207/10000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (50000049356816988597/50000000000000000000 : ℝ)^1024 ≤ (10000001923553207/10000000000000000 : ℝ)^5255 := by
      have hnat : (50000049356816988597 : ℕ)^1024*10000000000000000^5255 ≤ 10000001923553207^5255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000049356816988597 50000000000000000000 10000001923553207 10000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001923553207/10000000000000000 : ℝ)) (X := (50000049356816988597/50000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010778389554363517/25000000000000000000 : ℝ) ≤ (5000419986899579/5000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (25010778389554363517/25000000000000000000 : ℝ)^1024 ≤ (5000419986899579/5000000000000000 : ℝ)^5255 := by
      have hnat : (25010778389554363517 : ℕ)^1024*5000000000000000^5255 ≤ 5000419986899579^5255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010778389554363517 25000000000000000000 5000419986899579 5000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000419986899579/5000000000000000 : ℝ)) (X := (25010778389554363517/25000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043064201400465471/50000000000000000000 : ℝ) ≤ (10001678024045109/10000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (50043064201400465471/50000000000000000000 : ℝ)^1024 ≤ (10001678024045109/10000000000000000 : ℝ)^5255 := by
      have hnat : (50043064201400465471 : ℕ)^1024*10000000000000000^5255 ≤ 10001678024045109^5255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043064201400465471 50000000000000000000 10001678024045109 10000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001678024045109/10000000000000000 : ℝ)) (X := (50043064201400465471/50000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(49356816988597/100000000000000000000 : ℝ) ≤ ((1294561096861262811/1294640000000000000 : ℝ)+2*(838050245951/1618300000000000 : ℝ)*(5903/100000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (1294561096861262811/1294640000000000000 : ℝ)+2*(838050245951/1618300000000000 : ℝ)*(5903/100000 : ℝ)=(10000001923553207/10000000000000000 : ℝ) by norm_num, show 1+2*(49356816988597/100000000000000000000 : ℝ)=(50000049356816988597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43064201400465471/100000000000000000000 : ℝ)+(49356816988597/100000000000000000000 : ℝ) ≤ ((1294561096861262811/1294640000000000000 : ℝ)+(838050245951/1618300000000000 : ℝ)*((11043/50000 : ℝ)+(5903/100000 : ℝ)))^(5255/1024 : ℝ) := by
    rw [show (1294561096861262811/1294640000000000000 : ℝ)+(838050245951/1618300000000000 : ℝ)*((11043/50000 : ℝ)+(5903/100000 : ℝ))=(5000419986899579/5000000000000000 : ℝ) by norm_num, show 1+(43064201400465471/100000000000000000000 : ℝ)+(49356816988597/100000000000000000000 : ℝ)=(25010778389554363517/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43064201400465471/100000000000000000000 : ℝ) ≤ ((1294561096861262811/1294640000000000000 : ℝ)+2*(838050245951/1618300000000000 : ℝ)*(11043/50000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (1294561096861262811/1294640000000000000 : ℝ)+2*(838050245951/1618300000000000 : ℝ)*(11043/50000 : ℝ)=(10001678024045109/10000000000000000 : ℝ) by norm_num, show 1+2*(43064201400465471/100000000000000000000 : ℝ)=(50043064201400465471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1294561096861262811/1294640000000000000 : ℝ)*(X 1 0+X 2 0)+(838050245951/1618300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (5903/100000 : ℝ)) (hi := (11043/50000 : ℝ)) (c := (1294561096861262811/1294640000000000000 : ℝ)) (alpha := (838050245951/1618300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1294561096861262811/1294640000000000000 : ℝ)*(X 0 1+X 2 1)+(838050245951/1618300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (5903/100000 : ℝ)) (hi := (11043/50000 : ℝ)) (c := (1294561096861262811/1294640000000000000 : ℝ)) (alpha := (838050245951/1618300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1294561096861262811/1294640000000000000 : ℝ)*(X 0 2+X 1 2)+(838050245951/1618300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (5903/100000 : ℝ)) (hi := (11043/50000 : ℝ)) (c := (1294561096861262811/1294640000000000000 : ℝ)) (alpha := (838050245951/1618300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1426299281/10000000000 : ℝ)*X 0 0+(2744860393/5000000000 : ℝ)*X 0 1+(2561939099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337413313/2500000000 : ℝ)*X 1 0+(-8083487/50000000 : ℝ)*X 1 1+(5123877359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349651903/10000000000 : ℝ)*X 2 0+(5123878537/10000000000 : ℝ)*X 2 1+(-404174411/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2054030021/5000000000 : ℝ)*X 0 0+(144208129/400000000 : ℝ)*X 0 1+(581721909/1250000000 : ℝ)*X 0 2+(2054030021/5000000000 : ℝ)*X 1 0+(144208129/400000000 : ℝ)*X 1 1+(581721909/1250000000 : ℝ)*X 1 2+(2054030021/5000000000 : ℝ)*X 2 0+(144208129/400000000 : ℝ)*X 2 1+(581721909/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-713248681/5000000000 : ℝ)*X 0 0+(5128272681/10000000000 : ℝ)*X 0 1+(685656873/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525169971/1000000000 : ℝ)*X 1 0+(-627659977/5000000000 : ℝ)*X 1 1+(5485254759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625850047/5000000000 : ℝ)*X 2 0+(2742627507/5000000000 : ℝ)*X 2 1+(-627659523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4108629179/10000000000 : ℝ)*X 0 0+(4641180777/10000000000 : ℝ)*X 0 1+(72360033/200000000 : ℝ)*X 0 2+(4108629179/10000000000 : ℝ)*X 1 0+(4641180777/10000000000 : ℝ)*X 1 1+(72360033/200000000 : ℝ)*X 1 2+(4108629179/10000000000 : ℝ)*X 2 0+(4641180777/10000000000 : ℝ)*X 2 1+(72360033/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (440923357029476507337261969/32366000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (915830733/50000000000000 : ℝ)*(base19) + (972300989/100000000000000 : ℝ)*(base23) + (101824081/100000000000000 : ℝ)*(lower2) + (76313161/20000000000000 : ℝ)*(upper3) + (677303/6250000000000 : ℝ)*(lower4) + (921781323822207/50000000000000 : ℝ)*(major0) + (921781323822207/50000000000000 : ℝ)*(major1) + (921781323822207/50000000000000 : ℝ)*(major2) + (273343144339509/10000000000000 : ℝ)*(sp0) + (1366718710921693/50000000000000 : ℝ)*(sp1) + (341679785150483/12500000000000 : ℝ)*(sp2) + (23842021335139/2500000000000 : ℝ)*(sp3) + (1952527441/25000000000000 : ℝ)*(sp4) + (189371081/4000000000000 : ℝ)*(sp7) + (119210698460323/12500000000000 : ℝ)*(f.failure) + (2733439253504853/100000000000000 : ℝ)*(f.sum) + (277801554112641/80915000000000000000000000000 : ℝ)*base66 + (216187083256538523/64732000000000000000000000000000 : ℝ)*base68 + (205910083153382523/64732000000000000000000000000000 : ℝ)*base70 + (443065625404685477/64732000000000000000000000000000 : ℝ)*base71 + (319530219700161/80915000000000000000000000000 : ℝ)*base74 + (684155824518721477/64732000000000000000000000000000 : ℝ)*base75 + (156370062399245477/64732000000000000000000000000000 : ℝ)*base77 + (239838920660453477/64732000000000000000000000000000 : ℝ)*base79 + (89908411524549/20228750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1190579/125000000000000000000 : ℝ)*base90 + (1190579/125000000000000000000 : ℝ)*base92 + (1190579/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14128085738956460614780767/4045750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (467593871/100000000000000 : ℝ)*(base19) + (631657609/50000000000000 : ℝ)*(base23) + (40474801/20000000000000 : ℝ)*(lower4) + (2500947/10000000000000 : ℝ)*(lower5) + (236162803657451/12500000000000 : ℝ)*(major0) + (236162803657451/12500000000000 : ℝ)*(major1) + (236162803657451/12500000000000 : ℝ)*(major2) + (2048805793/50000000000000 : ℝ)*(sp1) + (7559036617/50000000000000 : ℝ)*(sp2) + (618639187/100000000000000 : ℝ)*(sp3) + (1400628850833491/50000000000000 : ℝ)*(sp4) + (1400626568230763/50000000000000 : ℝ)*(sp5) + (280124132027853/10000000000000 : ℝ)*(sp6) + (61084151363147/6250000000000 : ℝ)*(sp7) + (977347040449539/100000000000000 : ℝ)*(f.failure) + (1400628850833491/50000000000000 : ℝ)*(f.sum) + (2450131806831/40457500000000000000000000000 : ℝ)*base66 + (28487144819332561/16183000000000000000000000000000 : ℝ)*base67 + (21787340241859561/16183000000000000000000000000000 : ℝ)*base69 + (53027666265173561/16183000000000000000000000000000 : ℝ)*base71 + (31301916779083/80915000000000000000000000000 : ℝ)*base73 + (63491329971700439/16183000000000000000000000000000 : ℝ)*base76 + (3337586914003561/16183000000000000000000000000000 : ℝ)*base77 + (43124517234844561/16183000000000000000000000000000 : ℝ)*base79 + (8845159361453/20228750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5592653/1000000000000000000000 : ℝ)*base89 + (5592653/1000000000000000000000 : ℝ)*base91 + (5592653/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1705_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1705_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1705_s2_0 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2234661/15625000 : ℝ)*x 0 + (2736942133/5000000000 : ℝ)*x 1 + (5137118477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2234661/15625000 : ℝ)^5263 ≤ (4470258287321/50000000000000 : ℝ)^4239 := by
    have hnat : (2234661 : ℕ)^5263*50000000000000^4239 ≤ 4470258287321^4239*15625000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234661 15625000 4470258287321 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736942133/5000000000 : ℝ)^5263 ≤ (47323474366211/100000000000000 : ℝ)^4239 := by
    have hnat : (2736942133 : ℕ)^5263*100000000000000^4239 ≤ 47323474366211^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736942133 5000000000 47323474366211 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137118477/10000000000 : ℝ)^5263 ≤ (218680045219/500000000000 : ℝ)^4239 := by
    have hnat : (5137118477 : ℕ)^5263*500000000000^4239 ≤ 218680045219^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137118477 10000000000 218680045219 500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2234661/15625000 : ℝ), (2736942133/5000000000 : ℝ), (5137118477/10000000000 : ℝ)] ![(4470258287321/50000000000000 : ℝ), (47323474366211/100000000000000 : ℝ), (218680045219/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2234661/15625000 : ℝ)|^5263 ≤ (4470258287321/50000000000000 : ℝ)^4239
        have hw : |(-2234661/15625000 : ℝ)|=(2234661/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736942133/5000000000 : ℝ)|^5263 ≤ (47323474366211/100000000000000 : ℝ)^4239
        have hw : |(2736942133/5000000000 : ℝ)|=(2736942133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137118477/10000000000 : ℝ)|^5263 ≤ (218680045219/500000000000 : ℝ)^4239
        have hw : |(5137118477/10000000000 : ℝ)|=(5137118477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s2_1 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336343103/2500000000 : ℝ)*x 0 + (-1604900263/10000000000 : ℝ)*x 1 + (5137118691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336343103/2500000000 : ℝ)^5263 ≤ (45947996881403/100000000000000 : ℝ)^4239 := by
    have hnat : (1336343103 : ℕ)^5263*100000000000000^4239 ≤ 45947996881403^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336343103 2500000000 45947996881403 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1604900263/10000000000 : ℝ)^5263 ≤ (5157995896027/50000000000000 : ℝ)^4239 := by
    have hnat : (1604900263 : ℕ)^5263*50000000000000^4239 ≤ 5157995896027^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604900263 10000000000 5157995896027 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137118691/10000000000 : ℝ)^5263 ≤ (8747202261171/20000000000000 : ℝ)^4239 := by
    have hnat : (5137118691 : ℕ)^5263*20000000000000^4239 ≤ 8747202261171^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137118691 10000000000 8747202261171 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336343103/2500000000 : ℝ), (-1604900263/10000000000 : ℝ), (5137118691/10000000000 : ℝ)] ![(45947996881403/100000000000000 : ℝ), (5157995896027/50000000000000 : ℝ), (8747202261171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336343103/2500000000 : ℝ)|^5263 ≤ (45947996881403/100000000000000 : ℝ)^4239
        have hw : |(1336343103/2500000000 : ℝ)|=(1336343103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1604900263/10000000000 : ℝ)|^5263 ≤ (5157995896027/50000000000000 : ℝ)^4239
        have hw : |(-1604900263/10000000000 : ℝ)|=(1604900263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137118691/10000000000 : ℝ)|^5263 ≤ (8747202261171/20000000000000 : ℝ)^4239
        have hw : |(5137118691/10000000000 : ℝ)|=(5137118691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s2_2 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672686197/5000000000 : ℝ)*x 0 + (1027423723/2000000000 : ℝ)*x 1 + (-401225097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672686197/5000000000 : ℝ)^5263 ≤ (22973998344651/50000000000000 : ℝ)^4239 := by
    have hnat : (2672686197 : ℕ)^5263*50000000000000^4239 ≤ 22973998344651^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672686197 5000000000 22973998344651 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027423723/2000000000 : ℝ)^5263 ≤ (10934002625627/25000000000000 : ℝ)^4239 := by
    have hnat : (1027423723 : ℕ)^5263*25000000000000^4239 ≤ 10934002625627^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027423723 2000000000 10934002625627 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401225097/2500000000 : ℝ)^5263 ≤ (10315992789623/100000000000000 : ℝ)^4239 := by
    have hnat : (401225097 : ℕ)^5263*100000000000000^4239 ≤ 10315992789623^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401225097 2500000000 10315992789623 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672686197/5000000000 : ℝ), (1027423723/2000000000 : ℝ), (-401225097/2500000000 : ℝ)] ![(22973998344651/50000000000000 : ℝ), (10934002625627/25000000000000 : ℝ), (10315992789623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672686197/5000000000 : ℝ)|^5263 ≤ (22973998344651/50000000000000 : ℝ)^4239
        have hw : |(2672686197/5000000000 : ℝ)|=(2672686197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027423723/2000000000 : ℝ)|^5263 ≤ (10934002625627/25000000000000 : ℝ)^4239
        have hw : |(1027423723/2000000000 : ℝ)|=(1027423723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-401225097/2500000000 : ℝ)|^5263 ≤ (10315992789623/100000000000000 : ℝ)^4239
        have hw : |(-401225097/2500000000 : ℝ)|=(401225097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s2_3 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4111063741/10000000000 : ℝ)*x 0 + (364660373/1000000000 : ℝ)*x 1 + (1152959123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111063741/10000000000 : ℝ)^5263 ≤ (16583206944869/50000000000000 : ℝ)^4239 := by
    have hnat : (4111063741 : ℕ)^5263*50000000000000^4239 ≤ 16583206944869^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111063741 10000000000 16583206944869 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364660373/1000000000 : ℝ)^5263 ≤ (1428978098551/5000000000000 : ℝ)^4239 := by
    have hnat : (364660373 : ℕ)^5263*5000000000000^4239 ≤ 1428978098551^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364660373 1000000000 1428978098551 5000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152959123/2500000000 : ℝ)^5263 ≤ (38254024126207/100000000000000 : ℝ)^4239 := by
    have hnat : (1152959123 : ℕ)^5263*100000000000000^4239 ≤ 38254024126207^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152959123 2500000000 38254024126207 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111063741/10000000000 : ℝ), (364660373/1000000000 : ℝ), (1152959123/2500000000 : ℝ)] ![(16583206944869/50000000000000 : ℝ), (1428978098551/5000000000000 : ℝ), (38254024126207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111063741/10000000000 : ℝ)|^5263 ≤ (16583206944869/50000000000000 : ℝ)^4239
        have hw : |(4111063741/10000000000 : ℝ)|=(4111063741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364660373/1000000000 : ℝ)|^5263 ≤ (1428978098551/5000000000000 : ℝ)^4239
        have hw : |(364660373/1000000000 : ℝ)|=(364660373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152959123/2500000000 : ℝ)|^5263 ≤ (38254024126207/100000000000000 : ℝ)^4239
        have hw : |(1152959123/2500000000 : ℝ)|=(1152959123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s2_4 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1430337553/10000000000 : ℝ)*x 0 + (321302787/625000000 : ℝ)*x 1 + (5470102503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1430337553/10000000000 : ℝ)^5263 ≤ (8941715829909/100000000000000 : ℝ)^4239 := by
    have hnat : (1430337553 : ℕ)^5263*100000000000000^4239 ≤ 8941715829909^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430337553 10000000000 8941715829909 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321302787/625000000 : ℝ)^5263 ≤ (21887699423713/50000000000000 : ℝ)^4239 := by
    have hnat : (321302787 : ℕ)^5263*50000000000000^4239 ≤ 21887699423713^4239*625000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321302787 625000000 21887699423713 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470102503/10000000000 : ℝ)^5263 ≤ (47282885303283/100000000000000 : ℝ)^4239 := by
    have hnat : (5470102503 : ℕ)^5263*100000000000000^4239 ≤ 47282885303283^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470102503 10000000000 47282885303283 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1430337553/10000000000 : ℝ), (321302787/625000000 : ℝ), (5470102503/10000000000 : ℝ)] ![(8941715829909/100000000000000 : ℝ), (21887699423713/50000000000000 : ℝ), (47282885303283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1430337553/10000000000 : ℝ)|^5263 ≤ (8941715829909/100000000000000 : ℝ)^4239
        have hw : |(-1430337553/10000000000 : ℝ)|=(1430337553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321302787/625000000 : ℝ)|^5263 ≤ (21887699423713/50000000000000 : ℝ)^4239
        have hw : |(321302787/625000000 : ℝ)|=(321302787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470102503/10000000000 : ℝ)|^5263 ≤ (47282885303283/100000000000000 : ℝ)^4239
        have hw : |(5470102503/10000000000 : ℝ)|=(5470102503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s2_5 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627621203/5000000000 : ℝ)*x 0 + (-1271916589/10000000000 : ℝ)*x 1 + (85470351/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627621203/5000000000 : ℝ)^5263 ≤ (5623508573621/12500000000000 : ℝ)^4239 := by
    have hnat : (2627621203 : ℕ)^5263*12500000000000^4239 ≤ 5623508573621^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627621203 5000000000 5623508573621 12500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271916589/10000000000 : ℝ)^5263 ≤ (7729046512333/100000000000000 : ℝ)^4239 := by
    have hnat : (1271916589 : ℕ)^5263*100000000000000^4239 ≤ 7729046512333^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271916589 10000000000 7729046512333 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85470351/156250000 : ℝ)^5263 ≤ (47282884884737/100000000000000 : ℝ)^4239 := by
    have hnat : (85470351 : ℕ)^5263*100000000000000^4239 ≤ 47282884884737^4239*156250000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85470351 156250000 47282884884737 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627621203/5000000000 : ℝ), (-1271916589/10000000000 : ℝ), (85470351/156250000 : ℝ)] ![(5623508573621/12500000000000 : ℝ), (7729046512333/100000000000000 : ℝ), (47282884884737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627621203/5000000000 : ℝ)|^5263 ≤ (5623508573621/12500000000000 : ℝ)^4239
        have hw : |(2627621203/5000000000 : ℝ)|=(2627621203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1271916589/10000000000 : ℝ)|^5263 ≤ (7729046512333/100000000000000 : ℝ)^4239
        have hw : |(-1271916589/10000000000 : ℝ)|=(1271916589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85470351/156250000 : ℝ)|^5263 ≤ (47282884884737/100000000000000 : ℝ)^4239
        have hw : |(85470351/156250000 : ℝ)|=(85470351/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s2_6 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051048467/2000000000 : ℝ)*x 0 + (1367525619/2500000000 : ℝ)*x 1 + (-1271916671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051048467/2000000000 : ℝ)^5263 ≤ (2249403391717/5000000000000 : ℝ)^4239 := by
    have hnat : (1051048467 : ℕ)^5263*5000000000000^4239 ≤ 2249403391717^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051048467 2000000000 2249403391717 5000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367525619/2500000000 : ℝ)^5263 ≤ (47282885013521/100000000000000 : ℝ)^4239 := by
    have hnat : (1367525619 : ℕ)^5263*100000000000000^4239 ≤ 47282885013521^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367525619 2500000000 47282885013521 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271916671/10000000000 : ℝ)^5263 ≤ (483065445687/6250000000000 : ℝ)^4239 := by
    have hnat : (1271916671 : ℕ)^5263*6250000000000^4239 ≤ 483065445687^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271916671 10000000000 483065445687 6250000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051048467/2000000000 : ℝ), (1367525619/2500000000 : ℝ), (-1271916671/10000000000 : ℝ)] ![(2249403391717/5000000000000 : ℝ), (47282885013521/100000000000000 : ℝ), (483065445687/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051048467/2000000000 : ℝ)|^5263 ≤ (2249403391717/5000000000000 : ℝ)^4239
        have hw : |(1051048467/2000000000 : ℝ)|=(1051048467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367525619/2500000000 : ℝ)|^5263 ≤ (47282885013521/100000000000000 : ℝ)^4239
        have hw : |(1367525619/2500000000 : ℝ)|=(1367525619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1271916671/10000000000 : ℝ)|^5263 ≤ (483065445687/6250000000000 : ℝ)^4239
        have hw : |(-1271916671/10000000000 : ℝ)|=(1271916671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s2_7 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4111507069/10000000000 : ℝ)*x 0 + (575144617/1250000000 : ℝ)*x 1 + (731488641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111507069/10000000000 : ℝ)^5263 ≤ (16585427262367/50000000000000 : ℝ)^4239 := by
    have hnat : (4111507069 : ℕ)^5263*50000000000000^4239 ≤ 16585427262367^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111507069 10000000000 16585427262367 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575144617/1250000000 : ℝ)^5263 ≤ (38144071699647/100000000000000 : ℝ)^4239 := by
    have hnat : (575144617 : ℕ)^5263*100000000000000^4239 ≤ 38144071699647^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575144617 1250000000 38144071699647 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731488641/2000000000 : ℝ)^5263 ≤ (5737014751483/20000000000000 : ℝ)^4239 := by
    have hnat : (731488641 : ℕ)^5263*20000000000000^4239 ≤ 5737014751483^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731488641 2000000000 5737014751483 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111507069/10000000000 : ℝ), (575144617/1250000000 : ℝ), (731488641/2000000000 : ℝ)] ![(16585427262367/50000000000000 : ℝ), (38144071699647/100000000000000 : ℝ), (5737014751483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111507069/10000000000 : ℝ)|^5263 ≤ (16585427262367/50000000000000 : ℝ)^4239
        have hw : |(4111507069/10000000000 : ℝ)|=(4111507069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(575144617/1250000000 : ℝ)|^5263 ≤ (38144071699647/100000000000000 : ℝ)^4239
        have hw : |(575144617/1250000000 : ℝ)|=(575144617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(731488641/2000000000 : ℝ)|^5263 ≤ (5737014751483/20000000000000 : ℝ)^4239
        have hw : |(731488641/2000000000 : ℝ)|=(731488641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1705_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4979/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8571/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9669/100000 : ℝ) ^ (5255/1024 : ℝ) ≤ (621075829323537/100000000000000000000 : ℝ) := by
    have hpowers : (9669/100000 : ℝ)^5255 ≤ (621075829323537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9669 : ℕ)^5255*100000000000000000000^1024 ≤ 621075829323537^1024*100000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9669 100000 621075829323537 100000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9669/100000 : ℝ)) (X := (621075829323537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8737/50000 : ℝ) ^ (5255/1024 : ℝ) ≤ (12944394481442211/100000000000000000000 : ℝ) := by
    have hpowers : (8737/50000 : ℝ)^5255 ≤ (12944394481442211/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8737 : ℕ)^5255*100000000000000000000^1024 ≤ 12944394481442211^1024*50000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8737 50000 12944394481442211 100000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8737/50000 : ℝ)) (X := (12944394481442211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000621075829323537/50000000000000000000 : ℝ) ≤ (10000024204699107/10000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (50000621075829323537/50000000000000000000 : ℝ)^1024 ≤ (10000024204699107/10000000000000000 : ℝ)^5255 := by
      have hnat : (50000621075829323537 : ℕ)^1024*10000000000000000^5255 ≤ 10000024204699107^5255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000621075829323537 50000000000000000000 10000024204699107 10000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000024204699107/10000000000000000 : ℝ)) (X := (50000621075829323537/50000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003391367577691437/25000000000000000000 : ℝ) ≤ (2000052865016423/2000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (25003391367577691437/25000000000000000000 : ℝ)^1024 ≤ (2000052865016423/2000000000000000 : ℝ)^5255 := by
      have hnat : (25003391367577691437 : ℕ)^1024*2000000000000000^5255 ≤ 2000052865016423^5255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003391367577691437 25000000000000000000 2000052865016423 2000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000052865016423/2000000000000000 : ℝ)) (X := (25003391367577691437/25000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50012944394481442211/50000000000000000000 : ℝ) ≤ (10000504445465123/10000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (50012944394481442211/50000000000000000000 : ℝ)^1024 ≤ (10000504445465123/10000000000000000 : ℝ)^5255 := by
      have hnat : (50012944394481442211 : ℕ)^1024*10000000000000000^5255 ≤ 10000504445465123^5255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012944394481442211 50000000000000000000 10000504445465123 10000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000504445465123/10000000000000000 : ℝ)) (X := (50012944394481442211/50000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(621075829323537/100000000000000000000 : ℝ) ≤ ((78045545469709921431/78050000000000000000 : ℝ)+2*(7503761969/24390625000000 : ℝ)*(9669/100000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (78045545469709921431/78050000000000000000 : ℝ)+2*(7503761969/24390625000000 : ℝ)*(9669/100000 : ℝ)=(10000024204699107/10000000000000000 : ℝ) by norm_num, show 1+2*(621075829323537/100000000000000000000 : ℝ)=(50000621075829323537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12944394481442211/100000000000000000000 : ℝ)+(621075829323537/100000000000000000000 : ℝ) ≤ ((78045545469709921431/78050000000000000000 : ℝ)+(7503761969/24390625000000 : ℝ)*((8737/50000 : ℝ)+(9669/100000 : ℝ)))^(5255/1024 : ℝ) := by
    rw [show (78045545469709921431/78050000000000000000 : ℝ)+(7503761969/24390625000000 : ℝ)*((8737/50000 : ℝ)+(9669/100000 : ℝ))=(2000052865016423/2000000000000000 : ℝ) by norm_num, show 1+(12944394481442211/100000000000000000000 : ℝ)+(621075829323537/100000000000000000000 : ℝ)=(25003391367577691437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12944394481442211/100000000000000000000 : ℝ) ≤ ((78045545469709921431/78050000000000000000 : ℝ)+2*(7503761969/24390625000000 : ℝ)*(8737/50000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (78045545469709921431/78050000000000000000 : ℝ)+2*(7503761969/24390625000000 : ℝ)*(8737/50000 : ℝ)=(10000504445465123/10000000000000000 : ℝ) by norm_num, show 1+2*(12944394481442211/100000000000000000000 : ℝ)=(50012944394481442211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (78045545469709921431/78050000000000000000 : ℝ)*(X 1 0+X 2 0)+(7503761969/24390625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (8737/50000 : ℝ)) (c := (78045545469709921431/78050000000000000000 : ℝ)) (alpha := (7503761969/24390625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (78045545469709921431/78050000000000000000 : ℝ)*(X 0 1+X 2 1)+(7503761969/24390625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (8737/50000 : ℝ)) (c := (78045545469709921431/78050000000000000000 : ℝ)) (alpha := (7503761969/24390625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (78045545469709921431/78050000000000000000 : ℝ)*(X 0 2+X 1 2)+(7503761969/24390625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (8737/50000 : ℝ)) (c := (78045545469709921431/78050000000000000000 : ℝ)) (alpha := (7503761969/24390625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2234661/15625000 : ℝ)*X 0 0+(2736942133/5000000000 : ℝ)*X 0 1+(5137118477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336343103/2500000000 : ℝ)*X 1 0+(-1604900263/10000000000 : ℝ)*X 1 1+(5137118691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672686197/5000000000 : ℝ)*X 2 0+(1027423723/2000000000 : ℝ)*X 2 1+(-401225097/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4111063741/10000000000 : ℝ)*X 0 0+(364660373/1000000000 : ℝ)*X 0 1+(1152959123/2500000000 : ℝ)*X 0 2+(4111063741/10000000000 : ℝ)*X 1 0+(364660373/1000000000 : ℝ)*X 1 1+(1152959123/2500000000 : ℝ)*X 1 2+(4111063741/10000000000 : ℝ)*X 2 0+(364660373/1000000000 : ℝ)*X 2 1+(1152959123/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1430337553/10000000000 : ℝ)*X 0 0+(321302787/625000000 : ℝ)*X 0 1+(5470102503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627621203/5000000000 : ℝ)*X 1 0+(-1271916589/10000000000 : ℝ)*X 1 1+(85470351/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051048467/2000000000 : ℝ)*X 2 0+(1367525619/2500000000 : ℝ)*X 2 1+(-1271916671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4111507069/10000000000 : ℝ)*X 0 0+(575144617/1250000000 : ℝ)*X 0 1+(731488641/2000000000 : ℝ)*X 0 2+(4111507069/10000000000 : ℝ)*X 1 0+(575144617/1250000000 : ℝ)*X 1 1+(731488641/2000000000 : ℝ)*X 1 2+(4111507069/10000000000 : ℝ)*X 2 0+(575144617/1250000000 : ℝ)*X 2 1+(731488641/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63316358777697586514829/19512500000000000000000000000 : ℝ) := by norm_num
    linear_combination (664043271/100000000000000 : ℝ)*(base19) + (31194483/5000000000000 : ℝ)*(base23) + (146208067/100000000000000 : ℝ)*(upper3) + (4029653/25000000000000 : ℝ)*(upper4) + (22914021/50000000000000 : ℝ)*(upper5) + (2002731786807267/100000000000000 : ℝ)*(major0) + (2002731786807267/100000000000000 : ℝ)*(major1) + (2002731786807267/100000000000000 : ℝ)*(major2) + (296943154911413/10000000000000 : ℝ)*(sp0) + (1484719050130167/50000000000000 : ℝ)*(sp1) + (1484719070206973/50000000000000 : ℝ)*(sp2) + (64751362047141/6250000000000 : ℝ)*(sp3) + (1803797369/25000000000000 : ℝ)*(sp4) + (2908392909/100000000000000 : ℝ)*(sp7) + (518012350573583/50000000000000 : ℝ)*(f.failure) + (1484719382151803/50000000000000 : ℝ)*(f.sum) + (51743044698411/39025000000000000000000000000 : ℝ)*base65 + (2986216066356560923/7805000000000000000000000000000000 : ℝ)*base68 + (33522870044851560923/7805000000000000000000000000000000 : ℝ)*base70 + (30976640846698439077/7805000000000000000000000000000000 : ℝ)*base71 + (61778937372707/19512500000000000000000000000 : ℝ)*base74 + (34648619656568439077/7805000000000000000000000000000000 : ℝ)*base75 + (5224034636318439077/7805000000000000000000000000000000 : ℝ)*base77 + (45187947988846560923/7805000000000000000000000000000000 : ℝ)*base80 + (73951573298089/39025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6101441/500000000000000000000 : ℝ)*base89 + (6101441/500000000000000000000 : ℝ)*base91 + (6101441/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16595549797685300583754238937/1951250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45753279/4000000000000 : ℝ)*(base19) + (241193017/20000000000000 : ℝ)*(base23) + (39211047/25000000000000 : ℝ)*(upper3) + (57508003/100000000000000 : ℝ)*(lower4) + (49375179/25000000000000 : ℝ)*(upper5) + (1024193967417109/50000000000000 : ℝ)*(major0) + (1024193967417109/50000000000000 : ℝ)*(major1) + (1024193967417109/50000000000000 : ℝ)*(major2) + (10494660317/100000000000000 : ℝ)*(sp1) + (10129413751/100000000000000 : ℝ)*(sp2) + (1518566348194433/50000000000000 : ℝ)*(sp4) + (1518560528948287/50000000000000 : ℝ)*(sp5) + (3037121361010031/100000000000000 : ℝ)*(sp6) + (1059642889776687/100000000000000 : ℝ)*(sp7) + (1059642889776687/100000000000000 : ℝ)*(f.failure) + (1518566348194433/50000000000000 : ℝ)*(f.sum) + (15165985914881/39025000000000000000000000000 : ℝ)*base66 + (24989620545922362979/3902500000000000000000000000000000 : ℝ)*base67 + (3462452221500137021/3902500000000000000000000000000000 : ℝ)*base70 + (14816863171754862979/3902500000000000000000000000000000 : ℝ)*base71 + (54520719703369/39025000000000000000000000000 : ℝ)*base73 + (8470576462462637021/3902500000000000000000000000000000 : ℝ)*base76 + (11019094190722637021/3902500000000000000000000000000000 : ℝ)*base78 + (14144255102550137021/3902500000000000000000000000000000 : ℝ)*base80 + (52613378991297/19512500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2698849/1000000000000000000000 : ℝ)*base89 + (2698849/1000000000000000000000 : ℝ)*base91 + (2698849/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1705_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1705_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1705_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1705_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1705_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1705_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1705_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
