-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1570_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:47.404929+00:00
-- url     : https://prove2.me/submissions/c5512ffb-2784-40cc-91dd-2f82884c4bbc

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
theorem support_rectangle_w1570_s6_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674094641/5000000000 : ℝ)*x 0 + (2610033633/5000000000 : ℝ)*x 1 + (-1890857317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674094641/5000000000 : ℝ)^4637 ≤ (22394680452379/50000000000000 : ℝ)^3613 := by
    have hnat : (2674094641 : ℕ)^4637*50000000000000^3613 ≤ 22394680452379^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674094641 5000000000 22394680452379 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610033633/5000000000 : ℝ)^4637 ≤ (43416977135183/100000000000000 : ℝ)^3613 := by
    have hnat : (2610033633 : ℕ)^4637*100000000000000^3613 ≤ 43416977135183^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610033633 5000000000 43416977135183 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890857317/10000000000 : ℝ)^4637 ≤ (5896830974151/50000000000000 : ℝ)^3613 := by
    have hnat : (1890857317 : ℕ)^4637*50000000000000^3613 ≤ 5896830974151^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890857317 10000000000 5896830974151 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674094641/5000000000 : ℝ), (2610033633/5000000000 : ℝ), (-1890857317/10000000000 : ℝ)] ![(22394680452379/50000000000000 : ℝ), (43416977135183/100000000000000 : ℝ), (5896830974151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674094641/5000000000 : ℝ)|^4637 ≤ (22394680452379/50000000000000 : ℝ)^3613
        have hw : |(2674094641/5000000000 : ℝ)|=(2674094641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610033633/5000000000 : ℝ)|^4637 ≤ (43416977135183/100000000000000 : ℝ)^3613
        have hw : |(2610033633/5000000000 : ℝ)|=(2610033633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890857317/10000000000 : ℝ)|^4637 ≤ (5896830974151/50000000000000 : ℝ)^3613
        have hw : |(-1890857317/10000000000 : ℝ)|=(1890857317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s6_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1785641649/10000000000 : ℝ)*x 0 + (104422769/200000000 : ℝ)*x 1 + (135617647/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1785641649/10000000000 : ℝ)^4637 ≤ (10958146858219/100000000000000 : ℝ)^3613 := by
    have hnat : (1785641649 : ℕ)^4637*100000000000000^3613 ≤ 10958146858219^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785641649 10000000000 10958146858219 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104422769/200000000 : ℝ)^4637 ≤ (43428411954937/100000000000000 : ℝ)^3613 := by
    have hnat : (104422769 : ℕ)^4637*100000000000000^3613 ≤ 43428411954937^3613*200000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104422769 200000000 43428411954937 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135617647/250000000 : ℝ)^4637 ≤ (45613441179597/100000000000000 : ℝ)^3613 := by
    have hnat : (135617647 : ℕ)^4637*100000000000000^3613 ≤ 45613441179597^3613*250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135617647 250000000 45613441179597 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1785641649/10000000000 : ℝ), (104422769/200000000 : ℝ), (135617647/250000000 : ℝ)] ![(10958146858219/100000000000000 : ℝ), (43428411954937/100000000000000 : ℝ), (45613441179597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1785641649/10000000000 : ℝ)|^4637 ≤ (10958146858219/100000000000000 : ℝ)^3613
        have hw : |(-1785641649/10000000000 : ℝ)|=(1785641649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104422769/200000000 : ℝ)|^4637 ≤ (43428411954937/100000000000000 : ℝ)^3613
        have hw : |(104422769/200000000 : ℝ)|=(104422769/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135617647/250000000 : ℝ)|^4637 ≤ (45613441179597/100000000000000 : ℝ)^3613
        have hw : |(135617647/250000000 : ℝ)|=(135617647/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s6_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264688141/500000000 : ℝ)*x 0 + (-1686218367/10000000000 : ℝ)*x 1 + (135617647/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264688141/500000000 : ℝ)^4637 ≤ (22102609043911/50000000000000 : ℝ)^3613 := by
    have hnat : (264688141 : ℕ)^4637*50000000000000^3613 ≤ 22102609043911^3613*500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264688141 500000000 22102609043911 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1686218367/10000000000 : ℝ)^4637 ≤ (10181340725157/100000000000000 : ℝ)^3613 := by
    have hnat : (1686218367 : ℕ)^4637*100000000000000^3613 ≤ 10181340725157^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686218367 10000000000 10181340725157 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135617647/250000000 : ℝ)^4637 ≤ (45613441179597/100000000000000 : ℝ)^3613 := by
    have hnat : (135617647 : ℕ)^4637*100000000000000^3613 ≤ 45613441179597^3613*250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135617647 250000000 45613441179597 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264688141/500000000 : ℝ), (-1686218367/10000000000 : ℝ), (135617647/250000000 : ℝ)] ![(22102609043911/50000000000000 : ℝ), (10181340725157/100000000000000 : ℝ), (45613441179597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264688141/500000000 : ℝ)|^4637 ≤ (22102609043911/50000000000000 : ℝ)^3613
        have hw : |(264688141/500000000 : ℝ)|=(264688141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1686218367/10000000000 : ℝ)|^4637 ≤ (10181340725157/100000000000000 : ℝ)^3613
        have hw : |(-1686218367/10000000000 : ℝ)|=(1686218367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135617647/250000000 : ℝ)|^4637 ≤ (45613441179597/100000000000000 : ℝ)^3613
        have hw : |(135617647/250000000 : ℝ)|=(135617647/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s6_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293762821/10000000000 : ℝ)*x 0 + (5424705879/10000000000 : ℝ)*x 1 + (-1686218367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293762821/10000000000 : ℝ)^4637 ≤ (44205218098539/100000000000000 : ℝ)^3613 := by
    have hnat : (5293762821 : ℕ)^4637*100000000000000^3613 ≤ 44205218098539^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293762821 10000000000 44205218098539 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424705879/10000000000 : ℝ)^4637 ≤ (9122688233761/20000000000000 : ℝ)^3613 := by
    have hnat : (5424705879 : ℕ)^4637*20000000000000^3613 ≤ 9122688233761^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424705879 10000000000 9122688233761 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1686218367/10000000000 : ℝ)^4637 ≤ (10181340725157/100000000000000 : ℝ)^3613 := by
    have hnat : (1686218367 : ℕ)^4637*100000000000000^3613 ≤ 10181340725157^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686218367 10000000000 10181340725157 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293762821/10000000000 : ℝ), (5424705879/10000000000 : ℝ), (-1686218367/10000000000 : ℝ)] ![(44205218098539/100000000000000 : ℝ), (9122688233761/20000000000000 : ℝ), (10181340725157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293762821/10000000000 : ℝ)|^4637 ≤ (44205218098539/100000000000000 : ℝ)^3613
        have hw : |(5293762821/10000000000 : ℝ)|=(5293762821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424705879/10000000000 : ℝ)|^4637 ≤ (9122688233761/20000000000000 : ℝ)^3613
        have hw : |(5424705879/10000000000 : ℝ)|=(5424705879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1686218367/10000000000 : ℝ)|^4637 ≤ (10181340725157/100000000000000 : ℝ)^3613
        have hw : |(-1686218367/10000000000 : ℝ)|=(1686218367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s6_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243569307/10000000000 : ℝ)*x 0 + (280588001/625000000 : ℝ)*x 1 + (801774897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243569307/10000000000 : ℝ)^4637 ≤ (2080187858061/6250000000000 : ℝ)^3613 := by
    have hnat : (4243569307 : ℕ)^4637*6250000000000^3613 ≤ 2080187858061^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243569307 10000000000 2080187858061 6250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280588001/625000000 : ℝ)^4637 ≤ (35777679170079/100000000000000 : ℝ)^3613 := by
    have hnat : (280588001 : ℕ)^4637*100000000000000^3613 ≤ 35777679170079^3613*625000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280588001 625000000 35777679170079 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801774897/2000000000 : ℝ)^4637 ≤ (15469657544521/50000000000000 : ℝ)^3613 := by
    have hnat : (801774897 : ℕ)^4637*50000000000000^3613 ≤ 15469657544521^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801774897 2000000000 15469657544521 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243569307/10000000000 : ℝ), (280588001/625000000 : ℝ), (801774897/2000000000 : ℝ)] ![(2080187858061/6250000000000 : ℝ), (35777679170079/100000000000000 : ℝ), (15469657544521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243569307/10000000000 : ℝ)|^4637 ≤ (2080187858061/6250000000000 : ℝ)^3613
        have hw : |(4243569307/10000000000 : ℝ)|=(4243569307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280588001/625000000 : ℝ)|^4637 ≤ (35777679170079/100000000000000 : ℝ)^3613
        have hw : |(280588001/625000000 : ℝ)|=(280588001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801774897/2000000000 : ℝ)|^4637 ≤ (15469657544521/50000000000000 : ℝ)^3613
        have hw : |(801774897/2000000000 : ℝ)|=(801774897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11121/100000 : ℝ) ^ (4635/1024 : ℝ) ≤ (4813896838906103/100000000000000000000 : ℝ) := by
    have hpowers : (11121/100000 : ℝ)^4635 ≤ (4813896838906103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11121 : ℕ)^4635*100000000000000000000^1024 ≤ 4813896838906103^1024*100000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11121 100000 4813896838906103 100000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11121/100000 : ℝ)) (X := (4813896838906103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4635/1024 : ℝ) ≤ (673117221934791/3125000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4635 ≤ (673117221934791/3125000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4635*3125000000000000000^1024 ≤ 673117221934791^1024*20000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 673117221934791 3125000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (673117221934791/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004813896838906103/50000000000000000000 : ℝ) ≤ (10000212696677521/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (50004813896838906103/50000000000000000000 : ℝ)^1024 ≤ (10000212696677521/10000000000000000 : ℝ)^4635 := by
      have hnat : (50004813896838906103 : ℕ)^1024*10000000000000000^4635 ≤ 10000212696677521^4635*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004813896838906103 50000000000000000000 10000212696677521 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000212696677521/10000000000000000 : ℝ)) (X := (50004813896838906103/50000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005270729588163883/20000000000000000000 : ℝ) ≤ (10000582165385309/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (20005270729588163883/20000000000000000000 : ℝ)^1024 ≤ (10000582165385309/10000000000000000 : ℝ)^4635 := by
      have hnat : (20005270729588163883 : ℕ)^1024*10000000000000000^4635 ≤ 10000582165385309^4635*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005270729588163883 20000000000000000000 10000582165385309 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000582165385309/10000000000000000 : ℝ)) (X := (20005270729588163883/20000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563173117221934791/1562500000000000000 : ℝ) ≤ (10000951634093097/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (1563173117221934791/1562500000000000000 : ℝ)^1024 ≤ (10000951634093097/10000000000000000 : ℝ)^4635 := by
      have hnat : (1563173117221934791 : ℕ)^1024*10000000000000000^4635 ≤ 10000951634093097^4635*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563173117221934791 1562500000000000000 10000951634093097 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000951634093097/10000000000000000 : ℝ)) (X := (1563173117221934791/1562500000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4813896838906103/100000000000000000000 : ℝ) ≤ ((10908177621325520237/10910000000000000000 : ℝ)+2*(92367176947/109100000000000 : ℝ)*(11121/100000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (10908177621325520237/10910000000000000000 : ℝ)+2*(92367176947/109100000000000 : ℝ)*(11121/100000 : ℝ)=(10000212696677521/10000000000000000 : ℝ) by norm_num, show 1+2*(4813896838906103/100000000000000000000 : ℝ)=(50004813896838906103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(673117221934791/3125000000000000000 : ℝ)+(4813896838906103/100000000000000000000 : ℝ) ≤ ((10908177621325520237/10910000000000000000 : ℝ)+(92367176947/109100000000000 : ℝ)*((3097/20000 : ℝ)+(11121/100000 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (10908177621325520237/10910000000000000000 : ℝ)+(92367176947/109100000000000 : ℝ)*((3097/20000 : ℝ)+(11121/100000 : ℝ))=(10000582165385309/10000000000000000 : ℝ) by norm_num, show 1+(673117221934791/3125000000000000000 : ℝ)+(4813896838906103/100000000000000000000 : ℝ)=(20005270729588163883/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(673117221934791/3125000000000000000 : ℝ) ≤ ((10908177621325520237/10910000000000000000 : ℝ)+2*(92367176947/109100000000000 : ℝ)*(3097/20000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (10908177621325520237/10910000000000000000 : ℝ)+2*(92367176947/109100000000000 : ℝ)*(3097/20000 : ℝ)=(10000951634093097/10000000000000000 : ℝ) by norm_num, show 1+2*(673117221934791/3125000000000000000 : ℝ)=(1563173117221934791/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10908177621325520237/10910000000000000000 : ℝ)*(X 1 0+X 2 0)+(92367176947/109100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10908177621325520237/10910000000000000000 : ℝ)) (alpha := (92367176947/109100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10908177621325520237/10910000000000000000 : ℝ)*(X 0 1+X 2 1)+(92367176947/109100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10908177621325520237/10910000000000000000 : ℝ)) (alpha := (92367176947/109100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10908177621325520237/10910000000000000000 : ℝ)*(X 0 2+X 1 2)+(92367176947/109100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10908177621325520237/10910000000000000000 : ℝ)) (alpha := (92367176947/109100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2674094641/5000000000 : ℝ)*X 2 0+(2610033633/5000000000 : ℝ)*X 2 1+(-1890857317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1785641649/10000000000 : ℝ)*X 0 0+(104422769/200000000 : ℝ)*X 0 1+(135617647/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((264688141/500000000 : ℝ)*X 1 0+(-1686218367/10000000000 : ℝ)*X 1 1+(135617647/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5293762821/10000000000 : ℝ)*X 2 0+(5424705879/10000000000 : ℝ)*X 2 1+(-1686218367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4243569307/10000000000 : ℝ)*X 0 0+(280588001/625000000 : ℝ)*X 0 1+(801774897/2000000000 : ℝ)*X 0 2+(4243569307/10000000000 : ℝ)*X 1 0+(280588001/625000000 : ℝ)*X 1 1+(801774897/2000000000 : ℝ)*X 1 2+(4243569307/10000000000 : ℝ)*X 2 0+(280588001/625000000 : ℝ)*X 2 1+(801774897/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (876209422104422274609162933/272750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19995587/4000000000000 : ℝ)*(base19) + (27288137/5000000000000 : ℝ)*(base23) + (20487911/12500000000000 : ℝ)*(lower1) + (32405463/50000000000000 : ℝ)*(upper3) + (20528231/100000000000000 : ℝ)*(lower4) + (830839/1250000000000 : ℝ)*(upper5) + (1748346404007197/50000000000000 : ℝ)*(major0) + (1748346404007197/50000000000000 : ℝ)*(major1) + (1748346404007197/50000000000000 : ℝ)*(major2) + (18744597/3125000000000 : ℝ)*(sp0) + (1228092204271477/25000000000000 : ℝ)*(sp1) + (4912368317196233/100000000000000 : ℝ)*(sp2) + (982473534299213/20000000000000 : ℝ)*(sp3) + (260127086482439/12500000000000 : ℝ)*(sp4) + (260127086482439/12500000000000 : ℝ)*(f.failure) + (1228092204271477/25000000000000 : ℝ)*(f.sum) + (4915006357871/2727500000000000000000000000 : ℝ)*base66 + (12808247219237045689/545500000000000000000000000000000 : ℝ)*base67 + (3311321564893045689/545500000000000000000000000000000 : ℝ)*base69 + (15020880070671045689/545500000000000000000000000000000 : ℝ)*base71 + (26459806880263/5455000000000000000000000000 : ℝ)*base73 + (78882551535606954311/545500000000000000000000000000000 : ℝ)*base76 + (1868197759869545689/545500000000000000000000000000000 : ℝ)*base77 + (375877474817454311/545500000000000000000000000000000 : ℝ)*base80 + (4279946988983/5455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (164641/12500000000000000000 : ℝ)*base90 + (164641/12500000000000000000 : ℝ)*base92 + (164641/12500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1570_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1570_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1570_box_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1581812103/10000000000 : ℝ)*x 0 + (5396591171/10000000000 : ℝ)*x 1 + (5396591211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1581812103/10000000000 : ℝ)^4637 ≤ (9379476283373/100000000000000 : ℝ)^3613 := by
    have hnat : (1581812103 : ℕ)^4637*100000000000000^3613 ≤ 9379476283373^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581812103 10000000000 9379476283373 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396591171/10000000000 : ℝ)^4637 ≤ (45310261639633/100000000000000 : ℝ)^3613 := by
    have hnat : (5396591171 : ℕ)^4637*100000000000000^3613 ≤ 45310261639633^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396591171 10000000000 45310261639633 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396591211/10000000000 : ℝ)^4637 ≤ (45310262070661/100000000000000 : ℝ)^3613 := by
    have hnat : (5396591211 : ℕ)^4637*100000000000000^3613 ≤ 45310262070661^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396591211 10000000000 45310262070661 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1581812103/10000000000 : ℝ), (5396591171/10000000000 : ℝ), (5396591211/10000000000 : ℝ)] ![(9379476283373/100000000000000 : ℝ), (45310261639633/100000000000000 : ℝ), (45310262070661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1581812103/10000000000 : ℝ)|^4637 ≤ (9379476283373/100000000000000 : ℝ)^3613
        have hw : |(-1581812103/10000000000 : ℝ)|=(1581812103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396591171/10000000000 : ℝ)|^4637 ≤ (45310261639633/100000000000000 : ℝ)^3613
        have hw : |(5396591171/10000000000 : ℝ)|=(5396591171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396591211/10000000000 : ℝ)|^4637 ≤ (45310262070661/100000000000000 : ℝ)^3613
        have hw : |(5396591211/10000000000 : ℝ)|=(5396591211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527114273/1000000000 : ℝ)*x 0 + (-878098781/5000000000 : ℝ)*x 1 + (2698296033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527114273/1000000000 : ℝ)^4637 ≤ (5495367844557/12500000000000 : ℝ)^3613 := by
    have hnat : (527114273 : ℕ)^4637*12500000000000^3613 ≤ 5495367844557^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527114273 1000000000 5495367844557 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878098781/5000000000 : ℝ)^4637 ≤ (26816964861/250000000000 : ℝ)^3613 := by
    have hnat : (878098781 : ℕ)^4637*250000000000^3613 ≤ 26816964861^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878098781 5000000000 26816964861 250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698296033/5000000000 : ℝ)^4637 ≤ (453102712839/1000000000000 : ℝ)^3613 := by
    have hnat : (2698296033 : ℕ)^4637*1000000000000^3613 ≤ 453102712839^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698296033 5000000000 453102712839 1000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527114273/1000000000 : ℝ), (-878098781/5000000000 : ℝ), (2698296033/5000000000 : ℝ)] ![(5495367844557/12500000000000 : ℝ), (26816964861/250000000000 : ℝ), (453102712839/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527114273/1000000000 : ℝ)|^4637 ≤ (5495367844557/12500000000000 : ℝ)^3613
        have hw : |(527114273/1000000000 : ℝ)|=(527114273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878098781/5000000000 : ℝ)|^4637 ≤ (26816964861/250000000000 : ℝ)^3613
        have hw : |(-878098781/5000000000 : ℝ)|=(878098781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698296033/5000000000 : ℝ)|^4637 ≤ (453102712839/1000000000000 : ℝ)^3613
        have hw : |(2698296033/5000000000 : ℝ)|=(2698296033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271143029/10000000000 : ℝ)*x 0 + (5396592103/10000000000 : ℝ)*x 1 + (-1756197103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271143029/10000000000 : ℝ)^4637 ≤ (43962945956989/100000000000000 : ℝ)^3613 := by
    have hnat : (5271143029 : ℕ)^4637*100000000000000^3613 ≤ 43962945956989^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271143029 10000000000 43962945956989 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396592103/10000000000 : ℝ)^4637 ≤ (45310271682601/100000000000000 : ℝ)^3613 := by
    have hnat : (5396592103 : ℕ)^4637*100000000000000^3613 ≤ 45310271682601^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396592103 10000000000 45310271682601 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1756197103/10000000000 : ℝ)^4637 ≤ (536339117313/5000000000000 : ℝ)^3613 := by
    have hnat : (1756197103 : ℕ)^4637*5000000000000^3613 ≤ 536339117313^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756197103 10000000000 536339117313 5000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271143029/10000000000 : ℝ), (5396592103/10000000000 : ℝ), (-1756197103/10000000000 : ℝ)] ![(43962945956989/100000000000000 : ℝ), (45310271682601/100000000000000 : ℝ), (536339117313/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271143029/10000000000 : ℝ)|^4637 ≤ (43962945956989/100000000000000 : ℝ)^3613
        have hw : |(5271143029/10000000000 : ℝ)|=(5271143029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396592103/10000000000 : ℝ)|^4637 ≤ (45310271682601/100000000000000 : ℝ)^3613
        have hw : |(5396592103/10000000000 : ℝ)|=(5396592103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1756197103/10000000000 : ℝ)|^4637 ≤ (536339117313/5000000000000 : ℝ)^3613
        have hw : |(-1756197103/10000000000 : ℝ)|=(1756197103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1111047533/2500000000 : ℝ)*x 0 + (4149798263/10000000000 : ℝ)*x 1 + (2074899551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1111047533/2500000000 : ℝ)^4637 ≤ (35315850771577/100000000000000 : ℝ)^3613 := by
    have hnat : (1111047533 : ℕ)^4637*100000000000000^3613 ≤ 35315850771577^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111047533 2500000000 35315850771577 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149798263/10000000000 : ℝ)^4637 ≤ (32342070411757/100000000000000 : ℝ)^3613 := by
    have hnat : (4149798263 : ℕ)^4637*100000000000000^3613 ≤ 32342070411757^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149798263 10000000000 32342070411757 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074899551/5000000000 : ℝ)^4637 ≤ (16171039401941/50000000000000 : ℝ)^3613 := by
    have hnat : (2074899551 : ℕ)^4637*50000000000000^3613 ≤ 16171039401941^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074899551 5000000000 16171039401941 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1111047533/2500000000 : ℝ), (4149798263/10000000000 : ℝ), (2074899551/5000000000 : ℝ)] ![(35315850771577/100000000000000 : ℝ), (32342070411757/100000000000000 : ℝ), (16171039401941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1111047533/2500000000 : ℝ)|^4637 ≤ (35315850771577/100000000000000 : ℝ)^3613
        have hw : |(1111047533/2500000000 : ℝ)|=(1111047533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149798263/10000000000 : ℝ)|^4637 ≤ (32342070411757/100000000000000 : ℝ)^3613
        have hw : |(4149798263/10000000000 : ℝ)|=(4149798263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074899551/5000000000 : ℝ)|^4637 ≤ (16171039401941/50000000000000 : ℝ)^3613
        have hw : |(2074899551/5000000000 : ℝ)|=(2074899551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79792481/400000000 : ℝ)*x 0 + (2622527413/5000000000 : ℝ)*x 1 + (5245055159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79792481/400000000 : ℝ)^4637 ≤ (3158053759583/25000000000000 : ℝ)^3613 := by
    have hnat : (79792481 : ℕ)^4637*25000000000000^3613 ≤ 3158053759583^3613*400000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79792481 400000000 3158053759583 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622527413/5000000000 : ℝ)^4637 ≤ (43683890692139/100000000000000 : ℝ)^3613 := by
    have hnat : (2622527413 : ℕ)^4637*100000000000000^3613 ≤ 43683890692139^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622527413 5000000000 43683890692139 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245055159/10000000000 : ℝ)^4637 ≤ (43683894251603/100000000000000 : ℝ)^3613 := by
    have hnat : (5245055159 : ℕ)^4637*100000000000000^3613 ≤ 43683894251603^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245055159 10000000000 43683894251603 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79792481/400000000 : ℝ), (2622527413/5000000000 : ℝ), (5245055159/10000000000 : ℝ)] ![(3158053759583/25000000000000 : ℝ), (43683890692139/100000000000000 : ℝ), (43683894251603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79792481/400000000 : ℝ)|^4637 ≤ (3158053759583/25000000000000 : ℝ)^3613
        have hw : |(-79792481/400000000 : ℝ)|=(79792481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622527413/5000000000 : ℝ)|^4637 ≤ (43683890692139/100000000000000 : ℝ)^3613
        have hw : |(2622527413/5000000000 : ℝ)|=(2622527413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245055159/10000000000 : ℝ)|^4637 ≤ (43683894251603/100000000000000 : ℝ)^3613
        have hw : |(5245055159/10000000000 : ℝ)|=(5245055159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_5 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376184753/10000000000 : ℝ)*x 0 + (-909755551/5000000000 : ℝ)*x 1 + (2622527563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376184753/10000000000 : ℝ)^4637 ≤ (22545242894099/50000000000000 : ℝ)^3613 := by
    have hnat : (5376184753 : ℕ)^4637*50000000000000^3613 ≤ 22545242894099^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376184753 10000000000 22545242894099 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (909755551/5000000000 : ℝ)^4637 ≤ (11225620305979/100000000000000 : ℝ)^3613 := by
    have hnat : (909755551 : ℕ)^4637*100000000000000^3613 ≤ 11225620305979^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909755551 5000000000 11225620305979 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622527563/5000000000 : ℝ)^4637 ≤ (2730243368679/6250000000000 : ℝ)^3613 := by
    have hnat : (2622527563 : ℕ)^4637*6250000000000^3613 ≤ 2730243368679^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622527563 5000000000 2730243368679 6250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376184753/10000000000 : ℝ), (-909755551/5000000000 : ℝ), (2622527563/5000000000 : ℝ)] ![(22545242894099/50000000000000 : ℝ), (11225620305979/100000000000000 : ℝ), (2730243368679/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376184753/10000000000 : ℝ)|^4637 ≤ (22545242894099/50000000000000 : ℝ)^3613
        have hw : |(5376184753/10000000000 : ℝ)|=(5376184753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-909755551/5000000000 : ℝ)|^4637 ≤ (11225620305979/100000000000000 : ℝ)^3613
        have hw : |(-909755551/5000000000 : ℝ)|=(909755551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622527563/5000000000 : ℝ)|^4637 ≤ (2730243368679/6250000000000 : ℝ)^3613
        have hw : |(2622527563/5000000000 : ℝ)|=(2622527563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_6 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376184659/10000000000 : ℝ)*x 0 + (20980221/40000000 : ℝ)*x 1 + (-1819511061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376184659/10000000000 : ℝ)^4637 ≤ (45090484776367/100000000000000 : ℝ)^3613 := by
    have hnat : (5376184659 : ℕ)^4637*100000000000000^3613 ≤ 45090484776367^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376184659 10000000000 45090484776367 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20980221/40000000 : ℝ)^4637 ≤ (4368389522431/10000000000000 : ℝ)^3613 := by
    have hnat : (20980221 : ℕ)^4637*10000000000000^3613 ≤ 4368389522431^3613*40000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20980221 40000000 4368389522431 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1819511061/10000000000 : ℝ)^4637 ≤ (5612809990667/50000000000000 : ℝ)^3613 := by
    have hnat : (1819511061 : ℕ)^4637*50000000000000^3613 ≤ 5612809990667^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819511061 10000000000 5612809990667 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376184659/10000000000 : ℝ), (20980221/40000000 : ℝ), (-1819511061/10000000000 : ℝ)] ![(45090484776367/100000000000000 : ℝ), (4368389522431/10000000000000 : ℝ), (5612809990667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376184659/10000000000 : ℝ)|^4637 ≤ (45090484776367/100000000000000 : ℝ)^3613
        have hw : |(5376184659/10000000000 : ℝ)|=(5376184659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20980221/40000000 : ℝ)|^4637 ≤ (4368389522431/10000000000000 : ℝ)^3613
        have hw : |(20980221/40000000 : ℝ)|=(20980221/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1819511061/10000000000 : ℝ)|^4637 ≤ (5612809990667/50000000000000 : ℝ)^3613
        have hw : |(-1819511061/10000000000 : ℝ)|=(1819511061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_7 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80802611/200000000 : ℝ)*x 0 + (4351701399/10000000000 : ℝ)*x 1 + (2175850331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80802611/200000000 : ℝ)^4637 ≤ (15624624950631/50000000000000 : ℝ)^3613 := by
    have hnat : (80802611 : ℕ)^4637*50000000000000^3613 ≤ 15624624950631^3613*200000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80802611 200000000 15624624950631 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4351701399/10000000000 : ℝ)^4637 ≤ (34375378777323/100000000000000 : ℝ)^3613 := by
    have hnat : (4351701399 : ℕ)^4637*100000000000000^3613 ≤ 34375378777323^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351701399 10000000000 34375378777323 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175850331/5000000000 : ℝ)^4637 ≤ (34375371305527/100000000000000 : ℝ)^3613 := by
    have hnat : (2175850331 : ℕ)^4637*100000000000000^3613 ≤ 34375371305527^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175850331 5000000000 34375371305527 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80802611/200000000 : ℝ), (4351701399/10000000000 : ℝ), (2175850331/5000000000 : ℝ)] ![(15624624950631/50000000000000 : ℝ), (34375378777323/100000000000000 : ℝ), (34375371305527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80802611/200000000 : ℝ)|^4637 ≤ (15624624950631/50000000000000 : ℝ)^3613
        have hw : |(80802611/200000000 : ℝ)|=(80802611/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4351701399/10000000000 : ℝ)|^4637 ≤ (34375378777323/100000000000000 : ℝ)^3613
        have hw : |(4351701399/10000000000 : ℝ)|=(4351701399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2175850331/5000000000 : ℝ)|^4637 ≤ (34375371305527/100000000000000 : ℝ)^3613
        have hw : |(2175850331/5000000000 : ℝ)|=(2175850331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_8 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38145387/200000000 : ℝ)*x 0 + (2569145451/5000000000 : ℝ)*x 1 + (5416861839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38145387/200000000 : ℝ)^4637 ≤ (11925200842033/100000000000000 : ℝ)^3613 := by
    have hnat : (38145387 : ℕ)^4637*100000000000000^3613 ≤ 11925200842033^3613*200000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38145387 200000000 11925200842033 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569145451/5000000000 : ℝ)^4637 ≤ (531824879343/1250000000000 : ℝ)^3613 := by
    have hnat : (2569145451 : ℕ)^4637*1250000000000^3613 ≤ 531824879343^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569145451 5000000000 531824879343 1250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416861839/10000000000 : ℝ)^4637 ≤ (5691101098857/12500000000000 : ℝ)^3613 := by
    have hnat : (5416861839 : ℕ)^4637*12500000000000^3613 ≤ 5691101098857^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416861839 10000000000 5691101098857 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38145387/200000000 : ℝ), (2569145451/5000000000 : ℝ), (5416861839/10000000000 : ℝ)] ![(11925200842033/100000000000000 : ℝ), (531824879343/1250000000000 : ℝ), (5691101098857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38145387/200000000 : ℝ)|^4637 ≤ (11925200842033/100000000000000 : ℝ)^3613
        have hw : |(-38145387/200000000 : ℝ)|=(38145387/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569145451/5000000000 : ℝ)|^4637 ≤ (531824879343/1250000000000 : ℝ)^3613
        have hw : |(2569145451/5000000000 : ℝ)|=(2569145451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416861839/10000000000 : ℝ)|^4637 ≤ (5691101098857/12500000000000 : ℝ)^3613
        have hw : |(5416861839/10000000000 : ℝ)|=(5416861839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_9 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257088593/10000000000 : ℝ)*x 0 + (-873748287/5000000000 : ℝ)*x 1 + (5416862087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257088593/10000000000 : ℝ)^4637 ≤ (4381256241411/10000000000000 : ℝ)^3613 := by
    have hnat : (5257088593 : ℕ)^4637*10000000000000^3613 ≤ 4381256241411^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257088593 10000000000 4381256241411 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873748287/5000000000 : ℝ)^4637 ≤ (10658626104367/100000000000000 : ℝ)^3613 := by
    have hnat : (873748287 : ℕ)^4637*100000000000000^3613 ≤ 10658626104367^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873748287 5000000000 10658626104367 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416862087/10000000000 : ℝ)^4637 ≤ (1821152458643/4000000000000 : ℝ)^3613 := by
    have hnat : (5416862087 : ℕ)^4637*4000000000000^3613 ≤ 1821152458643^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416862087 10000000000 1821152458643 4000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257088593/10000000000 : ℝ), (-873748287/5000000000 : ℝ), (5416862087/10000000000 : ℝ)] ![(4381256241411/10000000000000 : ℝ), (10658626104367/100000000000000 : ℝ), (1821152458643/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257088593/10000000000 : ℝ)|^4637 ≤ (4381256241411/10000000000000 : ℝ)^3613
        have hw : |(5257088593/10000000000 : ℝ)|=(5257088593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-873748287/5000000000 : ℝ)|^4637 ≤ (10658626104367/100000000000000 : ℝ)^3613
        have hw : |(-873748287/5000000000 : ℝ)|=(873748287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416862087/10000000000 : ℝ)|^4637 ≤ (1821152458643/4000000000000 : ℝ)^3613
        have hw : |(5416862087/10000000000 : ℝ)|=(5416862087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_10 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257088721/10000000000 : ℝ)*x 0 + (1354215437/2500000000 : ℝ)*x 1 + (-873748433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257088721/10000000000 : ℝ)^4637 ≤ (43812563783201/100000000000000 : ℝ)^3613 := by
    have hnat : (5257088721 : ℕ)^4637*100000000000000^3613 ≤ 43812563783201^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257088721 10000000000 43812563783201 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354215437/2500000000 : ℝ)^4637 ≤ (45528807809223/100000000000000 : ℝ)^3613 := by
    have hnat : (1354215437 : ℕ)^4637*100000000000000^3613 ≤ 45528807809223^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354215437 2500000000 45528807809223 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873748433/5000000000 : ℝ)^4637 ≤ (133232854877/1250000000000 : ℝ)^3613 := by
    have hnat : (873748433 : ℕ)^4637*1250000000000^3613 ≤ 133232854877^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873748433 5000000000 133232854877 1250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257088721/10000000000 : ℝ), (1354215437/2500000000 : ℝ), (-873748433/5000000000 : ℝ)] ![(43812563783201/100000000000000 : ℝ), (45528807809223/100000000000000 : ℝ), (133232854877/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257088721/10000000000 : ℝ)|^4637 ≤ (43812563783201/100000000000000 : ℝ)^3613
        have hw : |(5257088721/10000000000 : ℝ)|=(5257088721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354215437/2500000000 : ℝ)|^4637 ≤ (45528807809223/100000000000000 : ℝ)^3613
        have hw : |(1354215437/2500000000 : ℝ)|=(1354215437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-873748433/5000000000 : ℝ)|^4637 ≤ (133232854877/1250000000000 : ℝ)^3613
        have hw : |(-873748433/5000000000 : ℝ)|=(873748433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_11 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4497096319/10000000000 : ℝ)*x 0 + (4122756197/10000000000 : ℝ)*x 1 + (2061378229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497096319/10000000000 : ℝ)^4637 ≤ (17928167240643/50000000000000 : ℝ)^3613 := by
    have hnat : (4497096319 : ℕ)^4637*50000000000000^3613 ≤ 17928167240643^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497096319 10000000000 17928167240643 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4122756197/10000000000 : ℝ)^4637 ≤ (3207183144361/10000000000000 : ℝ)^3613 := by
    have hnat : (4122756197 : ℕ)^4637*10000000000000^3613 ≤ 3207183144361^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122756197 10000000000 3207183144361 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061378229/5000000000 : ℝ)^4637 ≤ (16035917024719/50000000000000 : ℝ)^3613 := by
    have hnat : (2061378229 : ℕ)^4637*50000000000000^3613 ≤ 16035917024719^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061378229 5000000000 16035917024719 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497096319/10000000000 : ℝ), (4122756197/10000000000 : ℝ), (2061378229/5000000000 : ℝ)] ![(17928167240643/50000000000000 : ℝ), (3207183144361/10000000000000 : ℝ), (16035917024719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497096319/10000000000 : ℝ)|^4637 ≤ (17928167240643/50000000000000 : ℝ)^3613
        have hw : |(4497096319/10000000000 : ℝ)|=(4497096319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4122756197/10000000000 : ℝ)|^4637 ≤ (3207183144361/10000000000000 : ℝ)^3613
        have hw : |(4122756197/10000000000 : ℝ)|=(4122756197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2061378229/5000000000 : ℝ)|^4637 ≤ (16035917024719/50000000000000 : ℝ)^3613
        have hw : |(2061378229/5000000000 : ℝ)|=(2061378229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_12 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-166901617/1000000000 : ℝ)*x 0 + (2750050599/5000000000 : ℝ)*x 1 + (1307501453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166901617/1000000000 : ℝ)^4637 ≤ (2009645919447/20000000000000 : ℝ)^3613 := by
    have hnat : (166901617 : ℕ)^4637*20000000000000^3613 ≤ 2009645919447^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166901617 1000000000 2009645919447 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750050599/5000000000 : ℝ)^4637 ≤ (11607168598427/25000000000000 : ℝ)^3613 := by
    have hnat : (2750050599 : ℕ)^4637*25000000000000^3613 ≤ 11607168598427^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750050599 5000000000 11607168598427 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307501453/2500000000 : ℝ)^4637 ≤ (10880773998769/25000000000000 : ℝ)^3613 := by
    have hnat : (1307501453 : ℕ)^4637*25000000000000^3613 ≤ 10880773998769^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307501453 2500000000 10880773998769 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166901617/1000000000 : ℝ), (2750050599/5000000000 : ℝ), (1307501453/2500000000 : ℝ)] ![(2009645919447/20000000000000 : ℝ), (11607168598427/25000000000000 : ℝ), (10880773998769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166901617/1000000000 : ℝ)|^4637 ≤ (2009645919447/20000000000000 : ℝ)^3613
        have hw : |(-166901617/1000000000 : ℝ)|=(166901617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750050599/5000000000 : ℝ)|^4637 ≤ (11607168598427/25000000000000 : ℝ)^3613
        have hw : |(2750050599/5000000000 : ℝ)|=(2750050599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307501453/2500000000 : ℝ)|^4637 ≤ (10880773998769/25000000000000 : ℝ)^3613
        have hw : |(1307501453/2500000000 : ℝ)|=(1307501453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_13 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077323623/2000000000 : ℝ)*x 0 + (-1825628861/10000000000 : ℝ)*x 1 + (5230005457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077323623/2000000000 : ℝ)^4637 ≤ (4520282296479/10000000000000 : ℝ)^3613 := by
    have hnat : (1077323623 : ℕ)^4637*10000000000000^3613 ≤ 4520282296479^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077323623 2000000000 4520282296479 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1825628861/10000000000 : ℝ)^4637 ≤ (225481696379/2000000000000 : ℝ)^3613 := by
    have hnat : (1825628861 : ℕ)^4637*2000000000000^3613 ≤ 225481696379^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825628861 10000000000 225481696379 2000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230005457/10000000000 : ℝ)^4637 ≤ (2176154610177/5000000000000 : ℝ)^3613 := by
    have hnat : (5230005457 : ℕ)^4637*5000000000000^3613 ≤ 2176154610177^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230005457 10000000000 2176154610177 5000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077323623/2000000000 : ℝ), (-1825628861/10000000000 : ℝ), (5230005457/10000000000 : ℝ)] ![(4520282296479/10000000000000 : ℝ), (225481696379/2000000000000 : ℝ), (2176154610177/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077323623/2000000000 : ℝ)|^4637 ≤ (4520282296479/10000000000000 : ℝ)^3613
        have hw : |(1077323623/2000000000 : ℝ)|=(1077323623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1825628861/10000000000 : ℝ)|^4637 ≤ (225481696379/2000000000000 : ℝ)^3613
        have hw : |(-1825628861/10000000000 : ℝ)|=(1825628861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230005457/10000000000 : ℝ)|^4637 ≤ (2176154610177/5000000000000 : ℝ)^3613
        have hw : |(5230005457/10000000000 : ℝ)|=(5230005457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_14 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269330873/500000000 : ℝ)*x 0 + (5230006037/10000000000 : ℝ)*x 1 + (-182562897/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269330873/500000000 : ℝ)^4637 ≤ (9040563182079/20000000000000 : ℝ)^3613 := by
    have hnat : (269330873 : ℕ)^4637*20000000000000^3613 ≤ 9040563182079^3613*500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269330873 500000000 9040563182079 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230006037/10000000000 : ℝ)^4637 ≤ (43523098398161/100000000000000 : ℝ)^3613 := by
    have hnat : (5230006037 : ℕ)^4637*100000000000000^3613 ≤ 43523098398161^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230006037 10000000000 43523098398161 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182562897/1000000000 : ℝ)^4637 ≤ (2818521420713/25000000000000 : ℝ)^3613 := by
    have hnat : (182562897 : ℕ)^4637*25000000000000^3613 ≤ 2818521420713^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182562897 1000000000 2818521420713 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269330873/500000000 : ℝ), (5230006037/10000000000 : ℝ), (-182562897/1000000000 : ℝ)] ![(9040563182079/20000000000000 : ℝ), (43523098398161/100000000000000 : ℝ), (2818521420713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269330873/500000000 : ℝ)|^4637 ≤ (9040563182079/20000000000000 : ℝ)^3613
        have hw : |(269330873/500000000 : ℝ)|=(269330873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230006037/10000000000 : ℝ)|^4637 ≤ (43523098398161/100000000000000 : ℝ)^3613
        have hw : |(5230006037/10000000000 : ℝ)|=(5230006037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-182562897/1000000000 : ℝ)|^4637 ≤ (2818521420713/25000000000000 : ℝ)^3613
        have hw : |(-182562897/1000000000 : ℝ)|=(182562897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_box_15 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (999784387/2500000000 : ℝ)*x 0 + (437172821/1000000000 : ℝ)*x 1 + (546466101/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999784387/2500000000 : ℝ)^4637 ≤ (3855362912631/12500000000000 : ℝ)^3613 := by
    have hnat : (999784387 : ℕ)^4637*12500000000000^3613 ≤ 3855362912631^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999784387 2500000000 3855362912631 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437172821/1000000000 : ℝ)^4637 ≤ (17289272654151/50000000000000 : ℝ)^3613 := by
    have hnat : (437172821 : ℕ)^4637*50000000000000^3613 ≤ 17289272654151^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437172821 1000000000 17289272654151 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546466101/1250000000 : ℝ)^4637 ≤ (17289275689397/50000000000000 : ℝ)^3613 := by
    have hnat : (546466101 : ℕ)^4637*50000000000000^3613 ≤ 17289275689397^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546466101 1250000000 17289275689397 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(999784387/2500000000 : ℝ), (437172821/1000000000 : ℝ), (546466101/1250000000 : ℝ)] ![(3855362912631/12500000000000 : ℝ), (17289272654151/50000000000000 : ℝ), (17289275689397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(999784387/2500000000 : ℝ)|^4637 ≤ (3855362912631/12500000000000 : ℝ)^3613
        have hw : |(999784387/2500000000 : ℝ)|=(999784387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(437172821/1000000000 : ℝ)|^4637 ≤ (17289272654151/50000000000000 : ℝ)^3613
        have hw : |(437172821/1000000000 : ℝ)|=(437172821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546466101/1250000000 : ℝ)|^4637 ≤ (17289275689397/50000000000000 : ℝ)^3613
        have hw : |(546466101/1250000000 : ℝ)|=(546466101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63829/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58903/100000 : ℝ) ∧ (2023/2500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43183/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11121/100000 : ℝ) ^ (4635/1024 : ℝ) ≤ (4813896838906103/100000000000000000000 : ℝ) := by
    have hpowers : (11121/100000 : ℝ)^4635 ≤ (4813896838906103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11121 : ℕ)^4635*100000000000000000000^1024 ≤ 4813896838906103^1024*100000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11121 100000 4813896838906103 100000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11121/100000 : ℝ)) (X := (4813896838906103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4635/1024 : ℝ) ≤ (10766727804045357/50000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4635 ≤ (10766727804045357/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4635*50000000000000000000^1024 ≤ 10766727804045357^1024*25000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 10766727804045357 50000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (10766727804045357/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004813896838906103/50000000000000000000 : ℝ) ≤ (10000212696677521/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (50004813896838906103/50000000000000000000 : ℝ)^1024 ≤ (10000212696677521/10000000000000000 : ℝ)^4635 := by
      have hnat : (50004813896838906103 : ℕ)^1024*10000000000000000^4635 ≤ 10000212696677521^4635*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004813896838906103 50000000000000000000 10000212696677521 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000212696677521/10000000000000000 : ℝ)) (X := (50004813896838906103/50000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026347352446996817/100000000000000000000 : ℝ) ≤ (10000582026328943/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (100026347352446996817/100000000000000000000 : ℝ)^1024 ≤ (10000582026328943/10000000000000000 : ℝ)^4635 := by
      have hnat : (100026347352446996817 : ℕ)^1024*10000000000000000^4635 ≤ 10000582026328943^4635*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026347352446996817 100000000000000000000 10000582026328943 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000582026328943/10000000000000000 : ℝ)) (X := (100026347352446996817/100000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010766727804045357/25000000000000000000 : ℝ) ≤ (2000190271196073/2000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (25010766727804045357/25000000000000000000 : ℝ)^1024 ≤ (2000190271196073/2000000000000000 : ℝ)^4635 := by
      have hnat : (25010766727804045357 : ℕ)^1024*2000000000000000^4635 ≤ 2000190271196073^4635*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010766727804045357 25000000000000000000 2000190271196073 2000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000190271196073/2000000000000000 : ℝ)) (X := (25010766727804045357/25000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4813896838906103/100000000000000000000 : ℝ) ≤ ((43622713365497095999/43630000000000000000 : ℝ)+2*(184664825711/218150000000000 : ℝ)*(11121/100000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (43622713365497095999/43630000000000000000 : ℝ)+2*(184664825711/218150000000000 : ℝ)*(11121/100000 : ℝ)=(10000212696677521/10000000000000000 : ℝ) by norm_num, show 1+2*(4813896838906103/100000000000000000000 : ℝ)=(50004813896838906103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10766727804045357/50000000000000000000 : ℝ)+(4813896838906103/100000000000000000000 : ℝ) ≤ ((43622713365497095999/43630000000000000000 : ℝ)+(184664825711/218150000000000 : ℝ)*((3871/25000 : ℝ)+(11121/100000 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (43622713365497095999/43630000000000000000 : ℝ)+(184664825711/218150000000000 : ℝ)*((3871/25000 : ℝ)+(11121/100000 : ℝ))=(10000582026328943/10000000000000000 : ℝ) by norm_num, show 1+(10766727804045357/50000000000000000000 : ℝ)+(4813896838906103/100000000000000000000 : ℝ)=(100026347352446996817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10766727804045357/50000000000000000000 : ℝ) ≤ ((43622713365497095999/43630000000000000000 : ℝ)+2*(184664825711/218150000000000 : ℝ)*(3871/25000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (43622713365497095999/43630000000000000000 : ℝ)+2*(184664825711/218150000000000 : ℝ)*(3871/25000 : ℝ)=(2000190271196073/2000000000000000 : ℝ) by norm_num, show 1+2*(10766727804045357/50000000000000000000 : ℝ)=(25010766727804045357/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43622713365497095999/43630000000000000000 : ℝ)*(X 1 0+X 2 0)+(184664825711/218150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43622713365497095999/43630000000000000000 : ℝ)) (alpha := (184664825711/218150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43622713365497095999/43630000000000000000 : ℝ)*(X 0 1+X 2 1)+(184664825711/218150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43622713365497095999/43630000000000000000 : ℝ)) (alpha := (184664825711/218150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43622713365497095999/43630000000000000000 : ℝ)*(X 0 2+X 1 2)+(184664825711/218150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43622713365497095999/43630000000000000000 : ℝ)) (alpha := (184664825711/218150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1581812103/10000000000 : ℝ)*X 0 0+(5396591171/10000000000 : ℝ)*X 0 1+(5396591211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((527114273/1000000000 : ℝ)*X 1 0+(-878098781/5000000000 : ℝ)*X 1 1+(2698296033/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271143029/10000000000 : ℝ)*X 2 0+(5396592103/10000000000 : ℝ)*X 2 1+(-1756197103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1111047533/2500000000 : ℝ)*X 0 0+(4149798263/10000000000 : ℝ)*X 0 1+(2074899551/5000000000 : ℝ)*X 0 2+(1111047533/2500000000 : ℝ)*X 1 0+(4149798263/10000000000 : ℝ)*X 1 1+(2074899551/5000000000 : ℝ)*X 1 2+(1111047533/2500000000 : ℝ)*X 2 0+(4149798263/10000000000 : ℝ)*X 2 1+(2074899551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-79792481/400000000 : ℝ)*X 0 0+(2622527413/5000000000 : ℝ)*X 0 1+(5245055159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5376184753/10000000000 : ℝ)*X 1 0+(-909755551/5000000000 : ℝ)*X 1 1+(2622527563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5376184659/10000000000 : ℝ)*X 2 0+(20980221/40000000 : ℝ)*X 2 1+(-1819511061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((80802611/200000000 : ℝ)*X 0 0+(4351701399/10000000000 : ℝ)*X 0 1+(2175850331/5000000000 : ℝ)*X 0 2+(80802611/200000000 : ℝ)*X 1 0+(4351701399/10000000000 : ℝ)*X 1 1+(2175850331/5000000000 : ℝ)*X 1 2+(80802611/200000000 : ℝ)*X 2 0+(4351701399/10000000000 : ℝ)*X 2 1+(2175850331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-38145387/200000000 : ℝ)*X 0 0+(2569145451/5000000000 : ℝ)*X 0 1+(5416861839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257088593/10000000000 : ℝ)*X 1 0+(-873748287/5000000000 : ℝ)*X 1 1+(5416862087/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257088721/10000000000 : ℝ)*X 2 0+(1354215437/2500000000 : ℝ)*X 2 1+(-873748433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4497096319/10000000000 : ℝ)*X 0 0+(4122756197/10000000000 : ℝ)*X 0 1+(2061378229/5000000000 : ℝ)*X 0 2+(4497096319/10000000000 : ℝ)*X 1 0+(4122756197/10000000000 : ℝ)*X 1 1+(2061378229/5000000000 : ℝ)*X 1 2+(4497096319/10000000000 : ℝ)*X 2 0+(4122756197/10000000000 : ℝ)*X 2 1+(2061378229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-166901617/1000000000 : ℝ)*X 0 0+(2750050599/5000000000 : ℝ)*X 0 1+(1307501453/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1077323623/2000000000 : ℝ)*X 1 0+(-1825628861/10000000000 : ℝ)*X 1 1+(5230005457/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((269330873/500000000 : ℝ)*X 2 0+(5230006037/10000000000 : ℝ)*X 2 1+(-182562897/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((999784387/2500000000 : ℝ)*X 0 0+(437172821/1000000000 : ℝ)*X 0 1+(546466101/1250000000 : ℝ)*X 0 2+(999784387/2500000000 : ℝ)*X 1 0+(437172821/1000000000 : ℝ)*X 1 1+(546466101/1250000000 : ℝ)*X 1 2+(999784387/2500000000 : ℝ)*X 2 0+(437172821/1000000000 : ℝ)*X 2 1+(546466101/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63829/100000 : ℝ) ≤ (-1392367410119851942641590634299733/2181500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23341791/50000000000000 : ℝ)*(lower0) + (56579969/100000000000000 : ℝ)*(upper1) + (4377607/100000000000000 : ℝ)*(lower4) + (2307775888981363/100000000000000 : ℝ)*(major0) + (2307775888981363/100000000000000 : ℝ)*(major1) + (2307775888981363/100000000000000 : ℝ)*(major2) + (652676093501497/20000000000000 : ℝ)*(sp4) + (3263350027766621/100000000000000 : ℝ)*(sp5) + (1631662409456213/50000000000000 : ℝ)*(sp6) + (1373426952715177/100000000000000 : ℝ)*(sp7) + (73464789/25000000000000 : ℝ)*(sp12) + (1536680001/5000000000000 : ℝ)*(sp13) + (11188490843/20000000000000 : ℝ)*(sp14) + (4861604421/25000000000000 : ℝ)*(sp15) + (1373446399132861/100000000000000 : ℝ)*(f.failure) + (1631690380683321/50000000000000 : ℝ)*(f.sum) + (69374798506469/21815000000000000000000000000 : ℝ)*base66 + (17699437866308466637/4363000000000000000000000000000000 : ℝ)*base67 + (39244246560772466637/4363000000000000000000000000000000 : ℝ)*base69 + (2040158205066466637/4363000000000000000000000000000000 : ℝ)*base71 + (86139585954129/21815000000000000000000000000 : ℝ)*base74 + (13924542033335466637/4363000000000000000000000000000000 : ℝ)*base75 + (18897155297343466637/4363000000000000000000000000000000 : ℝ)*base77 + (9067718120917466637/4363000000000000000000000000000000 : ℝ)*base79 + (10831367854933/2726875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (186059/100000000000000000000 : ℝ)*base90 + (186059/100000000000000000000 : ℝ)*base92 + (186059/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58903/100000 : ℝ) ≤ (1285013183384891948472996713839929/2181500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144359669/100000000000000 : ℝ)*(lower1) + (80703519/100000000000000 : ℝ)*(lower3) + (3745577/2500000000000 : ℝ)*(upper4) + (17058643/100000000000000 : ℝ)*(upper5) + (2388005731025357/100000000000000 : ℝ)*(major0) + (2388005731025357/100000000000000 : ℝ)*(major1) + (2388005731025357/100000000000000 : ℝ)*(major2) + (667036436332443/20000000000000 : ℝ)*(sp0) + (833791891159253/25000000000000 : ℝ)*(sp1) + (1667581397468429/50000000000000 : ℝ)*(sp2) + (1421163831111881/100000000000000 : ℝ)*(sp3) + (14617025203/100000000000000 : ℝ)*(sp5) + (19386725357/100000000000000 : ℝ)*(sp6) + (3804997561/12500000000000 : ℝ)*(sp11) + (1421194271092369/100000000000000 : ℝ)*(f.failure) + (667036436332443/20000000000000 : ℝ)*(f.sum) + (54809587946169/21815000000000000000000000000 : ℝ)*base65 + (50060650505645646643/4363000000000000000000000000000000 : ℝ)*base67 + (50424318580455353357/4363000000000000000000000000000000 : ℝ)*base70 + (28808547405268646643/4363000000000000000000000000000000 : ℝ)*base71 + (123922026051619/21815000000000000000000000000 : ℝ)*base73 + (24925615887270353357/4363000000000000000000000000000000 : ℝ)*base76 + (46190293669353357/4363000000000000000000000000000000 : ℝ)*base78 + (5498240268171353357/4363000000000000000000000000000000 : ℝ)*base80 + (6530104727429/21815000000000000000000000000 : ℝ)*base81 + (124311/100000000000000000000 : ℝ)*base90 + (124311/100000000000000000000 : ℝ)*base92 + (124311/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2023/2500 : ℝ) ≤ (882663048868771749275867521579041/1090750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43526283/100000000000000 : ℝ)*(upper0) + (9278009/25000000000000 : ℝ)*(upper1) + (75994387/100000000000000 : ℝ)*(upper2) + (1373979/20000000000000 : ℝ)*(upper4) + (1287219283270551/50000000000000 : ℝ)*(major0) + (1287219283270551/50000000000000 : ℝ)*(major1) + (1287219283270551/50000000000000 : ℝ)*(major2) + (123223609061/100000000000000 : ℝ)*(sp1) + (5168058377/12500000000000 : ℝ)*(sp2) + (7196259569/100000000000000 : ℝ)*(sp4) + (3589748104536531/100000000000000 : ℝ)*(sp8) + (1794816038593519/50000000000000 : ℝ)*(sp9) + (897428489082271/25000000000000 : ℝ)*(sp10) + (1532147638722989/100000000000000 : ℝ)*(sp11) + (1532147638722989/100000000000000 : ℝ)*(f.failure) + (35897553007961/1000000000000 : ℝ)*(f.sum) + (67226131786751/5453750000000000000000000000 : ℝ)*base65 + (1740955394814674551/2181500000000000000000000000000000 : ℝ)*base68 + (21080686212584174551/2181500000000000000000000000000000 : ℝ)*base70 + (38545320616343674551/2181500000000000000000000000000000 : ℝ)*base72 + (13297810299241/21815000000000000000000000000 : ℝ)*base74 + (981286206972174551/2181500000000000000000000000000000 : ℝ)*base76 + (25281711096309674551/2181500000000000000000000000000000 : ℝ)*base78 + (13113076770920674551/2181500000000000000000000000000000 : ℝ)*base80 + (34741656053747/10907500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (679909/100000000000000000000 : ℝ)*base89 + (679909/100000000000000000000 : ℝ)*base91 + (679909/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-43183/50000 : ℝ) ≤ (-1884026197858427026291978291329483/2181500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26542127/20000000000000 : ℝ)*(upper3) + (8507851/5000000000000 : ℝ)*(lower4) + (142984603/100000000000000 : ℝ)*(upper5) + (2614934910299161/100000000000000 : ℝ)*(major0) + (2614934910299161/100000000000000 : ℝ)*(major1) + (2614934910299161/100000000000000 : ℝ)*(major2) + (9756109289/100000000000000 : ℝ)*(sp4) + (18527216051/10000000000000 : ℝ)*(sp5) + (115932788273/100000000000000 : ℝ)*(sp6) + (112507978181/100000000000000 : ℝ)*(sp7) + (370239942223019/10000000000000 : ℝ)*(sp12) + (3702223906178969/100000000000000 : ℝ)*(sp13) + (1851146622775603/50000000000000 : ℝ)*(sp14) + (389034016524777/25000000000000 : ℝ)*(sp15) + (1556248574077289/100000000000000 : ℝ)*(f.failure) + (3702409178339479/100000000000000 : ℝ)*(f.sum) + (38466531662393/21815000000000000000000000000 : ℝ)*base66 + (35786941863058643161/4363000000000000000000000000000000 : ℝ)*base68 + (17992979539449356839/4363000000000000000000000000000000 : ℝ)*base69 + (3821448392716643161/4363000000000000000000000000000000 : ℝ)*base72 + (898717987911/170429687500000000000000000 : ℝ)*base74 + (17869885094456643161/4363000000000000000000000000000000 : ℝ)*base76 + (5414005146957356839/4363000000000000000000000000000000 : ℝ)*base77 + (10071714531352643161/4363000000000000000000000000000000 : ℝ)*base80 + (101601706289347/21815000000000000000000000000 : ℝ)*base81 + (238209/100000000000000000000 : ℝ)*base89 + (238209/100000000000000000000 : ℝ)*base91 + (238209/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1570_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63829/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58903/100000 : ℝ) else (2023/2500 : ℝ) ≤ X j i ∧ X j i ≤ (43183/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1570_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1570_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63829/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58903/100000 : ℝ) else (2023/2500 : ℝ) ≤ X j i ∧ X j i ≤ (43183/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1570_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1570_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63829/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58903/100000 : ℝ) else (2023/2500 : ℝ) ≤ X j i ∧ X j i ≤ (43183/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1570_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
