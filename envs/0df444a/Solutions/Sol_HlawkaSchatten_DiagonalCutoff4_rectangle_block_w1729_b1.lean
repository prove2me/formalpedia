-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1729_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:06:20.000634+00:00
-- url     : https://prove2.me/submissions/536685bd-6e1a-4911-aacb-347d97f54899

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
theorem support_rectangle_w1729_s3_0 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-336570563/2500000000 : ℝ)*x 0 + (341136021/625000000 : ℝ)*x 1 + (5140275237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336570563/2500000000 : ℝ)^5455 ≤ (8469939023903/100000000000000 : ℝ)^4431 := by
    have hnat : (336570563 : ℕ)^5455*100000000000000^4431 ≤ 8469939023903^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336570563 2500000000 8469939023903 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341136021/625000000 : ℝ)^5455 ≤ (47454728948947/100000000000000 : ℝ)^4431 := by
    have hnat : (341136021 : ℕ)^5455*100000000000000^4431 ≤ 47454728948947^4431*625000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341136021 625000000 47454728948947 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140275237/10000000000 : ℝ)^5455 ≤ (44075332012169/100000000000000 : ℝ)^4431 := by
    have hnat : (5140275237 : ℕ)^5455*100000000000000^4431 ≤ 44075332012169^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140275237 10000000000 44075332012169 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-336570563/2500000000 : ℝ), (341136021/625000000 : ℝ), (5140275237/10000000000 : ℝ)] ![(8469939023903/100000000000000 : ℝ), (47454728948947/100000000000000 : ℝ), (44075332012169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-336570563/2500000000 : ℝ)|^5455 ≤ (8469939023903/100000000000000 : ℝ)^4431
        have hw : |(-336570563/2500000000 : ℝ)|=(336570563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341136021/625000000 : ℝ)|^5455 ≤ (47454728948947/100000000000000 : ℝ)^4431
        have hw : |(341136021/625000000 : ℝ)|=(341136021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140275237/10000000000 : ℝ)|^5455 ≤ (44075332012169/100000000000000 : ℝ)^4431
        have hw : |(5140275237/10000000000 : ℝ)|=(5140275237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s3_1 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337129367/10000000000 : ℝ)*x 0 + (-755437127/5000000000 : ℝ)*x 1 + (5140275237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337129367/10000000000 : ℝ)^5455 ≤ (9232488899731/20000000000000 : ℝ)^4431 := by
    have hnat : (5337129367 : ℕ)^5455*20000000000000^4431 ≤ 9232488899731^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337129367 10000000000 9232488899731 20000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (755437127/5000000000 : ℝ)^5455 ≤ (1220277933891/12500000000000 : ℝ)^4431 := by
    have hnat : (755437127 : ℕ)^5455*12500000000000^4431 ≤ 1220277933891^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755437127 5000000000 1220277933891 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140275237/10000000000 : ℝ)^5455 ≤ (44075332012169/100000000000000 : ℝ)^4431 := by
    have hnat : (5140275237 : ℕ)^5455*100000000000000^4431 ≤ 44075332012169^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140275237 10000000000 44075332012169 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337129367/10000000000 : ℝ), (-755437127/5000000000 : ℝ), (5140275237/10000000000 : ℝ)] ![(9232488899731/20000000000000 : ℝ), (1220277933891/12500000000000 : ℝ), (44075332012169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337129367/10000000000 : ℝ)|^5455 ≤ (9232488899731/20000000000000 : ℝ)^4431
        have hw : |(5337129367/10000000000 : ℝ)|=(5337129367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-755437127/5000000000 : ℝ)|^5455 ≤ (1220277933891/12500000000000 : ℝ)^4431
        have hw : |(-755437127/5000000000 : ℝ)|=(755437127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140275237/10000000000 : ℝ)|^5455 ≤ (44075332012169/100000000000000 : ℝ)^4431
        have hw : |(5140275237/10000000000 : ℝ)|=(5140275237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s3_2 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337129361/10000000000 : ℝ)*x 0 + (5140275239/10000000000 : ℝ)*x 1 + (-1510874259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337129361/10000000000 : ℝ)^5455 ≤ (23081222217383/50000000000000 : ℝ)^4431 := by
    have hnat : (5337129361 : ℕ)^5455*50000000000000^4431 ≤ 23081222217383^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337129361 10000000000 23081222217383 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140275239/10000000000 : ℝ)^5455 ≤ (22037666016641/50000000000000 : ℝ)^4431 := by
    have hnat : (5140275239 : ℕ)^5455*50000000000000^4431 ≤ 22037666016641^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140275239 10000000000 22037666016641 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510874259/10000000000 : ℝ)^5455 ≤ (97622235109/1000000000000 : ℝ)^4431 := by
    have hnat : (1510874259 : ℕ)^5455*1000000000000^4431 ≤ 97622235109^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510874259 10000000000 97622235109 1000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337129361/10000000000 : ℝ), (5140275239/10000000000 : ℝ), (-1510874259/10000000000 : ℝ)] ![(23081222217383/50000000000000 : ℝ), (22037666016641/50000000000000 : ℝ), (97622235109/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337129361/10000000000 : ℝ)|^5455 ≤ (23081222217383/50000000000000 : ℝ)^4431
        have hw : |(5337129361/10000000000 : ℝ)|=(5337129361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140275239/10000000000 : ℝ)|^5455 ≤ (22037666016641/50000000000000 : ℝ)^4431
        have hw : |(5140275239/10000000000 : ℝ)|=(5140275239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1510874259/10000000000 : ℝ)|^5455 ≤ (97622235109/1000000000000 : ℝ)^4431
        have hw : |(-1510874259/10000000000 : ℝ)|=(1510874259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s3_3 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1020262081/2500000000 : ℝ)*x 0 + (3617256811/10000000000 : ℝ)*x 1 + (4578972969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020262081/2500000000 : ℝ)^5455 ≤ (518371924821/1562500000000 : ℝ)^4431 := by
    have hnat : (1020262081 : ℕ)^5455*1562500000000^4431 ≤ 518371924821^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020262081 2500000000 518371924821 1562500000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3617256811/10000000000 : ℝ)^5455 ≤ (28597048890959/100000000000000 : ℝ)^4431 := by
    have hnat : (3617256811 : ℕ)^5455*100000000000000^4431 ≤ 28597048890959^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3617256811 10000000000 28597048890959 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578972969/10000000000 : ℝ)^5455 ≤ (7645429581167/20000000000000 : ℝ)^4431 := by
    have hnat : (4578972969 : ℕ)^5455*20000000000000^4431 ≤ 7645429581167^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578972969 10000000000 7645429581167 20000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020262081/2500000000 : ℝ), (3617256811/10000000000 : ℝ), (4578972969/10000000000 : ℝ)] ![(518371924821/1562500000000 : ℝ), (28597048890959/100000000000000 : ℝ), (7645429581167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020262081/2500000000 : ℝ)|^5455 ≤ (518371924821/1562500000000 : ℝ)^4431
        have hw : |(1020262081/2500000000 : ℝ)|=(1020262081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3617256811/10000000000 : ℝ)|^5455 ≤ (28597048890959/100000000000000 : ℝ)^4431
        have hw : |(3617256811/10000000000 : ℝ)|=(3617256811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578972969/10000000000 : ℝ)|^5455 ≤ (7645429581167/20000000000000 : ℝ)^4431
        have hw : |(4578972969/10000000000 : ℝ)|=(4578972969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s3_4 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1346423147/10000000000 : ℝ)*x 0 + (1285963601/2500000000 : ℝ)*x 1 + (5454543943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346423147/10000000000 : ℝ)^5455 ≤ (8471030308439/100000000000000 : ℝ)^4431 := by
    have hnat : (1346423147 : ℕ)^5455*100000000000000^4431 ≤ 8471030308439^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346423147 10000000000 8471030308439 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285963601/2500000000 : ℝ)^5455 ≤ (1764524679421/4000000000000 : ℝ)^4431 := by
    have hnat : (1285963601 : ℕ)^5455*4000000000000^4431 ≤ 1764524679421^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285963601 2500000000 1764524679421 4000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454543943/10000000000 : ℝ)^5455 ≤ (47415852698911/100000000000000 : ℝ)^4431 := by
    have hnat : (5454543943 : ℕ)^5455*100000000000000^4431 ≤ 47415852698911^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454543943 10000000000 47415852698911 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1346423147/10000000000 : ℝ), (1285963601/2500000000 : ℝ), (5454543943/10000000000 : ℝ)] ![(8471030308439/100000000000000 : ℝ), (1764524679421/4000000000000 : ℝ), (47415852698911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1346423147/10000000000 : ℝ)|^5455 ≤ (8471030308439/100000000000000 : ℝ)^4431
        have hw : |(-1346423147/10000000000 : ℝ)|=(1346423147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285963601/2500000000 : ℝ)|^5455 ≤ (1764524679421/4000000000000 : ℝ)^4431
        have hw : |(1285963601/2500000000 : ℝ)|=(1285963601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454543943/10000000000 : ℝ)|^5455 ≤ (47415852698911/100000000000000 : ℝ)^4431
        have hw : |(5454543943/10000000000 : ℝ)|=(5454543943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s3_5 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050409519/2000000000 : ℝ)*x 0 + (-598302777/5000000000 : ℝ)*x 1 + (272727197/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050409519/2000000000 : ℝ)^5455 ≤ (11314539222233/25000000000000 : ℝ)^4431 := by
    have hnat : (1050409519 : ℕ)^5455*25000000000000^4431 ≤ 11314539222233^4431*2000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050409519 2000000000 11314539222233 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598302777/5000000000 : ℝ)^5455 ≤ (366299521361/5000000000000 : ℝ)^4431 := by
    have hnat : (598302777 : ℕ)^5455*5000000000000^4431 ≤ 366299521361^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598302777 5000000000 366299521361 5000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272727197/500000000 : ℝ)^5455 ≤ (23707926333403/50000000000000 : ℝ)^4431 := by
    have hnat : (272727197 : ℕ)^5455*50000000000000^4431 ≤ 23707926333403^4431*500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272727197 500000000 23707926333403 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050409519/2000000000 : ℝ), (-598302777/5000000000 : ℝ), (272727197/500000000 : ℝ)] ![(11314539222233/25000000000000 : ℝ), (366299521361/5000000000000 : ℝ), (23707926333403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050409519/2000000000 : ℝ)|^5455 ≤ (11314539222233/25000000000000 : ℝ)^4431
        have hw : |(1050409519/2000000000 : ℝ)|=(1050409519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-598302777/5000000000 : ℝ)|^5455 ≤ (366299521361/5000000000000 : ℝ)^4431
        have hw : |(-598302777/5000000000 : ℝ)|=(598302777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272727197/500000000 : ℝ)|^5455 ≤ (23707926333403/50000000000000 : ℝ)^4431
        have hw : |(272727197/500000000 : ℝ)|=(272727197/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s3_6 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626023797/5000000000 : ℝ)*x 0 + (2727271971/5000000000 : ℝ)*x 1 + (-1196605553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626023797/5000000000 : ℝ)^5455 ≤ (11314539219581/25000000000000 : ℝ)^4431 := by
    have hnat : (2626023797 : ℕ)^5455*25000000000000^4431 ≤ 11314539219581^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626023797 5000000000 11314539219581 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727271971/5000000000 : ℝ)^5455 ≤ (47415852688209/100000000000000 : ℝ)^4431 := by
    have hnat : (2727271971 : ℕ)^5455*100000000000000^4431 ≤ 47415852688209^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727271971 5000000000 47415852688209 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196605553/10000000000 : ℝ)^5455 ≤ (7325990419683/100000000000000 : ℝ)^4431 := by
    have hnat : (1196605553 : ℕ)^5455*100000000000000^4431 ≤ 7325990419683^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196605553 10000000000 7325990419683 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626023797/5000000000 : ℝ), (2727271971/5000000000 : ℝ), (-1196605553/10000000000 : ℝ)] ![(11314539219581/25000000000000 : ℝ), (47415852688209/100000000000000 : ℝ), (7325990419683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626023797/5000000000 : ℝ)|^5455 ≤ (11314539219581/25000000000000 : ℝ)^4431
        have hw : |(2626023797/5000000000 : ℝ)|=(2626023797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727271971/5000000000 : ℝ)|^5455 ≤ (47415852688209/100000000000000 : ℝ)^4431
        have hw : |(2727271971/5000000000 : ℝ)|=(2727271971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1196605553/10000000000 : ℝ)|^5455 ≤ (7325990419683/100000000000000 : ℝ)^4431
        have hw : |(-1196605553/10000000000 : ℝ)|=(1196605553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s3_7 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1020368641/2500000000 : ℝ)*x 0 + (4568145259/10000000000 : ℝ)*x 1 + (453530693/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020368641/2500000000 : ℝ)^5455 ≤ (16590034502463/50000000000000 : ℝ)^4431 := by
    have hnat : (1020368641 : ℕ)^5455*50000000000000^4431 ≤ 16590034502463^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020368641 2500000000 16590034502463 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4568145259/10000000000 : ℝ)^5455 ≤ (9528973537283/25000000000000 : ℝ)^4431 := by
    have hnat : (4568145259 : ℕ)^5455*25000000000000^4431 ≤ 9528973537283^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568145259 10000000000 9528973537283 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453530693/1250000000 : ℝ)^5455 ≤ (28704036825503/100000000000000 : ℝ)^4431 := by
    have hnat : (453530693 : ℕ)^5455*100000000000000^4431 ≤ 28704036825503^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453530693 1250000000 28704036825503 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020368641/2500000000 : ℝ), (4568145259/10000000000 : ℝ), (453530693/1250000000 : ℝ)] ![(16590034502463/50000000000000 : ℝ), (9528973537283/25000000000000 : ℝ), (28704036825503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020368641/2500000000 : ℝ)|^5455 ≤ (16590034502463/50000000000000 : ℝ)^4431
        have hw : |(1020368641/2500000000 : ℝ)|=(1020368641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4568145259/10000000000 : ℝ)|^5455 ≤ (9528973537283/25000000000000 : ℝ)^4431
        have hw : |(4568145259/10000000000 : ℝ)|=(4568145259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453530693/1250000000 : ℝ)|^5455 ≤ (28704036825503/100000000000000 : ℝ)^4431
        have hw : |(453530693/1250000000 : ℝ)|=(453530693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1729_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2537/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4239/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8481/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8481/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8481/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8481/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8481/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8481/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10143/100000 : ℝ) ^ (5447/1024 : ℝ) ≤ (516970011508669/100000000000000000000 : ℝ) := by
    have hpowers : (10143/100000 : ℝ)^5447 ≤ (516970011508669/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10143 : ℕ)^5447*100000000000000000000^1024 ≤ 516970011508669^1024*100000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10143 100000 516970011508669 100000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10143/100000 : ℝ)) (X := (516970011508669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8481/50000 : ℝ) ^ (5447/1024 : ℝ) ≤ (7967638630680469/100000000000000000000 : ℝ) := by
    have hpowers : (8481/50000 : ℝ)^5447 ≤ (7967638630680469/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8481 : ℕ)^5447*100000000000000000000^1024 ≤ 7967638630680469^1024*50000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8481 50000 7967638630680469 100000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8481/50000 : ℝ)) (X := (7967638630680469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000516970011508669/50000000000000000000 : ℝ) ≤ (10000019437307493/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50000516970011508669/50000000000000000000 : ℝ)^1024 ≤ (10000019437307493/10000000000000000 : ℝ)^5447 := by
      have hnat : (50000516970011508669 : ℕ)^1024*10000000000000000^5447 ≤ 10000019437307493^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000516970011508669 50000000000000000000 10000019437307493 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000019437307493/10000000000000000 : ℝ)) (X := (50000516970011508669/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004242304321094569/50000000000000000000 : ℝ) ≤ (125001993744257/125000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50004242304321094569/50000000000000000000 : ℝ)^1024 ≤ (125001993744257/125000000000000 : ℝ)^5447 := by
      have hnat : (50004242304321094569 : ℕ)^1024*125000000000000^5447 ≤ 125001993744257^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004242304321094569 50000000000000000000 125001993744257 125000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125001993744257/125000000000000 : ℝ)) (X := (50004242304321094569/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007967638630680469/50000000000000000000 : ℝ) ≤ (10000299561773627/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50007967638630680469/50000000000000000000 : ℝ)^1024 ≤ (10000299561773627/10000000000000000 : ℝ)^5447 := by
      have hnat : (50007967638630680469 : ℕ)^1024*10000000000000000^5447 ≤ 10000299561773627^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007967638630680469 50000000000000000000 10000299561773627 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000299561773627/10000000000000000 : ℝ)) (X := (50007967638630680469/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(516970011508669/100000000000000000000 : ℝ) ≤ ((4545819416035986507/4546000000000000000 : ℝ)+2*(140062233067/681900000000000 : ℝ)*(10143/100000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (4545819416035986507/4546000000000000000 : ℝ)+2*(140062233067/681900000000000 : ℝ)*(10143/100000 : ℝ)=(10000019437307493/10000000000000000 : ℝ) by norm_num, show 1+2*(516970011508669/100000000000000000000 : ℝ)=(50000516970011508669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7967638630680469/100000000000000000000 : ℝ)+(516970011508669/100000000000000000000 : ℝ) ≤ ((4545819416035986507/4546000000000000000 : ℝ)+(140062233067/681900000000000 : ℝ)*((8481/50000 : ℝ)+(10143/100000 : ℝ)))^(5447/1024 : ℝ) := by
    rw [show (4545819416035986507/4546000000000000000 : ℝ)+(140062233067/681900000000000 : ℝ)*((8481/50000 : ℝ)+(10143/100000 : ℝ))=(125001993744257/125000000000000 : ℝ) by norm_num, show 1+(7967638630680469/100000000000000000000 : ℝ)+(516970011508669/100000000000000000000 : ℝ)=(50004242304321094569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7967638630680469/100000000000000000000 : ℝ) ≤ ((4545819416035986507/4546000000000000000 : ℝ)+2*(140062233067/681900000000000 : ℝ)*(8481/50000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (4545819416035986507/4546000000000000000 : ℝ)+2*(140062233067/681900000000000 : ℝ)*(8481/50000 : ℝ)=(10000299561773627/10000000000000000 : ℝ) by norm_num, show 1+2*(7967638630680469/100000000000000000000 : ℝ)=(50007967638630680469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4545819416035986507/4546000000000000000 : ℝ)*(X 1 0+X 2 0)+(140062233067/681900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (10143/100000 : ℝ)) (hi := (8481/50000 : ℝ)) (c := (4545819416035986507/4546000000000000000 : ℝ)) (alpha := (140062233067/681900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4545819416035986507/4546000000000000000 : ℝ)*(X 0 1+X 2 1)+(140062233067/681900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (10143/100000 : ℝ)) (hi := (8481/50000 : ℝ)) (c := (4545819416035986507/4546000000000000000 : ℝ)) (alpha := (140062233067/681900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4545819416035986507/4546000000000000000 : ℝ)*(X 0 2+X 1 2)+(140062233067/681900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (10143/100000 : ℝ)) (hi := (8481/50000 : ℝ)) (c := (4545819416035986507/4546000000000000000 : ℝ)) (alpha := (140062233067/681900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-336570563/2500000000 : ℝ)*X 0 0+(341136021/625000000 : ℝ)*X 0 1+(5140275237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5337129367/10000000000 : ℝ)*X 1 0+(-755437127/5000000000 : ℝ)*X 1 1+(5140275237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5337129361/10000000000 : ℝ)*X 2 0+(5140275239/10000000000 : ℝ)*X 2 1+(-1510874259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1020262081/2500000000 : ℝ)*X 0 0+(3617256811/10000000000 : ℝ)*X 0 1+(4578972969/10000000000 : ℝ)*X 0 2+(1020262081/2500000000 : ℝ)*X 1 0+(3617256811/10000000000 : ℝ)*X 1 1+(4578972969/10000000000 : ℝ)*X 1 2+(1020262081/2500000000 : ℝ)*X 2 0+(3617256811/10000000000 : ℝ)*X 2 1+(4578972969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1346423147/10000000000 : ℝ)*X 0 0+(1285963601/2500000000 : ℝ)*X 0 1+(5454543943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050409519/2000000000 : ℝ)*X 1 0+(-598302777/5000000000 : ℝ)*X 1 1+(272727197/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626023797/5000000000 : ℝ)*X 2 0+(2727271971/5000000000 : ℝ)*X 2 1+(-1196605553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1020368641/2500000000 : ℝ)*X 0 0+(4568145259/10000000000 : ℝ)*X 0 1+(453530693/1250000000 : ℝ)*X 0 2+(1020368641/2500000000 : ℝ)*X 1 0+(4568145259/10000000000 : ℝ)*X 1 1+(453530693/1250000000 : ℝ)*X 1 2+(1020368641/2500000000 : ℝ)*X 2 0+(4568145259/10000000000 : ℝ)*X 2 1+(453530693/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (640065870245257168198929541/113650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40463277/5000000000000 : ℝ)*(base19) + (379246969/50000000000000 : ℝ)*(base23) + (25210071/100000000000000 : ℝ)*(lower2) + (27400847/20000000000000 : ℝ)*(upper3) + (99995651/100000000000000 : ℝ)*(upper5) + (2092731239927621/100000000000000 : ℝ)*(major0) + (2092731239927621/100000000000000 : ℝ)*(major1) + (2092731239927621/100000000000000 : ℝ)*(major2) + (629128157383029/20000000000000 : ℝ)*(sp0) + (3145648132344559/100000000000000 : ℝ)*(sp1) + (3145648183116161/100000000000000 : ℝ)*(sp2) + (32494075535789/3125000000000 : ℝ)*(sp3) + (4077347477/50000000000000 : ℝ)*(sp4) + (2933369761/100000000000000 : ℝ)*(sp7) + (1039813350515009/100000000000000 : ℝ)*(f.failure) + (1572824470805049/50000000000000 : ℝ)*(f.sum) + (149836809202303/34095000000000000000000000000 : ℝ)*base66 + (9686510083549430459/1363800000000000000000000000000000 : ℝ)*base68 + (2288087270245430459/1363800000000000000000000000000000 : ℝ)*base70 + (8127985109375769541/1363800000000000000000000000000000 : ℝ)*base71 + (3433463548567/532734375000000000000000000 : ℝ)*base74 + (7146294043290230459/1363800000000000000000000000000000 : ℝ)*base76 + (4071395415182630459/1363800000000000000000000000000000 : ℝ)*base78 + (2813710005132830459/1363800000000000000000000000000000 : ℝ)*base80 + (18021470782777/8523750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (27256251/5000000000000000000000 : ℝ)*base89 + (27256251/5000000000000000000000 : ℝ)*base91 + (27256251/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99066193411976813932187859/14206250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (467161829/50000000000000 : ℝ)*(base19) + (502149779/50000000000000 : ℝ)*(base23) + (137920091/50000000000000 : ℝ)*(lower1) + (147886949/100000000000000 : ℝ)*(upper3) + (61741/195312500000 : ℝ)*(lower4) + (36245711/25000000000000 : ℝ)*(upper5) + (267661142953029/12500000000000 : ℝ)*(major0) + (267661142953029/12500000000000 : ℝ)*(major1) + (267661142953029/12500000000000 : ℝ)*(major2) + (320993953/50000000000000 : ℝ)*(sp2) + (3218637785562069/100000000000000 : ℝ)*(sp4) + (804659212809603/25000000000000 : ℝ)*(sp5) + (643727227854921/20000000000000 : ℝ)*(sp6) + (132992533654867/12500000000000 : ℝ)*(sp7) + (132992533654867/12500000000000 : ℝ)*(f.failure) + (3218637785562069/100000000000000 : ℝ)*(f.sum) + (21063711931083/11365000000000000000000000000 : ℝ)*base65 + (960403094419100297/56825000000000000000000000000000 : ℝ)*base68 + (316393603859675297/56825000000000000000000000000000 : ℝ)*base70 + (827855187396900297/56825000000000000000000000000000 : ℝ)*base72 + (7415282949951/1420625000000000000000000000 : ℝ)*base73 + (4493540040911599703/56825000000000000000000000000000 : ℝ)*base75 + (37921730392100297/56825000000000000000000000000000 : ℝ)*base78 + (146978822945700297/56825000000000000000000000000000 : ℝ)*base80 + (64152140062377/11365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5763487/625000000000000000000 : ℝ)*base90 + (5763487/625000000000000000000 : ℝ)*base92 + (5763487/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1729_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2537/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4239/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1729_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1729_box_0 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-520849899/5000000000 : ℝ)*x 0 + (5407391501/10000000000 : ℝ)*x 1 + (2703695751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520849899/5000000000 : ℝ)^5455 ≤ (3088259623257/50000000000000 : ℝ)^4431 := by
    have hnat : (520849899 : ℕ)^5455*50000000000000^4431 ≤ 3088259623257^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520849899 5000000000 3088259623257 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407391501/10000000000 : ℝ)^5455 ≤ (23455870182491/50000000000000 : ℝ)^4431 := by
    have hnat : (5407391501 : ℕ)^5455*50000000000000^4431 ≤ 23455870182491^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407391501 10000000000 23455870182491 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703695751/5000000000 : ℝ)^5455 ≤ (46911740375663/100000000000000 : ℝ)^4431 := by
    have hnat : (2703695751 : ℕ)^5455*100000000000000^4431 ≤ 46911740375663^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703695751 5000000000 46911740375663 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-520849899/5000000000 : ℝ), (5407391501/10000000000 : ℝ), (2703695751/5000000000 : ℝ)] ![(3088259623257/50000000000000 : ℝ), (23455870182491/50000000000000 : ℝ), (46911740375663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-520849899/5000000000 : ℝ)|^5455 ≤ (3088259623257/50000000000000 : ℝ)^4431
        have hw : |(-520849899/5000000000 : ℝ)|=(520849899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407391501/10000000000 : ℝ)|^5455 ≤ (23455870182491/50000000000000 : ℝ)^4431
        have hw : |(5407391501/10000000000 : ℝ)|=(5407391501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703695751/5000000000 : ℝ)|^5455 ≤ (46911740375663/100000000000000 : ℝ)^4431
        have hw : |(2703695751/5000000000 : ℝ)|=(2703695751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_1 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612122787/5000000000 : ℝ)*x 0 + (-52062249/400000000 : ℝ)*x 1 + (337961969/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612122787/5000000000 : ℝ)^5455 ≤ (44963394888291/100000000000000 : ℝ)^4431 := by
    have hnat : (2612122787 : ℕ)^5455*100000000000000^4431 ≤ 44963394888291^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612122787 5000000000 44963394888291 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52062249/400000000 : ℝ)^5455 ≤ (8124864688609/100000000000000 : ℝ)^4431 := by
    have hnat : (52062249 : ℕ)^5455*100000000000000^4431 ≤ 8124864688609^4431*400000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52062249 400000000 8124864688609 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337961969/625000000 : ℝ)^5455 ≤ (46911740397023/100000000000000 : ℝ)^4431 := by
    have hnat : (337961969 : ℕ)^5455*100000000000000^4431 ≤ 46911740397023^4431*625000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337961969 625000000 46911740397023 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612122787/5000000000 : ℝ), (-52062249/400000000 : ℝ), (337961969/625000000 : ℝ)] ![(44963394888291/100000000000000 : ℝ), (8124864688609/100000000000000 : ℝ), (46911740397023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612122787/5000000000 : ℝ)|^5455 ≤ (44963394888291/100000000000000 : ℝ)^4431
        have hw : |(2612122787/5000000000 : ℝ)|=(2612122787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52062249/400000000 : ℝ)|^5455 ≤ (8124864688609/100000000000000 : ℝ)^4431
        have hw : |(-52062249/400000000 : ℝ)|=(52062249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337961969/625000000 : ℝ)|^5455 ≤ (46911740397023/100000000000000 : ℝ)^4431
        have hw : |(337961969/625000000 : ℝ)|=(337961969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_2 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224245551/10000000000 : ℝ)*x 0 + (5407391523/10000000000 : ℝ)*x 1 + (-162694529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224245551/10000000000 : ℝ)^5455 ≤ (44963394644591/100000000000000 : ℝ)^4431 := by
    have hnat : (5224245551 : ℕ)^5455*100000000000000^4431 ≤ 44963394644591^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224245551 10000000000 44963394644591 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407391523/10000000000 : ℝ)^5455 ≤ (46911740599951/100000000000000 : ℝ)^4431 := by
    have hnat : (5407391523 : ℕ)^5455*100000000000000^4431 ≤ 46911740599951^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407391523 10000000000 46911740599951 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162694529/1250000000 : ℝ)^5455 ≤ (1624972948481/20000000000000 : ℝ)^4431 := by
    have hnat : (162694529 : ℕ)^5455*20000000000000^4431 ≤ 1624972948481^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162694529 1250000000 1624972948481 20000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224245551/10000000000 : ℝ), (5407391523/10000000000 : ℝ), (-162694529/1250000000 : ℝ)] ![(44963394644591/100000000000000 : ℝ), (46911740599951/100000000000000 : ℝ), (1624972948481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224245551/10000000000 : ℝ)|^5455 ≤ (44963394644591/100000000000000 : ℝ)^4431
        have hw : |(5224245551/10000000000 : ℝ)|=(5224245551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407391523/10000000000 : ℝ)|^5455 ≤ (46911740599951/100000000000000 : ℝ)^4431
        have hw : |(5407391523/10000000000 : ℝ)|=(5407391523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-162694529/1250000000 : ℝ)|^5455 ≤ (1624972948481/20000000000000 : ℝ)^4431
        have hw : |(-162694529/1250000000 : ℝ)|=(162694529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_3 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (892219571/2000000000 : ℝ)*x 0 + (39118169/100000000 : ℝ)*x 1 + (977954219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892219571/2000000000 : ℝ)^5455 ≤ (37019288066421/100000000000000 : ℝ)^4431 := by
    have hnat : (892219571 : ℕ)^5455*100000000000000^4431 ≤ 37019288066421^4431*2000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892219571 2000000000 37019288066421 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39118169/100000000 : ℝ)^5455 ≤ (15745178038239/50000000000000 : ℝ)^4431 := by
    have hnat : (39118169 : ℕ)^5455*50000000000000^4431 ≤ 15745178038239^4431*100000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39118169 100000000 15745178038239 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977954219/2500000000 : ℝ)^5455 ≤ (7872588959657/25000000000000 : ℝ)^4431 := by
    have hnat : (977954219 : ℕ)^5455*25000000000000^4431 ≤ 7872588959657^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977954219 2500000000 7872588959657 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(892219571/2000000000 : ℝ), (39118169/100000000 : ℝ), (977954219/2500000000 : ℝ)] ![(37019288066421/100000000000000 : ℝ), (15745178038239/50000000000000 : ℝ), (7872588959657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(892219571/2000000000 : ℝ)|^5455 ≤ (37019288066421/100000000000000 : ℝ)^4431
        have hw : |(892219571/2000000000 : ℝ)|=(892219571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39118169/100000000 : ℝ)|^5455 ≤ (15745178038239/50000000000000 : ℝ)^4431
        have hw : |(39118169/100000000 : ℝ)|=(39118169/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(977954219/2500000000 : ℝ)|^5455 ≤ (7872588959657/25000000000000 : ℝ)^4431
        have hw : |(977954219/2500000000 : ℝ)|=(977954219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_4 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1671193571/10000000000 : ℝ)*x 0 + (517797629/1000000000 : ℝ)*x 1 + (1294494029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1671193571/10000000000 : ℝ)^5455 ≤ (11052714666949/100000000000000 : ℝ)^4431 := by
    have hnat : (1671193571 : ℕ)^5455*100000000000000^4431 ≤ 11052714666949^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671193571 10000000000 11052714666949 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517797629/1000000000 : ℝ)^5455 ≤ (44473643580129/100000000000000 : ℝ)^4431 := by
    have hnat : (517797629 : ℕ)^5455*100000000000000^4431 ≤ 44473643580129^4431*1000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517797629 1000000000 44473643580129 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294494029/2500000000 : ℝ)^5455 ≤ (44473641740269/100000000000000 : ℝ)^4431 := by
    have hnat : (1294494029 : ℕ)^5455*100000000000000^4431 ≤ 44473641740269^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294494029 2500000000 44473641740269 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1671193571/10000000000 : ℝ), (517797629/1000000000 : ℝ), (1294494029/2500000000 : ℝ)] ![(11052714666949/100000000000000 : ℝ), (44473643580129/100000000000000 : ℝ), (44473641740269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1671193571/10000000000 : ℝ)|^5455 ≤ (11052714666949/100000000000000 : ℝ)^4431
        have hw : |(-1671193571/10000000000 : ℝ)|=(1671193571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517797629/1000000000 : ℝ)|^5455 ≤ (44473643580129/100000000000000 : ℝ)^4431
        have hw : |(517797629/1000000000 : ℝ)|=(517797629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294494029/2500000000 : ℝ)|^5455 ≤ (44473641740269/100000000000000 : ℝ)^4431
        have hw : |(1294494029/2500000000 : ℝ)|=(1294494029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_5 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672392219/1250000000 : ℝ)*x 0 + (-1403618837/10000000000 : ℝ)*x 1 + (1294494201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672392219/1250000000 : ℝ)^5455 ≤ (23305081000039/50000000000000 : ℝ)^4431 := by
    have hnat : (672392219 : ℕ)^5455*50000000000000^4431 ≤ 23305081000039^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672392219 1250000000 23305081000039 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403618837/10000000000 : ℝ)^5455 ≤ (8916188969517/100000000000000 : ℝ)^4431 := by
    have hnat : (1403618837 : ℕ)^5455*100000000000000^4431 ≤ 8916188969517^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403618837 10000000000 8916188969517 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294494201/2500000000 : ℝ)^5455 ≤ (44473649015119/100000000000000 : ℝ)^4431 := by
    have hnat : (1294494201 : ℕ)^5455*100000000000000^4431 ≤ 44473649015119^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294494201 2500000000 44473649015119 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672392219/1250000000 : ℝ), (-1403618837/10000000000 : ℝ), (1294494201/2500000000 : ℝ)] ![(23305081000039/50000000000000 : ℝ), (8916188969517/100000000000000 : ℝ), (44473649015119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672392219/1250000000 : ℝ)|^5455 ≤ (23305081000039/50000000000000 : ℝ)^4431
        have hw : |(672392219/1250000000 : ℝ)|=(672392219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1403618837/10000000000 : ℝ)|^5455 ≤ (8916188969517/100000000000000 : ℝ)^4431
        have hw : |(-1403618837/10000000000 : ℝ)|=(1403618837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294494201/2500000000 : ℝ)|^5455 ≤ (44473649015119/100000000000000 : ℝ)^4431
        have hw : |(1294494201/2500000000 : ℝ)|=(1294494201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_6 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672392243/1250000000 : ℝ)*x 0 + (2588988347/5000000000 : ℝ)*x 1 + (-350904681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672392243/1250000000 : ℝ)^5455 ≤ (4661016404823/10000000000000 : ℝ)^4431 := by
    have hnat : (672392243 : ℕ)^5455*10000000000000^4431 ≤ 4661016404823^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672392243 1250000000 4661016404823 10000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588988347/5000000000 : ℝ)^5455 ≤ (44473647851989/100000000000000 : ℝ)^4431 := by
    have hnat : (2588988347 : ℕ)^5455*100000000000000^4431 ≤ 44473647851989^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588988347 5000000000 44473647851989 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (350904681/2500000000 : ℝ)^5455 ≤ (139315438841/1562500000000 : ℝ)^4431 := by
    have hnat : (350904681 : ℕ)^5455*1562500000000^4431 ≤ 139315438841^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350904681 2500000000 139315438841 1562500000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672392243/1250000000 : ℝ), (2588988347/5000000000 : ℝ), (-350904681/2500000000 : ℝ)] ![(4661016404823/10000000000000 : ℝ), (44473647851989/100000000000000 : ℝ), (139315438841/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672392243/1250000000 : ℝ)|^5455 ≤ (4661016404823/10000000000000 : ℝ)^4431
        have hw : |(672392243/1250000000 : ℝ)|=(672392243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588988347/5000000000 : ℝ)|^5455 ≤ (44473647851989/100000000000000 : ℝ)^4431
        have hw : |(2588988347/5000000000 : ℝ)|=(2588988347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-350904681/2500000000 : ℝ)|^5455 ≤ (139315438841/1562500000000 : ℝ)^4431
        have hw : |(-350904681/2500000000 : ℝ)|=(350904681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_7 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3684385951/10000000000 : ℝ)*x 0 + (4299373399/10000000000 : ℝ)*x 1 + (171974937/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3684385951/10000000000 : ℝ)^5455 ≤ (29251793408141/100000000000000 : ℝ)^4431 := by
    have hnat : (3684385951 : ℕ)^5455*100000000000000^4431 ≤ 29251793408141^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3684385951 10000000000 29251793408141 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4299373399/10000000000 : ℝ)^5455 ≤ (1768705157713/5000000000000 : ℝ)^4431 := by
    have hnat : (4299373399 : ℕ)^5455*5000000000000^4431 ≤ 1768705157713^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299373399 10000000000 1768705157713 5000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171974937/400000000 : ℝ)^5455 ≤ (17687051708809/50000000000000 : ℝ)^4431 := by
    have hnat : (171974937 : ℕ)^5455*50000000000000^4431 ≤ 17687051708809^4431*400000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171974937 400000000 17687051708809 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3684385951/10000000000 : ℝ), (4299373399/10000000000 : ℝ), (171974937/400000000 : ℝ)] ![(29251793408141/100000000000000 : ℝ), (1768705157713/5000000000000 : ℝ), (17687051708809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3684385951/10000000000 : ℝ)|^5455 ≤ (29251793408141/100000000000000 : ℝ)^4431
        have hw : |(3684385951/10000000000 : ℝ)|=(3684385951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4299373399/10000000000 : ℝ)|^5455 ≤ (1768705157713/5000000000000 : ℝ)^4431
        have hw : |(4299373399/10000000000 : ℝ)|=(4299373399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171974937/400000000 : ℝ)|^5455 ≤ (17687051708809/50000000000000 : ℝ)^4431
        have hw : |(171974937/400000000 : ℝ)|=(171974937/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_8 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1535572971/10000000000 : ℝ)*x 0 + (5007751341/10000000000 : ℝ)*x 1 + (5449356609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1535572971/10000000000 : ℝ)^5455 ≤ (4979529613487/50000000000000 : ℝ)^4431 := by
    have hnat : (1535572971 : ℕ)^5455*50000000000000^4431 ≤ 4979529613487^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535572971 10000000000 4979529613487 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5007751341/10000000000 : ℝ)^5455 ≤ (42680595938161/100000000000000 : ℝ)^4431 := by
    have hnat : (5007751341 : ℕ)^5455*100000000000000^4431 ≤ 42680595938161^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007751341 10000000000 42680595938161 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449356609/10000000000 : ℝ)^5455 ≤ (1184008620607/2500000000000 : ℝ)^4431 := by
    have hnat : (5449356609 : ℕ)^5455*2500000000000^4431 ≤ 1184008620607^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449356609 10000000000 1184008620607 2500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1535572971/10000000000 : ℝ), (5007751341/10000000000 : ℝ), (5449356609/10000000000 : ℝ)] ![(4979529613487/50000000000000 : ℝ), (42680595938161/100000000000000 : ℝ), (1184008620607/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1535572971/10000000000 : ℝ)|^5455 ≤ (4979529613487/50000000000000 : ℝ)^4431
        have hw : |(-1535572971/10000000000 : ℝ)|=(1535572971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5007751341/10000000000 : ℝ)|^5455 ≤ (42680595938161/100000000000000 : ℝ)^4431
        have hw : |(5007751341/10000000000 : ℝ)|=(5007751341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449356609/10000000000 : ℝ)|^5455 ≤ (1184008620607/2500000000000 : ℝ)^4431
        have hw : |(5449356609/10000000000 : ℝ)|=(5449356609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_9 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103918757/200000000 : ℝ)*x 0 + (-1282154081/10000000000 : ℝ)*x 1 + (217974247/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103918757/200000000 : ℝ)^5455 ≤ (11165910894681/25000000000000 : ℝ)^4431 := by
    have hnat : (103918757 : ℕ)^5455*25000000000000^4431 ≤ 11165910894681^4431*200000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103918757 200000000 11165910894681 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282154081/10000000000 : ℝ)^5455 ≤ (7976016230667/100000000000000 : ℝ)^4431 := by
    have hnat : (1282154081 : ℕ)^5455*100000000000000^4431 ≤ 7976016230667^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282154081 10000000000 7976016230667 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217974247/400000000 : ℝ)^5455 ≤ (23680170090353/50000000000000 : ℝ)^4431 := by
    have hnat : (217974247 : ℕ)^5455*50000000000000^4431 ≤ 23680170090353^4431*400000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217974247 400000000 23680170090353 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103918757/200000000 : ℝ), (-1282154081/10000000000 : ℝ), (217974247/400000000 : ℝ)] ![(11165910894681/25000000000000 : ℝ), (7976016230667/100000000000000 : ℝ), (23680170090353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103918757/200000000 : ℝ)|^5455 ≤ (11165910894681/25000000000000 : ℝ)^4431
        have hw : |(103918757/200000000 : ℝ)|=(103918757/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1282154081/10000000000 : ℝ)|^5455 ≤ (7976016230667/100000000000000 : ℝ)^4431
        have hw : |(-1282154081/10000000000 : ℝ)|=(1282154081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217974247/400000000 : ℝ)|^5455 ≤ (23680170090353/50000000000000 : ℝ)^4431
        have hw : |(217974247/400000000 : ℝ)|=(217974247/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_10 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519593779/1000000000 : ℝ)*x 0 + (544935647/1000000000 : ℝ)*x 1 + (-1282153751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519593779/1000000000 : ℝ)^5455 ≤ (44663642943781/100000000000000 : ℝ)^4431 := by
    have hnat : (519593779 : ℕ)^5455*100000000000000^4431 ≤ 44663642943781^4431*1000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519593779 1000000000 44663642943781 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544935647/1000000000 : ℝ)^5455 ≤ (11840085834263/25000000000000 : ℝ)^4431 := by
    have hnat : (544935647 : ℕ)^5455*25000000000000^4431 ≤ 11840085834263^4431*1000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544935647 1000000000 11840085834263 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282153751/10000000000 : ℝ)^5455 ≤ (797601370339/10000000000000 : ℝ)^4431 := by
    have hnat : (1282153751 : ℕ)^5455*10000000000000^4431 ≤ 797601370339^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282153751 10000000000 797601370339 10000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519593779/1000000000 : ℝ), (544935647/1000000000 : ℝ), (-1282153751/10000000000 : ℝ)] ![(44663642943781/100000000000000 : ℝ), (11840085834263/25000000000000 : ℝ), (797601370339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519593779/1000000000 : ℝ)|^5455 ≤ (44663642943781/100000000000000 : ℝ)^4431
        have hw : |(519593779/1000000000 : ℝ)|=(519593779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544935647/1000000000 : ℝ)|^5455 ≤ (11840085834263/25000000000000 : ℝ)^4431
        have hw : |(544935647/1000000000 : ℝ)|=(544935647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1282153751/10000000000 : ℝ)|^5455 ≤ (797601370339/10000000000000 : ℝ)^4431
        have hw : |(-1282153751/10000000000 : ℝ)|=(1282153751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_11 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (143694679/312500000 : ℝ)*x 0 + (960184489/2500000000 : ℝ)*x 1 + (1920369017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (143694679/312500000 : ℝ)^5455 ≤ (38425159573031/100000000000000 : ℝ)^4431 := by
    have hnat : (143694679 : ℕ)^5455*100000000000000^4431 ≤ 38425159573031^4431*312500000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143694679 312500000 38425159573031 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960184489/2500000000 : ℝ)^5455 ≤ (30787419820511/100000000000000 : ℝ)^4431 := by
    have hnat : (960184489 : ℕ)^5455*100000000000000^4431 ≤ 30787419820511^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960184489 2500000000 30787419820511 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920369017/5000000000 : ℝ)^5455 ≤ (6157484118051/20000000000000 : ℝ)^4431 := by
    have hnat : (1920369017 : ℕ)^5455*20000000000000^4431 ≤ 6157484118051^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920369017 5000000000 6157484118051 20000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(143694679/312500000 : ℝ), (960184489/2500000000 : ℝ), (1920369017/5000000000 : ℝ)] ![(38425159573031/100000000000000 : ℝ), (30787419820511/100000000000000 : ℝ), (6157484118051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(143694679/312500000 : ℝ)|^5455 ≤ (38425159573031/100000000000000 : ℝ)^4431
        have hw : |(143694679/312500000 : ℝ)|=(143694679/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(960184489/2500000000 : ℝ)|^5455 ≤ (30787419820511/100000000000000 : ℝ)^4431
        have hw : |(960184489/2500000000 : ℝ)|=(960184489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1920369017/5000000000 : ℝ)|^5455 ≤ (6157484118051/20000000000000 : ℝ)^4431
        have hw : |(1920369017/5000000000 : ℝ)|=(1920369017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_12 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1171367051/10000000000 : ℝ)*x 0 + (5569889437/10000000000 : ℝ)*x 1 + (5153077217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1171367051/10000000000 : ℝ)^5455 ≤ (3568114833833/50000000000000 : ℝ)^4431 := by
    have hnat : (1171367051 : ℕ)^5455*50000000000000^4431 ≤ 3568114833833^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171367051 10000000000 3568114833833 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5569889437/10000000000 : ℝ)^5455 ≤ (1216331521309/2500000000000 : ℝ)^4431 := by
    have hnat : (5569889437 : ℕ)^5455*2500000000000^4431 ≤ 1216331521309^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569889437 10000000000 1216331521309 2500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153077217/10000000000 : ℝ)^5455 ≤ (44210509462563/100000000000000 : ℝ)^4431 := by
    have hnat : (5153077217 : ℕ)^5455*100000000000000^4431 ≤ 44210509462563^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153077217 10000000000 44210509462563 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1171367051/10000000000 : ℝ), (5569889437/10000000000 : ℝ), (5153077217/10000000000 : ℝ)] ![(3568114833833/50000000000000 : ℝ), (1216331521309/2500000000000 : ℝ), (44210509462563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1171367051/10000000000 : ℝ)|^5455 ≤ (3568114833833/50000000000000 : ℝ)^4431
        have hw : |(-1171367051/10000000000 : ℝ)|=(1171367051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5569889437/10000000000 : ℝ)|^5455 ≤ (1216331521309/2500000000000 : ℝ)^4431
        have hw : |(5569889437/10000000000 : ℝ)|=(5569889437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153077217/10000000000 : ℝ)|^5455 ≤ (44210509462563/100000000000000 : ℝ)^4431
        have hw : |(5153077217/10000000000 : ℝ)|=(5153077217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_13 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348995589/2500000000 : ℝ)*x 0 + (-1414272047/10000000000 : ℝ)*x 1 + (2576538671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348995589/2500000000 : ℝ)^5455 ≤ (5848739509537/12500000000000 : ℝ)^4431 := by
    have hnat : (1348995589 : ℕ)^5455*12500000000000^4431 ≤ 5848739509537^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348995589 2500000000 5848739509537 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1414272047/10000000000 : ℝ)^5455 ≤ (2249893281551/25000000000000 : ℝ)^4431 := by
    have hnat : (1414272047 : ℕ)^5455*25000000000000^4431 ≤ 2249893281551^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414272047 10000000000 2249893281551 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576538671/5000000000 : ℝ)^5455 ≤ (4421051078283/10000000000000 : ℝ)^4431 := by
    have hnat : (2576538671 : ℕ)^5455*10000000000000^4431 ≤ 4421051078283^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576538671 5000000000 4421051078283 10000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348995589/2500000000 : ℝ), (-1414272047/10000000000 : ℝ), (2576538671/5000000000 : ℝ)] ![(5848739509537/12500000000000 : ℝ), (2249893281551/25000000000000 : ℝ), (4421051078283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348995589/2500000000 : ℝ)|^5455 ≤ (5848739509537/12500000000000 : ℝ)^4431
        have hw : |(1348995589/2500000000 : ℝ)|=(1348995589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1414272047/10000000000 : ℝ)|^5455 ≤ (2249893281551/25000000000000 : ℝ)^4431
        have hw : |(-1414272047/10000000000 : ℝ)|=(1414272047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576538671/5000000000 : ℝ)|^5455 ≤ (4421051078283/10000000000000 : ℝ)^4431
        have hw : |(2576538671/5000000000 : ℝ)|=(2576538671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_14 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42156113/78125000 : ℝ)*x 0 + (5153077453/10000000000 : ℝ)*x 1 + (-1414271751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42156113/78125000 : ℝ)^5455 ≤ (23394958614607/50000000000000 : ℝ)^4431 := by
    have hnat : (42156113 : ℕ)^5455*50000000000000^4431 ≤ 23394958614607^4431*78125000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42156113 78125000 23394958614607 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153077453/10000000000 : ℝ)^5455 ≤ (11052627988807/25000000000000 : ℝ)^4431 := by
    have hnat : (5153077453 : ℕ)^5455*25000000000000^4431 ≤ 11052627988807^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153077453 10000000000 11052627988807 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414271751/10000000000 : ℝ)^5455 ≤ (8999570807349/100000000000000 : ℝ)^4431 := by
    have hnat : (1414271751 : ℕ)^5455*100000000000000^4431 ≤ 8999570807349^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414271751 10000000000 8999570807349 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42156113/78125000 : ℝ), (5153077453/10000000000 : ℝ), (-1414271751/10000000000 : ℝ)] ![(23394958614607/50000000000000 : ℝ), (11052627988807/25000000000000 : ℝ), (8999570807349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42156113/78125000 : ℝ)|^5455 ≤ (23394958614607/50000000000000 : ℝ)^4431
        have hw : |(42156113/78125000 : ℝ)|=(42156113/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153077453/10000000000 : ℝ)|^5455 ≤ (11052627988807/25000000000000 : ℝ)^4431
        have hw : |(5153077453/10000000000 : ℝ)|=(5153077453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1414271751/10000000000 : ℝ)|^5455 ≤ (8999570807349/100000000000000 : ℝ)^4431
        have hw : |(-1414271751/10000000000 : ℝ)|=(1414271751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_box_15 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3597106439/10000000000 : ℝ)*x 0 + (542665049/1250000000 : ℝ)*x 1 + (4341320949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3597106439/10000000000 : ℝ)^5455 ≤ (14200528543663/50000000000000 : ℝ)^4431 := by
    have hnat : (3597106439 : ℕ)^5455*50000000000000^4431 ≤ 14200528543663^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3597106439 10000000000 14200528543663 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542665049/1250000000 : ℝ)^5455 ≤ (7159893723547/20000000000000 : ℝ)^4431 := by
    have hnat : (542665049 : ℕ)^5455*20000000000000^4431 ≤ 7159893723547^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542665049 1250000000 7159893723547 20000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4341320949/10000000000 : ℝ)^5455 ≤ (35799474272349/100000000000000 : ℝ)^4431 := by
    have hnat : (4341320949 : ℕ)^5455*100000000000000^4431 ≤ 35799474272349^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341320949 10000000000 35799474272349 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3597106439/10000000000 : ℝ), (542665049/1250000000 : ℝ), (4341320949/10000000000 : ℝ)] ![(14200528543663/50000000000000 : ℝ), (7159893723547/20000000000000 : ℝ), (35799474272349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3597106439/10000000000 : ℝ)|^5455 ≤ (14200528543663/50000000000000 : ℝ)^4431
        have hw : |(3597106439/10000000000 : ℝ)|=(3597106439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542665049/1250000000 : ℝ)|^5455 ≤ (7159893723547/20000000000000 : ℝ)^4431
        have hw : |(542665049/1250000000 : ℝ)|=(542665049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4341320949/10000000000 : ℝ)|^5455 ≤ (35799474272349/100000000000000 : ℝ)^4431
        have hw : |(4341320949/10000000000 : ℝ)|=(4341320949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1729_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4239/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2537/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66933/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11769/20000 : ℝ) ∧ (20519/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90687/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4239/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2537/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4239/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2537/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4239/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2537/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4239/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2537/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4239/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2537/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4239/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2537/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2537/25000 : ℝ) ^ (5447/1024 : ℝ) ≤ (518327039197143/100000000000000000000 : ℝ) := by
    have hpowers : (2537/25000 : ℝ)^5447 ≤ (518327039197143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2537 : ℕ)^5447*100000000000000000000^1024 ≤ 518327039197143^1024*25000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2537 25000 518327039197143 100000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2537/25000 : ℝ)) (X := (518327039197143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4239/25000 : ℝ) ^ (5447/1024 : ℝ) ≤ (7952658021798803/100000000000000000000 : ℝ) := by
    have hpowers : (4239/25000 : ℝ)^5447 ≤ (7952658021798803/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4239 : ℕ)^5447*100000000000000000000^1024 ≤ 7952658021798803^1024*25000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4239 25000 7952658021798803 100000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4239/25000 : ℝ)) (X := (7952658021798803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000518327039197143/50000000000000000000 : ℝ) ≤ (1250002436041189/1250000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50000518327039197143/50000000000000000000 : ℝ)^1024 ≤ (1250002436041189/1250000000000000 : ℝ)^5447 := by
      have hnat : (50000518327039197143 : ℕ)^1024*1250000000000000^5447 ≤ 1250002436041189^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000518327039197143 50000000000000000000 1250002436041189 1250000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002436041189/1250000000000000 : ℝ)) (X := (50000518327039197143/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004235492530497973/50000000000000000000 : ℝ) ≤ (10000159243443867/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50004235492530497973/50000000000000000000 : ℝ)^1024 ≤ (10000159243443867/10000000000000000 : ℝ)^5447 := by
      have hnat : (50004235492530497973 : ℕ)^1024*10000000000000000^5447 ≤ 10000159243443867^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004235492530497973 50000000000000000000 10000159243443867 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000159243443867/10000000000000000 : ℝ)) (X := (50004235492530497973/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007952658021798803/50000000000000000000 : ℝ) ≤ (5000149499279111/5000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50007952658021798803/50000000000000000000 : ℝ)^1024 ≤ (5000149499279111/5000000000000000 : ℝ)^5447 := by
      have hnat : (50007952658021798803 : ℕ)^1024*5000000000000000^5447 ≤ 5000149499279111^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007952658021798803 50000000000000000000 5000149499279111 5000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000149499279111/5000000000000000 : ℝ)) (X := (50007952658021798803/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(518327039197143/100000000000000000000 : ℝ) ≤ ((8509662025843296077/8510000000000000000 : ℝ)+2*(27951022871/136160000000000 : ℝ)*(2537/25000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (8509662025843296077/8510000000000000000 : ℝ)+2*(27951022871/136160000000000 : ℝ)*(2537/25000 : ℝ)=(1250002436041189/1250000000000000 : ℝ) by norm_num, show 1+2*(518327039197143/100000000000000000000 : ℝ)=(50000518327039197143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7952658021798803/100000000000000000000 : ℝ)+(518327039197143/100000000000000000000 : ℝ) ≤ ((8509662025843296077/8510000000000000000 : ℝ)+(27951022871/136160000000000 : ℝ)*((4239/25000 : ℝ)+(2537/25000 : ℝ)))^(5447/1024 : ℝ) := by
    rw [show (8509662025843296077/8510000000000000000 : ℝ)+(27951022871/136160000000000 : ℝ)*((4239/25000 : ℝ)+(2537/25000 : ℝ))=(10000159243443867/10000000000000000 : ℝ) by norm_num, show 1+(7952658021798803/100000000000000000000 : ℝ)+(518327039197143/100000000000000000000 : ℝ)=(50004235492530497973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7952658021798803/100000000000000000000 : ℝ) ≤ ((8509662025843296077/8510000000000000000 : ℝ)+2*(27951022871/136160000000000 : ℝ)*(4239/25000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (8509662025843296077/8510000000000000000 : ℝ)+2*(27951022871/136160000000000 : ℝ)*(4239/25000 : ℝ)=(5000149499279111/5000000000000000 : ℝ) by norm_num, show 1+2*(7952658021798803/100000000000000000000 : ℝ)=(50007952658021798803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8509662025843296077/8510000000000000000 : ℝ)*(X 1 0+X 2 0)+(27951022871/136160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (2537/25000 : ℝ)) (hi := (4239/25000 : ℝ)) (c := (8509662025843296077/8510000000000000000 : ℝ)) (alpha := (27951022871/136160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8509662025843296077/8510000000000000000 : ℝ)*(X 0 1+X 2 1)+(27951022871/136160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (2537/25000 : ℝ)) (hi := (4239/25000 : ℝ)) (c := (8509662025843296077/8510000000000000000 : ℝ)) (alpha := (27951022871/136160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8509662025843296077/8510000000000000000 : ℝ)*(X 0 2+X 1 2)+(27951022871/136160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (2537/25000 : ℝ)) (hi := (4239/25000 : ℝ)) (c := (8509662025843296077/8510000000000000000 : ℝ)) (alpha := (27951022871/136160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-520849899/5000000000 : ℝ)*X 0 0+(5407391501/10000000000 : ℝ)*X 0 1+(2703695751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612122787/5000000000 : ℝ)*X 1 0+(-52062249/400000000 : ℝ)*X 1 1+(337961969/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224245551/10000000000 : ℝ)*X 2 0+(5407391523/10000000000 : ℝ)*X 2 1+(-162694529/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((892219571/2000000000 : ℝ)*X 0 0+(39118169/100000000 : ℝ)*X 0 1+(977954219/2500000000 : ℝ)*X 0 2+(892219571/2000000000 : ℝ)*X 1 0+(39118169/100000000 : ℝ)*X 1 1+(977954219/2500000000 : ℝ)*X 1 2+(892219571/2000000000 : ℝ)*X 2 0+(39118169/100000000 : ℝ)*X 2 1+(977954219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1671193571/10000000000 : ℝ)*X 0 0+(517797629/1000000000 : ℝ)*X 0 1+(1294494029/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((672392219/1250000000 : ℝ)*X 1 0+(-1403618837/10000000000 : ℝ)*X 1 1+(1294494201/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672392243/1250000000 : ℝ)*X 2 0+(2588988347/5000000000 : ℝ)*X 2 1+(-350904681/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3684385951/10000000000 : ℝ)*X 0 0+(4299373399/10000000000 : ℝ)*X 0 1+(171974937/400000000 : ℝ)*X 0 2+(3684385951/10000000000 : ℝ)*X 1 0+(4299373399/10000000000 : ℝ)*X 1 1+(171974937/400000000 : ℝ)*X 1 2+(3684385951/10000000000 : ℝ)*X 2 0+(4299373399/10000000000 : ℝ)*X 2 1+(171974937/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1535572971/10000000000 : ℝ)*X 0 0+(5007751341/10000000000 : ℝ)*X 0 1+(5449356609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((103918757/200000000 : ℝ)*X 1 0+(-1282154081/10000000000 : ℝ)*X 1 1+(217974247/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((519593779/1000000000 : ℝ)*X 2 0+(544935647/1000000000 : ℝ)*X 2 1+(-1282153751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((143694679/312500000 : ℝ)*X 0 0+(960184489/2500000000 : ℝ)*X 0 1+(1920369017/5000000000 : ℝ)*X 0 2+(143694679/312500000 : ℝ)*X 1 0+(960184489/2500000000 : ℝ)*X 1 1+(1920369017/5000000000 : ℝ)*X 1 2+(143694679/312500000 : ℝ)*X 2 0+(960184489/2500000000 : ℝ)*X 2 1+(1920369017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1171367051/10000000000 : ℝ)*X 0 0+(5569889437/10000000000 : ℝ)*X 0 1+(5153077217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1348995589/2500000000 : ℝ)*X 1 0+(-1414272047/10000000000 : ℝ)*X 1 1+(2576538671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((42156113/78125000 : ℝ)*X 2 0+(5153077453/10000000000 : ℝ)*X 2 1+(-1414271751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3597106439/10000000000 : ℝ)*X 0 0+(542665049/1250000000 : ℝ)*X 0 1+(4341320949/10000000000 : ℝ)*X 0 2+(3597106439/10000000000 : ℝ)*X 1 0+(542665049/1250000000 : ℝ)*X 1 1+(4341320949/10000000000 : ℝ)*X 1 2+(3597106439/10000000000 : ℝ)*X 2 0+(542665049/1250000000 : ℝ)*X 2 1+(4341320949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66933/100000 : ℝ) ≤ (-2278320412842412791682938747/3404000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4197/781250000000 : ℝ)*(upper3) + (31115151/100000000000000 : ℝ)*(upper4) + (32686421/100000000000000 : ℝ)*(upper5) + (702229322070599/50000000000000 : ℝ)*(major0) + (702229322070599/50000000000000 : ℝ)*(major1) + (702229322070599/50000000000000 : ℝ)*(major2) + (15044499/100000000000000 : ℝ)*(sp3) + (533348433686553/25000000000000 : ℝ)*(sp4) + (2133356068797477/100000000000000 : ℝ)*(sp5) + (2133361913850259/100000000000000 : ℝ)*(sp6) + (697831995373969/100000000000000 : ℝ)*(sp7) + (221303397/12500000000000 : ℝ)*(sp8) + (39436375911/100000000000000 : ℝ)*(sp13) + (33591323129/100000000000000 : ℝ)*(sp14) + (174458002604617/25000000000000 : ℝ)*(f.failure) + (533348876293347/25000000000000 : ℝ)*(f.sum) + (1877957550093/680800000000000000000000000 : ℝ)*base65 + (123382981576697377/425500000000000000000000000000000 : ℝ)*base68 + (1080280993024302623/425500000000000000000000000000000 : ℝ)*base69 + (2566118713219802623/425500000000000000000000000000000 : ℝ)*base71 + (1014379789931/3404000000000000000000000000 : ℝ)*base74 + (750285233572697377/425500000000000000000000000000000 : ℝ)*base76 + (76833367453802623/425500000000000000000000000000000 : ℝ)*base77 + (10633007395197377/425500000000000000000000000000000 : ℝ)*base80 + (14088790743913/3404000000000000000000000000 : ℝ)*base81 + (4248237/1250000000000000000000 : ℝ)*base90 + (4248237/1250000000000000000000 : ℝ)*base92 + (4248237/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11769/20000 : ℝ) ≤ (31299416830661843293078587041439/53187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85383/2500000000000 : ℝ)*(lower0) + (1944919/50000000000000 : ℝ)*(upper2) + (11511/10000000000000 : ℝ)*(upper3) + (713997/100000000000000 : ℝ)*(lower5) + (189349766651431/12500000000000 : ℝ)*(major0) + (189349766651431/12500000000000 : ℝ)*(major1) + (189349766651431/12500000000000 : ℝ)*(major2) + (2257324208213211/100000000000000 : ℝ)*(sp0) + (1128662096775877/50000000000000 : ℝ)*(sp1) + (22573241094929/1000000000000 : ℝ)*(sp2) + (376328122089551/50000000000000 : ℝ)*(sp3) + (916341/6250000000000 : ℝ)*(sp5) + (9872031/10000000000000 : ℝ)*(sp6) + (41633763/100000000000000 : ℝ)*(sp7) + (376328142906433/50000000000000 : ℝ)*(f.failure) + (2257324208213211/100000000000000 : ℝ)*(f.sum) + (1626111670853/425500000000000000000000000 : ℝ)*base65 + (455546749129701313/106375000000000000000000000000000 : ℝ)*base68 + (393295312061076313/106375000000000000000000000000000 : ℝ)*base70 + (1104931995228673687/106375000000000000000000000000000 : ℝ)*base71 + (344715784783/106375000000000000000000000 : ℝ)*base74 + (725851413936673687/106375000000000000000000000000000 : ℝ)*base75 + (741958493474673687/106375000000000000000000000000000 : ℝ)*base77 + (168255171897923687/106375000000000000000000000000000 : ℝ)*base79 + (69221285867/106375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16784187/2500000000000000000000 : ℝ)*base89 + (16784187/2500000000000000000000 : ℝ)*base91 + (16784187/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (20519/25000 : ℝ) ≤ (60738335746462505842977081/74000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7106893/100000000000000 : ℝ)*(upper1) + (83477253/100000000000000 : ℝ)*(lower3) + (30093857/100000000000000 : ℝ)*(upper4) + (25673093/100000000000000 : ℝ)*(lower5) + (381175802397607/25000000000000 : ℝ)*(major0) + (381175802397607/25000000000000 : ℝ)*(major1) + (381175802397607/25000000000000 : ℝ)*(major2) + (1833382179/100000000000000 : ℝ)*(sp0) + (3857658511/25000000000000 : ℝ)*(sp2) + (2887418323/50000000000000 : ℝ)*(sp3) + (2211393714407/97656250000 : ℝ)*(sp8) + (566117249233737/25000000000000 : ℝ)*(sp9) + (283056695787613/12500000000000 : ℝ)*(sp10) + (15151440734253/2000000000000 : ℝ)*(sp11) + (47348613221831/6250000000000 : ℝ)*(f.failure) + (566117249233737/25000000000000 : ℝ)*(f.sum) + (615297491401/74000000000000000000000000 : ℝ)*base66 + (29573894987134793/9250000000000000000000000000000 : ℝ)*base67 + (61500536396384793/9250000000000000000000000000000 : ℝ)*base69 + (111833185670615207/9250000000000000000000000000000 : ℝ)*base72 + (114548372751/74000000000000000000000000 : ℝ)*base73 + (60638276093884793/9250000000000000000000000000000 : ℝ)*base75 + (26547432757615207/9250000000000000000000000000000 : ℝ)*base78 + (27168706769115207/9250000000000000000000000000000 : ℝ)*base80 + (454994484223/74000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3864509/312500000000000000000 : ℝ)*base89 + (3864509/312500000000000000000 : ℝ)*base91 + (3864509/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-90687/100000 : ℝ) ≤ (-1507277127348745581202824428709/1662109375000000000000000000000 : ℝ) := by norm_num
    linear_combination (31061407/50000000000000 : ℝ)*(lower1) + (1001557/1562500000000 : ℝ)*(lower2) + (28356697/100000000000000 : ℝ)*(upper5) + (49250027646331/3125000000000 : ℝ)*(major0) + (49250027646331/3125000000000 : ℝ)*(major1) + (49250027646331/3125000000000 : ℝ)*(major2) + (482260053/25000000000000 : ℝ)*(sp0) + (6521547677/20000000000000 : ℝ)*(sp5) + (9936624379/100000000000000 : ℝ)*(sp6) + (1220553253/20000000000000 : ℝ)*(sp7) + (1199581000129561/50000000000000 : ℝ)*(sp12) + (599782830390237/25000000000000 : ℝ)*(sp13) + (1199576996337477/50000000000000 : ℝ)*(sp14) + (783059935074839/100000000000000 : ℝ)*(sp15) + (48941627365069/6250000000000 : ℝ)*(f.failure) + (1199581964649667/50000000000000 : ℝ)*(f.sum) + (2915138241483/425500000000000000000000000 : ℝ)*base65 + (7073841530412763/26593750000000000000000000000000 : ℝ)*base68 + (232323692068493487/26593750000000000000000000000000 : ℝ)*base69 + (310619319190055987/26593750000000000000000000000000 : ℝ)*base71 + (2261476838159/425500000000000000000000000 : ℝ)*base74 + (57295334594805987/26593750000000000000000000000000 : ℝ)*base75 + (398094156383055987/26593750000000000000000000000000 : ℝ)*base77 + (211986784552024737/26593750000000000000000000000000 : ℝ)*base79 + (1724959702941/425500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2785409/312500000000000000000 : ℝ)*base90 + (2785409/312500000000000000000 : ℝ)*base92 + (2785409/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1729_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4239/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2537/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66933/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (20519/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90687/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1729_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1729_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66933/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (20519/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90687/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1729_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1729_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66933/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (20519/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90687/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1729_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
