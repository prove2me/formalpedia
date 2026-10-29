-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1628_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:14.011285+00:00
-- url     : https://prove2.me/submissions/e396d529-0128-425a-baa2-8de87c9b0b9a

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
theorem support_rectangle_w1628_s0_0 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-306411639/2000000000 : ℝ)*x 0 + (5813229367/10000000000 : ℝ)*x 1 + (4906203771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (306411639/2000000000 : ℝ)^4831 ≤ (9249794203717/100000000000000 : ℝ)^3807 := by
    have hnat : (306411639 : ℕ)^4831*100000000000000^3807 ≤ 9249794203717^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306411639 2000000000 9249794203717 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5813229367/10000000000 : ℝ)^4831 ≤ (25120072919521/50000000000000 : ℝ)^3807 := by
    have hnat : (5813229367 : ℕ)^4831*50000000000000^3807 ≤ 25120072919521^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5813229367 10000000000 25120072919521 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4906203771/10000000000 : ℝ)^4831 ≤ (40510059944897/100000000000000 : ℝ)^3807 := by
    have hnat : (4906203771 : ℕ)^4831*100000000000000^3807 ≤ 40510059944897^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906203771 10000000000 40510059944897 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-306411639/2000000000 : ℝ), (5813229367/10000000000 : ℝ), (4906203771/10000000000 : ℝ)] ![(9249794203717/100000000000000 : ℝ), (25120072919521/50000000000000 : ℝ), (40510059944897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-306411639/2000000000 : ℝ)|^4831 ≤ (9249794203717/100000000000000 : ℝ)^3807
        have hw : |(-306411639/2000000000 : ℝ)|=(306411639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5813229367/10000000000 : ℝ)|^4831 ≤ (25120072919521/50000000000000 : ℝ)^3807
        have hw : |(5813229367/10000000000 : ℝ)|=(5813229367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4906203771/10000000000 : ℝ)|^4831 ≤ (40510059944897/100000000000000 : ℝ)^3807
        have hw : |(4906203771/10000000000 : ℝ)|=(4906203771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s0_1 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (68079479/125000000 : ℝ)*x 0 + (-2032260293/10000000000 : ℝ)*x 1 + (981241017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68079479/125000000 : ℝ)^4831 ≤ (23125681439537/50000000000000 : ℝ)^3807 := by
    have hnat : (68079479 : ℕ)^4831*50000000000000^3807 ≤ 23125681439537^3807*125000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68079479 125000000 23125681439537 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2032260293/10000000000 : ℝ)^4831 ≤ (2647712679281/20000000000000 : ℝ)^3807 := by
    have hnat : (2032260293 : ℕ)^4831*20000000000000^3807 ≤ 2647712679281^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032260293 10000000000 2647712679281 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981241017/2000000000 : ℝ)^4831 ≤ (4051007371277/10000000000000 : ℝ)^3807 := by
    have hnat : (981241017 : ℕ)^4831*10000000000000^3807 ≤ 4051007371277^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981241017 2000000000 4051007371277 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68079479/125000000 : ℝ), (-2032260293/10000000000 : ℝ), (981241017/2000000000 : ℝ)] ![(23125681439537/50000000000000 : ℝ), (2647712679281/20000000000000 : ℝ), (4051007371277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68079479/125000000 : ℝ)|^4831 ≤ (23125681439537/50000000000000 : ℝ)^3807
        have hw : |(68079479/125000000 : ℝ)|=(68079479/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2032260293/10000000000 : ℝ)|^4831 ≤ (2647712679281/20000000000000 : ℝ)^3807
        have hw : |(-2032260293/10000000000 : ℝ)|=(2032260293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(981241017/2000000000 : ℝ)|^4831 ≤ (4051007371277/10000000000000 : ℝ)^3807
        have hw : |(981241017/2000000000 : ℝ)|=(981241017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s0_2 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089271671/2000000000 : ℝ)*x 0 + (2453102131/5000000000 : ℝ)*x 1 + (-203226129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089271671/2000000000 : ℝ)^4831 ≤ (46251363256247/100000000000000 : ℝ)^3807 := by
    have hnat : (1089271671 : ℕ)^4831*100000000000000^3807 ≤ 46251363256247^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089271671 2000000000 46251363256247 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2453102131/5000000000 : ℝ)^4831 ≤ (40510065089513/100000000000000 : ℝ)^3807 := by
    have hnat : (2453102131 : ℕ)^4831*100000000000000^3807 ≤ 40510065089513^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453102131 5000000000 40510065089513 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203226129/1000000000 : ℝ)^4831 ≤ (13238571637993/100000000000000 : ℝ)^3807 := by
    have hnat : (203226129 : ℕ)^4831*100000000000000^3807 ≤ 13238571637993^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203226129 1000000000 13238571637993 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089271671/2000000000 : ℝ), (2453102131/5000000000 : ℝ), (-203226129/1000000000 : ℝ)] ![(46251363256247/100000000000000 : ℝ), (40510065089513/100000000000000 : ℝ), (13238571637993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089271671/2000000000 : ℝ)|^4831 ≤ (46251363256247/100000000000000 : ℝ)^3807
        have hw : |(1089271671/2000000000 : ℝ)|=(1089271671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2453102131/5000000000 : ℝ)|^4831 ≤ (40510065089513/100000000000000 : ℝ)^3807
        have hw : |(2453102131/5000000000 : ℝ)|=(2453102131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203226129/1000000000 : ℝ)|^4831 ≤ (13238571637993/100000000000000 : ℝ)^3807
        have hw : |(-203226129/1000000000 : ℝ)|=(203226129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s0_3 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (820208641/2000000000 : ℝ)*x 0 + (1538803873/5000000000 : ℝ)*x 1 + (535939871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820208641/2000000000 : ℝ)^4831 ≤ (16133974543259/50000000000000 : ℝ)^3807 := by
    have hnat : (820208641 : ℕ)^4831*50000000000000^3807 ≤ 16133974543259^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820208641 2000000000 16133974543259 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1538803873/5000000000 : ℝ)^4831 ≤ (22415776768847/100000000000000 : ℝ)^3807 := by
    have hnat : (1538803873 : ℕ)^4831*100000000000000^3807 ≤ 22415776768847^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538803873 5000000000 22415776768847 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535939871/1000000000 : ℝ)^4831 ≤ (1812650965253/4000000000000 : ℝ)^3807 := by
    have hnat : (535939871 : ℕ)^4831*4000000000000^3807 ≤ 1812650965253^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535939871 1000000000 1812650965253 4000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(820208641/2000000000 : ℝ), (1538803873/5000000000 : ℝ), (535939871/1000000000 : ℝ)] ![(16133974543259/50000000000000 : ℝ), (22415776768847/100000000000000 : ℝ), (1812650965253/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(820208641/2000000000 : ℝ)|^4831 ≤ (16133974543259/50000000000000 : ℝ)^3807
        have hw : |(820208641/2000000000 : ℝ)|=(820208641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1538803873/5000000000 : ℝ)|^4831 ≤ (22415776768847/100000000000000 : ℝ)^3807
        have hw : |(1538803873/5000000000 : ℝ)|=(1538803873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(535939871/1000000000 : ℝ)|^4831 ≤ (1812650965253/4000000000000 : ℝ)^3807
        have hw : |(535939871/1000000000 : ℝ)|=(535939871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s0_4 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-306923407/2000000000 : ℝ)*x 0 + (197158497/400000000 : ℝ)*x 1 + (578967143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (306923407/2000000000 : ℝ)^4831 ≤ (9269403030127/100000000000000 : ℝ)^3807 := by
    have hnat : (306923407 : ℕ)^4831*100000000000000^3807 ≤ 9269403030127^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306923407 2000000000 9269403030127 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197158497/400000000 : ℝ)^4831 ≤ (40748669915629/100000000000000 : ℝ)^3807 := by
    have hnat : (197158497 : ℕ)^4831*100000000000000^3807 ≤ 40748669915629^3807*400000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197158497 400000000 40748669915629 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578967143/1000000000 : ℝ)^4831 ≤ (12495481760383/25000000000000 : ℝ)^3807 := by
    have hnat : (578967143 : ℕ)^4831*25000000000000^3807 ≤ 12495481760383^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578967143 1000000000 12495481760383 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-306923407/2000000000 : ℝ), (197158497/400000000 : ℝ), (578967143/1000000000 : ℝ)] ![(9269403030127/100000000000000 : ℝ), (40748669915629/100000000000000 : ℝ), (12495481760383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-306923407/2000000000 : ℝ)|^4831 ≤ (9269403030127/100000000000000 : ℝ)^3807
        have hw : |(-306923407/2000000000 : ℝ)|=(306923407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197158497/400000000 : ℝ)|^4831 ≤ (40748669915629/100000000000000 : ℝ)^3807
        have hw : |(197158497/400000000 : ℝ)|=(197158497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(578967143/1000000000 : ℝ)|^4831 ≤ (12495481760383/25000000000000 : ℝ)^3807
        have hw : |(578967143/1000000000 : ℝ)|=(578967143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s0_5 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198705513/10000000000 : ℝ)*x 0 + (-1148794087/10000000000 : ℝ)*x 1 + (5789671097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198705513/10000000000 : ℝ)^4831 ≤ (21799534942227/50000000000000 : ℝ)^3807 := by
    have hnat : (5198705513 : ℕ)^4831*50000000000000^3807 ≤ 21799534942227^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198705513 10000000000 21799534942227 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1148794087/10000000000 : ℝ)^4831 ≤ (401187919313/6250000000000 : ℝ)^3807 := by
    have hnat : (1148794087 : ℕ)^4831*6250000000000^3807 ≤ 401187919313^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148794087 10000000000 401187919313 6250000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5789671097/10000000000 : ℝ)^4831 ≤ (4998192339351/10000000000000 : ℝ)^3807 := by
    have hnat : (5789671097 : ℕ)^4831*10000000000000^3807 ≤ 4998192339351^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5789671097 10000000000 4998192339351 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198705513/10000000000 : ℝ), (-1148794087/10000000000 : ℝ), (5789671097/10000000000 : ℝ)] ![(21799534942227/50000000000000 : ℝ), (401187919313/6250000000000 : ℝ), (4998192339351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198705513/10000000000 : ℝ)|^4831 ≤ (21799534942227/50000000000000 : ℝ)^3807
        have hw : |(5198705513/10000000000 : ℝ)|=(5198705513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1148794087/10000000000 : ℝ)|^4831 ≤ (401187919313/6250000000000 : ℝ)^3807
        have hw : |(-1148794087/10000000000 : ℝ)|=(1148794087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5789671097/10000000000 : ℝ)|^4831 ≤ (4998192339351/10000000000000 : ℝ)^3807
        have hw : |(5789671097/10000000000 : ℝ)|=(5789671097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s0_6 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599352301/5000000000 : ℝ)*x 0 + (90463633/156250000 : ℝ)*x 1 + (-1148793269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599352301/5000000000 : ℝ)^4831 ≤ (5449882523663/12500000000000 : ℝ)^3807 := by
    have hnat : (2599352301 : ℕ)^4831*12500000000000^3807 ≤ 5449882523663^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599352301 5000000000 5449882523663 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90463633/156250000 : ℝ)^4831 ≤ (24990969447433/50000000000000 : ℝ)^3807 := by
    have hnat : (90463633 : ℕ)^4831*50000000000000^3807 ≤ 24990969447433^3807*156250000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90463633 156250000 24990969447433 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148793269/10000000000 : ℝ)^4831 ≤ (320950045447/5000000000000 : ℝ)^3807 := by
    have hnat : (1148793269 : ℕ)^4831*5000000000000^3807 ≤ 320950045447^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148793269 10000000000 320950045447 5000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599352301/5000000000 : ℝ), (90463633/156250000 : ℝ), (-1148793269/10000000000 : ℝ)] ![(5449882523663/12500000000000 : ℝ), (24990969447433/50000000000000 : ℝ), (320950045447/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599352301/5000000000 : ℝ)|^4831 ≤ (5449882523663/12500000000000 : ℝ)^3807
        have hw : |(2599352301/5000000000 : ℝ)|=(2599352301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90463633/156250000 : ℝ)|^4831 ≤ (24990969447433/50000000000000 : ℝ)^3807
        have hw : |(90463633/156250000 : ℝ)|=(90463633/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1148793269/10000000000 : ℝ)|^4831 ≤ (320950045447/5000000000000 : ℝ)^3807
        have hw : |(-1148793269/10000000000 : ℝ)|=(1148793269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s0_7 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4107478919/10000000000 : ℝ)*x 0 + (2651072501/5000000000 : ℝ)*x 1 + (62737433/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4107478919/10000000000 : ℝ)^4831 ≤ (16166110374157/50000000000000 : ℝ)^3807 := by
    have hnat : (4107478919 : ℕ)^4831*50000000000000^3807 ≤ 16166110374157^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4107478919 10000000000 16166110374157 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2651072501/5000000000 : ℝ)^4831 ≤ (44702837280987/100000000000000 : ℝ)^3807 := by
    have hnat : (2651072501 : ℕ)^4831*100000000000000^3807 ≤ 44702837280987^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651072501 5000000000 44702837280987 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62737433/200000000 : ℝ)^4831 ≤ (4592988391641/20000000000000 : ℝ)^3807 := by
    have hnat : (62737433 : ℕ)^4831*20000000000000^3807 ≤ 4592988391641^3807*200000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62737433 200000000 4592988391641 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4107478919/10000000000 : ℝ), (2651072501/5000000000 : ℝ), (62737433/200000000 : ℝ)] ![(16166110374157/50000000000000 : ℝ), (44702837280987/100000000000000 : ℝ), (4592988391641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4107478919/10000000000 : ℝ)|^4831 ≤ (16166110374157/50000000000000 : ℝ)^3807
        have hw : |(4107478919/10000000000 : ℝ)|=(4107478919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2651072501/5000000000 : ℝ)|^4831 ≤ (44702837280987/100000000000000 : ℝ)^3807
        have hw : |(2651072501/5000000000 : ℝ)|=(2651072501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62737433/200000000 : ℝ)|^4831 ≤ (4592988391641/20000000000000 : ℝ)^3807
        have hw : |(62737433/200000000 : ℝ)|=(62737433/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1628_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1101/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4767/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4827/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4827 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4827*1^1024 ≤ 0^1024*1^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4827/1024 : ℝ) ≤ (1330955853303154867/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4827 ≤ (1330955853303154867/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4827*100000000000000000000^1024 ≤ 1330955853303154867^1024*5^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1330955853303154867 100000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1330955853303154867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4827 := by
      have hnat : (1 : ℕ)^1024*1^4827 ≤ 1^4827*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101330955853303154867/100000000000000000000 : ℝ) ≤ (5014044015200131/5000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (101330955853303154867/100000000000000000000 : ℝ)^1024 ≤ (5014044015200131/5000000000000000 : ℝ)^4827 := by
      have hnat : (101330955853303154867 : ℕ)^1024*5000000000000000^4827 ≤ 5014044015200131^4827*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101330955853303154867 100000000000000000000 5014044015200131 5000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014044015200131/5000000000000000 : ℝ)) (X := (101330955853303154867/100000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51330955853303154867/50000000000000000000 : ℝ) ≤ (2514044015200131/2500000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (51330955853303154867/50000000000000000000 : ℝ)^1024 ≤ (2514044015200131/2500000000000000 : ℝ)^4827 := by
      have hnat : (51330955853303154867 : ℕ)^1024*2500000000000000^4827 ≤ 2514044015200131^4827*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51330955853303154867 50000000000000000000 2514044015200131 2500000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514044015200131/2500000000000000 : ℝ)) (X := (51330955853303154867/50000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14044015200131/2000000000000000 : ℝ)*(0 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14044015200131/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1330955853303154867/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14044015200131/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4827/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14044015200131/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014044015200131/5000000000000000 : ℝ) by norm_num, show 1+(1330955853303154867/100000000000000000000 : ℝ)+(0 : ℝ)=(101330955853303154867/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1330955853303154867/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14044015200131/2000000000000000 : ℝ)*(2/5 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14044015200131/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514044015200131/2500000000000000 : ℝ) by norm_num, show 1+2*(1330955853303154867/100000000000000000000 : ℝ)=(51330955853303154867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14044015200131/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14044015200131/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14044015200131/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14044015200131/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14044015200131/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14044015200131/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-306411639/2000000000 : ℝ)*X 0 0+(5813229367/10000000000 : ℝ)*X 0 1+(4906203771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((68079479/125000000 : ℝ)*X 1 0+(-2032260293/10000000000 : ℝ)*X 1 1+(981241017/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1089271671/2000000000 : ℝ)*X 2 0+(2453102131/5000000000 : ℝ)*X 2 1+(-203226129/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((820208641/2000000000 : ℝ)*X 0 0+(1538803873/5000000000 : ℝ)*X 0 1+(535939871/1000000000 : ℝ)*X 0 2+(820208641/2000000000 : ℝ)*X 1 0+(1538803873/5000000000 : ℝ)*X 1 1+(535939871/1000000000 : ℝ)*X 1 2+(820208641/2000000000 : ℝ)*X 2 0+(1538803873/5000000000 : ℝ)*X 2 1+(535939871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-306923407/2000000000 : ℝ)*X 0 0+(197158497/400000000 : ℝ)*X 0 1+(578967143/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198705513/10000000000 : ℝ)*X 1 0+(-1148794087/10000000000 : ℝ)*X 1 1+(5789671097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599352301/5000000000 : ℝ)*X 2 0+(90463633/156250000 : ℝ)*X 2 1+(-1148793269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4107478919/10000000000 : ℝ)*X 0 0+(2651072501/5000000000 : ℝ)*X 0 1+(62737433/200000000 : ℝ)*X 0 2+(4107478919/10000000000 : ℝ)*X 1 0+(2651072501/5000000000 : ℝ)*X 1 1+(62737433/200000000 : ℝ)*X 1 2+(4107478919/10000000000 : ℝ)*X 2 0+(2651072501/5000000000 : ℝ)*X 2 1+(62737433/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (279567297348450363919629/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49817073/5000000000000 : ℝ)*(base19) + (1038073057/100000000000000 : ℝ)*(base23) + (12366679/50000000000000 : ℝ)*(upper2) + (297445459/100000000000000 : ℝ)*(upper3) + (5863633/100000000000000 : ℝ)*(upper4) + (770386022191653/100000000000000 : ℝ)*(major0) + (770386022191653/100000000000000 : ℝ)*(major1) + (770386022191653/100000000000000 : ℝ)*(major2) + (551255522469353/50000000000000 : ℝ)*(sp0) + (4306695571037/390625000000 : ℝ)*(sp1) + (8820112195631/800000000000 : ℝ)*(sp2) + (219127008520223/50000000000000 : ℝ)*(sp3) + (4017588227/100000000000000 : ℝ)*(sp4) + (111137509/4000000000000 : ℝ)*(sp7) + (438256795478171/100000000000000 : ℝ)*(f.failure) + (275628765631733/25000000000000 : ℝ)*(f.sum) + (242549423706543/100000000000000000000000000000 : ℝ)*base65 + (771674915893457/200000000000000000000000000000 : ℝ)*base68 + (1639493136493457/200000000000000000000000000000 : ℝ)*base70 + (1120490883706543/200000000000000000000000000000 : ℝ)*base71 + (53669154293457/100000000000000000000000000000 : ℝ)*base74 + (453935173293457/200000000000000000000000000000 : ℝ)*base76 + (945118833293457/200000000000000000000000000000 : ℝ)*base78 + (966751949506543/200000000000000000000000000000 : ℝ)*base79 + (127408183293457/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7906811/10000000000000000000000 : ℝ)*base90 + (7906811/10000000000000000000000 : ℝ)*base92 + (7906811/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (320350955692702103882151/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85131231/10000000000000 : ℝ)*(base19) + (1248970799/100000000000000 : ℝ)*(base23) + (312831443/50000000000000 : ℝ)*(base39) + (56312033/100000000000000 : ℝ)*(upper3) + (94098357/25000000000000 : ℝ)*(upper5) + (405915866255807/50000000000000 : ℝ)*(major0) + (405915866255807/50000000000000 : ℝ)*(major1) + (101478888356091/12500000000000 : ℝ)*(major2) + (2981773681/100000000000000 : ℝ)*(sp1) + (2646743407/100000000000000 : ℝ)*(sp2) + (580914108203569/50000000000000 : ℝ)*(sp4) + (290456095830287/25000000000000 : ℝ)*(sp5) + (580912473177909/50000000000000 : ℝ)*(sp6) + (57729301173237/12500000000000 : ℝ)*(sp7) + (57729301173237/12500000000000 : ℝ)*(f.failure) + (145228605258753/12500000000000 : ℝ)*(f.sum) + (57974482097599/100000000000000000000000000000 : ℝ)*base66 + (87013921797921/25000000000000000000000000000 : ℝ)*base67 + (424316828089283/100000000000000000000000000000 : ℝ)*base70 + (80858823852079/25000000000000000000000000000 : ℝ)*base72 + (299329439002401/100000000000000000000000000000 : ℝ)*base73 + (560232818189283/100000000000000000000000000000 : ℝ)*base76 + (297813111410717/100000000000000000000000000000 : ℝ)*base77 + (270038021710717/100000000000000000000000000000 : ℝ)*base79 + (137727470489283/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4352683/1250000000000000000000 : ℝ)*base89 + (4352683/1250000000000000000000 : ℝ)*base91 + (4352683/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1628_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1101/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4767/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1628_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1628_s1_0 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1647327133/10000000000 : ℝ)*x 0 + (2756919059/5000000000 : ℝ)*x 1 + (5130882179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1647327133/10000000000 : ℝ)^4831 ≤ (10141698784453/100000000000000 : ℝ)^3807 := by
    have hnat : (1647327133 : ℕ)^4831*100000000000000^3807 ≤ 10141698784453^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1647327133 10000000000 10141698784453 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756919059/5000000000 : ℝ)^4831 ≤ (46979758211303/100000000000000 : ℝ)^3807 := by
    have hnat : (2756919059 : ℕ)^4831*100000000000000^3807 ≤ 46979758211303^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756919059 5000000000 46979758211303 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5130882179/10000000000 : ℝ)^4831 ≤ (8575708599197/20000000000000 : ℝ)^3807 := by
    have hnat : (5130882179 : ℕ)^4831*20000000000000^3807 ≤ 8575708599197^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130882179 10000000000 8575708599197 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1647327133/10000000000 : ℝ), (2756919059/5000000000 : ℝ), (5130882179/10000000000 : ℝ)] ![(10141698784453/100000000000000 : ℝ), (46979758211303/100000000000000 : ℝ), (8575708599197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1647327133/10000000000 : ℝ)|^4831 ≤ (10141698784453/100000000000000 : ℝ)^3807
        have hw : |(-1647327133/10000000000 : ℝ)|=(1647327133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756919059/5000000000 : ℝ)|^4831 ≤ (46979758211303/100000000000000 : ℝ)^3807
        have hw : |(2756919059/5000000000 : ℝ)|=(2756919059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5130882179/10000000000 : ℝ)|^4831 ≤ (8575708599197/20000000000000 : ℝ)^3807
        have hw : |(5130882179/10000000000 : ℝ)|=(5130882179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s1_1 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341680017/2500000000 : ℝ)*x 0 + (-1847034007/10000000000 : ℝ)*x 1 + (2565440977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341680017/2500000000 : ℝ)^4831 ≤ (45394845385943/100000000000000 : ℝ)^3807 := by
    have hnat : (1341680017 : ℕ)^4831*100000000000000^3807 ≤ 45394845385943^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341680017 2500000000 45394845385943 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847034007/10000000000 : ℝ)^4831 ≤ (2931653498791/25000000000000 : ℝ)^3807 := by
    have hnat : (1847034007 : ℕ)^4831*25000000000000^3807 ≤ 2931653498791^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847034007 10000000000 2931653498791 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565440977/5000000000 : ℝ)^4831 ≤ (42878540609907/100000000000000 : ℝ)^3807 := by
    have hnat : (2565440977 : ℕ)^4831*100000000000000^3807 ≤ 42878540609907^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565440977 5000000000 42878540609907 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341680017/2500000000 : ℝ), (-1847034007/10000000000 : ℝ), (2565440977/5000000000 : ℝ)] ![(45394845385943/100000000000000 : ℝ), (2931653498791/25000000000000 : ℝ), (42878540609907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341680017/2500000000 : ℝ)|^4831 ≤ (45394845385943/100000000000000 : ℝ)^3807
        have hw : |(1341680017/2500000000 : ℝ)|=(1341680017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1847034007/10000000000 : ℝ)|^4831 ≤ (2931653498791/25000000000000 : ℝ)^3807
        have hw : |(-1847034007/10000000000 : ℝ)|=(1847034007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565440977/5000000000 : ℝ)|^4831 ≤ (42878540609907/100000000000000 : ℝ)^3807
        have hw : |(2565440977/5000000000 : ℝ)|=(2565440977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s1_2 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683360343/5000000000 : ℝ)*x 0 + (641360147/1250000000 : ℝ)*x 1 + (-1847034207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683360343/5000000000 : ℝ)^4831 ≤ (9078970403881/20000000000000 : ℝ)^3807 := by
    have hnat : (2683360343 : ℕ)^4831*20000000000000^3807 ≤ 9078970403881^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683360343 5000000000 9078970403881 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641360147/1250000000 : ℝ)^4831 ≤ (42878532359379/100000000000000 : ℝ)^3807 := by
    have hnat : (641360147 : ℕ)^4831*100000000000000^3807 ≤ 42878532359379^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641360147 1250000000 42878532359379 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1847034207/10000000000 : ℝ)^4831 ≤ (2345323121297/20000000000000 : ℝ)^3807 := by
    have hnat : (1847034207 : ℕ)^4831*20000000000000^3807 ≤ 2345323121297^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847034207 10000000000 2345323121297 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683360343/5000000000 : ℝ), (641360147/1250000000 : ℝ), (-1847034207/10000000000 : ℝ)] ![(9078970403881/20000000000000 : ℝ), (42878532359379/100000000000000 : ℝ), (2345323121297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683360343/5000000000 : ℝ)|^4831 ≤ (9078970403881/20000000000000 : ℝ)^3807
        have hw : |(2683360343/5000000000 : ℝ)|=(2683360343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641360147/1250000000 : ℝ)|^4831 ≤ (42878532359379/100000000000000 : ℝ)^3807
        have hw : |(641360147/1250000000 : ℝ)|=(641360147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1847034207/10000000000 : ℝ)|^4831 ≤ (2345323121297/20000000000000 : ℝ)^3807
        have hw : |(-1847034207/10000000000 : ℝ)|=(1847034207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s1_3 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4188624559/10000000000 : ℝ)*x 0 + (3727624459/10000000000 : ℝ)*x 1 + (2345511009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188624559/10000000000 : ℝ)^4831 ≤ (8286228381837/25000000000000 : ℝ)^3807 := by
    have hnat : (4188624559 : ℕ)^4831*25000000000000^3807 ≤ 8286228381837^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188624559 10000000000 8286228381837 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3727624459/10000000000 : ℝ)^4831 ≤ (28586220900749/100000000000000 : ℝ)^3807 := by
    have hnat : (3727624459 : ℕ)^4831*100000000000000^3807 ≤ 28586220900749^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727624459 10000000000 28586220900749 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2345511009/5000000000 : ℝ)^4831 ≤ (478360819467/1250000000000 : ℝ)^3807 := by
    have hnat : (2345511009 : ℕ)^4831*1250000000000^3807 ≤ 478360819467^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345511009 5000000000 478360819467 1250000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188624559/10000000000 : ℝ), (3727624459/10000000000 : ℝ), (2345511009/5000000000 : ℝ)] ![(8286228381837/25000000000000 : ℝ), (28586220900749/100000000000000 : ℝ), (478360819467/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188624559/10000000000 : ℝ)|^4831 ≤ (8286228381837/25000000000000 : ℝ)^3807
        have hw : |(4188624559/10000000000 : ℝ)|=(4188624559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3727624459/10000000000 : ℝ)|^4831 ≤ (28586220900749/100000000000000 : ℝ)^3807
        have hw : |(3727624459/10000000000 : ℝ)|=(3727624459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2345511009/5000000000 : ℝ)|^4831 ≤ (478360819467/1250000000000 : ℝ)^3807
        have hw : |(2345511009/5000000000 : ℝ)|=(2345511009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s1_4 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1647516341/10000000000 : ℝ)*x 0 + (5134913757/10000000000 : ℝ)*x 1 + (1101949261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1647516341/10000000000 : ℝ)^4831 ≤ (253579424443/2500000000000 : ℝ)^3807 := by
    have hnat : (1647516341 : ℕ)^4831*2500000000000^3807 ≤ 253579424443^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1647516341 10000000000 253579424443 2500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134913757/10000000000 : ℝ)^4831 ≤ (10730325389409/25000000000000 : ℝ)^3807 := by
    have hnat : (5134913757 : ℕ)^4831*25000000000000^3807 ≤ 10730325389409^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134913757 10000000000 10730325389409 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101949261/2000000000 : ℝ)^4831 ≤ (46935521447313/100000000000000 : ℝ)^3807 := by
    have hnat : (1101949261 : ℕ)^4831*100000000000000^3807 ≤ 46935521447313^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101949261 2000000000 46935521447313 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1647516341/10000000000 : ℝ), (5134913757/10000000000 : ℝ), (1101949261/2000000000 : ℝ)] ![(253579424443/2500000000000 : ℝ), (10730325389409/25000000000000 : ℝ), (46935521447313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1647516341/10000000000 : ℝ)|^4831 ≤ (253579424443/2500000000000 : ℝ)^3807
        have hw : |(-1647516341/10000000000 : ℝ)|=(1647516341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134913757/10000000000 : ℝ)|^4831 ≤ (10730325389409/25000000000000 : ℝ)^3807
        have hw : |(5134913757/10000000000 : ℝ)|=(5134913757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101949261/2000000000 : ℝ)|^4831 ≤ (46935521447313/100000000000000 : ℝ)^3807
        have hw : |(1101949261/2000000000 : ℝ)|=(1101949261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s1_5 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658073363/1250000000 : ℝ)*x 0 + (-11745351/80000000 : ℝ)*x 1 + (110194933/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658073363/1250000000 : ℝ)^4831 ≤ (44301391785453/100000000000000 : ℝ)^3807 := by
    have hnat : (658073363 : ℕ)^4831*100000000000000^3807 ≤ 44301391785453^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658073363 1250000000 44301391785453 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11745351/80000000 : ℝ)^4831 ≤ (8763083021087/100000000000000 : ℝ)^3807 := by
    have hnat : (11745351 : ℕ)^4831*100000000000000^3807 ≤ 8763083021087^3807*80000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11745351 80000000 8763083021087 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110194933/200000000 : ℝ)^4831 ≤ (187742100707/400000000000 : ℝ)^3807 := by
    have hnat : (110194933 : ℕ)^4831*400000000000^3807 ≤ 187742100707^3807*200000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110194933 200000000 187742100707 400000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658073363/1250000000 : ℝ), (-11745351/80000000 : ℝ), (110194933/200000000 : ℝ)] ![(44301391785453/100000000000000 : ℝ), (8763083021087/100000000000000 : ℝ), (187742100707/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658073363/1250000000 : ℝ)|^4831 ≤ (44301391785453/100000000000000 : ℝ)^3807
        have hw : |(658073363/1250000000 : ℝ)|=(658073363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11745351/80000000 : ℝ)|^4831 ≤ (8763083021087/100000000000000 : ℝ)^3807
        have hw : |(-11745351/80000000 : ℝ)|=(11745351/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110194933/200000000 : ℝ)|^4831 ≤ (187742100707/400000000000 : ℝ)^3807
        have hw : |(110194933/200000000 : ℝ)|=(110194933/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s1_6 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211669/8000000 : ℝ)*x 0 + (550974689/1000000000 : ℝ)*x 1 + (-293633891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211669/8000000 : ℝ)^4831 ≤ (44301384801763/100000000000000 : ℝ)^3807 := by
    have hnat : (4211669 : ℕ)^4831*100000000000000^3807 ≤ 44301384801763^3807*8000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211669 8000000 44301384801763 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550974689/1000000000 : ℝ)^4831 ≤ (23467763885571/50000000000000 : ℝ)^3807 := by
    have hnat : (550974689 : ℕ)^4831*50000000000000^3807 ≤ 23467763885571^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550974689 1000000000 23467763885571 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293633891/2000000000 : ℝ)^4831 ≤ (4381543707053/50000000000000 : ℝ)^3807 := by
    have hnat : (293633891 : ℕ)^4831*50000000000000^3807 ≤ 4381543707053^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293633891 2000000000 4381543707053 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211669/8000000 : ℝ), (550974689/1000000000 : ℝ), (-293633891/2000000000 : ℝ)] ![(44301384801763/100000000000000 : ℝ), (23467763885571/50000000000000 : ℝ), (4381543707053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211669/8000000 : ℝ)|^4831 ≤ (44301384801763/100000000000000 : ℝ)^3807
        have hw : |(4211669/8000000 : ℝ)|=(4211669/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550974689/1000000000 : ℝ)|^4831 ≤ (23467763885571/50000000000000 : ℝ)^3807
        have hw : |(550974689/1000000000 : ℝ)|=(550974689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-293633891/2000000000 : ℝ)|^4831 ≤ (4381543707053/50000000000000 : ℝ)^3807
        have hw : |(-293633891/2000000000 : ℝ)|=(293633891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s1_7 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (837819573/2000000000 : ℝ)*x 0 + (4680880679/10000000000 : ℝ)*x 1 + (467239663/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837819573/2000000000 : ℝ)^4831 ≤ (16574833156487/50000000000000 : ℝ)^3807 := by
    have hnat : (837819573 : ℕ)^4831*50000000000000^3807 ≤ 16574833156487^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837819573 2000000000 16574833156487 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4680880679/10000000000 : ℝ)^4831 ≤ (381639110189/1000000000000 : ℝ)^3807 := by
    have hnat : (4680880679 : ℕ)^4831*1000000000000^3807 ≤ 381639110189^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4680880679 10000000000 381639110189 1000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467239663/1250000000 : ℝ)^4831 ≤ (2868642265519/10000000000000 : ℝ)^3807 := by
    have hnat : (467239663 : ℕ)^4831*10000000000000^3807 ≤ 2868642265519^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467239663 1250000000 2868642265519 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837819573/2000000000 : ℝ), (4680880679/10000000000 : ℝ), (467239663/1250000000 : ℝ)] ![(16574833156487/50000000000000 : ℝ), (381639110189/1000000000000 : ℝ), (2868642265519/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837819573/2000000000 : ℝ)|^4831 ≤ (16574833156487/50000000000000 : ℝ)^3807
        have hw : |(837819573/2000000000 : ℝ)|=(837819573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4680880679/10000000000 : ℝ)|^4831 ≤ (381639110189/1000000000000 : ℝ)^3807
        have hw : |(4680880679/10000000000 : ℝ)|=(4680880679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467239663/1250000000 : ℝ)|^4831 ≤ (2868642265519/10000000000000 : ℝ)^3807
        have hw : |(467239663/1250000000 : ℝ)|=(467239663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1628_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4767/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4717/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17559/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4767/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1101/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4767/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1101/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4767/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1101/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4767/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1101/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4767/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1101/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4767/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1101/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1101/25000 : ℝ) ^ (4827/1024 : ℝ) ≤ (20241669946039/50000000000000000000 : ℝ) := by
    have hpowers : (1101/25000 : ℝ)^4827 ≤ (20241669946039/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1101 : ℕ)^4827*50000000000000000000^1024 ≤ 20241669946039^1024*25000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1101 25000 20241669946039 50000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1101/25000 : ℝ)) (X := (20241669946039/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4767/20000 : ℝ) ^ (4827/1024 : ℝ) ≤ (28987780820057731/25000000000000000000 : ℝ) := by
    have hpowers : (4767/20000 : ℝ)^4827 ≤ (28987780820057731/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4767 : ℕ)^4827*25000000000000000000^1024 ≤ 28987780820057731^1024*20000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4767 20000 28987780820057731 25000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4767/20000 : ℝ)) (X := (28987780820057731/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000020241669946039/25000000000000000000 : ℝ) ≤ (10000001717626967/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (25000020241669946039/25000000000000000000 : ℝ)^1024 ≤ (10000001717626967/10000000000000000 : ℝ)^4827 := by
      have hnat : (25000020241669946039 : ℕ)^1024*10000000000000000^4827 ≤ 10000001717626967^4827*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000020241669946039 25000000000000000000 10000001717626967 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001717626967/10000000000000000 : ℝ)) (X := (25000020241669946039/25000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50057995803310061501/50000000000000000000 : ℝ) ≤ (10002459522915433/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (50057995803310061501/50000000000000000000 : ℝ)^1024 ≤ (10002459522915433/10000000000000000 : ℝ)^4827 := by
      have hnat : (50057995803310061501 : ℕ)^1024*10000000000000000^4827 ≤ 10002459522915433^4827*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057995803310061501 50000000000000000000 10002459522915433 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002459522915433/10000000000000000 : ℝ)) (X := (50057995803310061501/50000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12528987780820057731/12500000000000000000 : ℝ) ≤ (10004917328203899/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (12528987780820057731/12500000000000000000 : ℝ)^1024 ≤ (10004917328203899/10000000000000000 : ℝ)^4827 := by
      have hnat : (12528987780820057731 : ℕ)^1024*10000000000000000^4827 ≤ 10004917328203899^4827*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12528987780820057731 12500000000000000000 10004917328203899 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004917328203899/10000000000000000 : ℝ)) (X := (12528987780820057731/12500000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20241669946039/50000000000000000000 : ℝ) ≤ ((64762795008742929083/64770000000000000000 : ℝ)+2*(1228902644233/971550000000000 : ℝ)*(1101/25000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (64762795008742929083/64770000000000000000 : ℝ)+2*(1228902644233/971550000000000 : ℝ)*(1101/25000 : ℝ)=(10000001717626967/10000000000000000 : ℝ) by norm_num, show 1+2*(20241669946039/50000000000000000000 : ℝ)=(25000020241669946039/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28987780820057731/25000000000000000000 : ℝ)+(20241669946039/50000000000000000000 : ℝ) ≤ ((64762795008742929083/64770000000000000000 : ℝ)+(1228902644233/971550000000000 : ℝ)*((4767/20000 : ℝ)+(1101/25000 : ℝ)))^(4827/1024 : ℝ) := by
    rw [show (64762795008742929083/64770000000000000000 : ℝ)+(1228902644233/971550000000000 : ℝ)*((4767/20000 : ℝ)+(1101/25000 : ℝ))=(10002459522915433/10000000000000000 : ℝ) by norm_num, show 1+(28987780820057731/25000000000000000000 : ℝ)+(20241669946039/50000000000000000000 : ℝ)=(50057995803310061501/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28987780820057731/25000000000000000000 : ℝ) ≤ ((64762795008742929083/64770000000000000000 : ℝ)+2*(1228902644233/971550000000000 : ℝ)*(4767/20000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (64762795008742929083/64770000000000000000 : ℝ)+2*(1228902644233/971550000000000 : ℝ)*(4767/20000 : ℝ)=(10004917328203899/10000000000000000 : ℝ) by norm_num, show 1+2*(28987780820057731/25000000000000000000 : ℝ)=(12528987780820057731/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64762795008742929083/64770000000000000000 : ℝ)*(X 1 0+X 2 0)+(1228902644233/971550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (1101/25000 : ℝ)) (hi := (4767/20000 : ℝ)) (c := (64762795008742929083/64770000000000000000 : ℝ)) (alpha := (1228902644233/971550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64762795008742929083/64770000000000000000 : ℝ)*(X 0 1+X 2 1)+(1228902644233/971550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (1101/25000 : ℝ)) (hi := (4767/20000 : ℝ)) (c := (64762795008742929083/64770000000000000000 : ℝ)) (alpha := (1228902644233/971550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64762795008742929083/64770000000000000000 : ℝ)*(X 0 2+X 1 2)+(1228902644233/971550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (1101/25000 : ℝ)) (hi := (4767/20000 : ℝ)) (c := (64762795008742929083/64770000000000000000 : ℝ)) (alpha := (1228902644233/971550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1647327133/10000000000 : ℝ)*X 0 0+(2756919059/5000000000 : ℝ)*X 0 1+(5130882179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1341680017/2500000000 : ℝ)*X 1 0+(-1847034007/10000000000 : ℝ)*X 1 1+(2565440977/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683360343/5000000000 : ℝ)*X 2 0+(641360147/1250000000 : ℝ)*X 2 1+(-1847034207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4188624559/10000000000 : ℝ)*X 0 0+(3727624459/10000000000 : ℝ)*X 0 1+(2345511009/5000000000 : ℝ)*X 0 2+(4188624559/10000000000 : ℝ)*X 1 0+(3727624459/10000000000 : ℝ)*X 1 1+(2345511009/5000000000 : ℝ)*X 1 2+(4188624559/10000000000 : ℝ)*X 2 0+(3727624459/10000000000 : ℝ)*X 2 1+(2345511009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1647516341/10000000000 : ℝ)*X 0 0+(5134913757/10000000000 : ℝ)*X 0 1+(1101949261/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((658073363/1250000000 : ℝ)*X 1 0+(-11745351/80000000 : ℝ)*X 1 1+(110194933/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4211669/8000000 : ℝ)*X 2 0+(550974689/1000000000 : ℝ)*X 2 1+(-293633891/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((837819573/2000000000 : ℝ)*X 0 0+(4680880679/10000000000 : ℝ)*X 0 1+(467239663/1250000000 : ℝ)*X 0 2+(837819573/2000000000 : ℝ)*X 1 0+(4680880679/10000000000 : ℝ)*X 1 1+(467239663/1250000000 : ℝ)*X 1 2+(837819573/2000000000 : ℝ)*X 2 0+(4680880679/10000000000 : ℝ)*X 2 1+(467239663/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14227666443362141213235286823/1619250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423957661/100000000000000 : ℝ)*(base1) + (1381434569/100000000000000 : ℝ)*(base19) + (84106687/5000000000000 : ℝ)*(base23) + (37777899/20000000000000 : ℝ)*(upper3) + (59370493/50000000000000 : ℝ)*(upper5) + (1824638435743927/100000000000000 : ℝ)*(major0) + (1824638435743927/100000000000000 : ℝ)*(major1) + (1824638435743927/100000000000000 : ℝ)*(major2) + (2611272172056407/100000000000000 : ℝ)*(sp0) + (2611275842661273/100000000000000 : ℝ)*(sp1) + (1305637770981051/50000000000000 : ℝ)*(sp2) + (207599117761269/20000000000000 : ℝ)*(sp3) + (1095199419/20000000000000 : ℝ)*(sp4) + (3341742067/100000000000000 : ℝ)*(sp7) + (129749919313259/12500000000000 : ℝ)*(f.failure) + (1305638612047921/50000000000000 : ℝ)*(f.sum) + (127735421930519/48577500000000000000000000000 : ℝ)*base66 + (93525141811134013177/19431000000000000000000000000000000 : ℝ)*base68 + (32826829172061013177/19431000000000000000000000000000000 : ℝ)*base70 + (14278695475730986823/19431000000000000000000000000000000 : ℝ)*base71 + (427582058508253/97155000000000000000000000000 : ℝ)*base74 + (191078967574695013177/19431000000000000000000000000000000 : ℝ)*base76 + (170236436817117013177/19431000000000000000000000000000000 : ℝ)*base78 + (83555756578875013177/19431000000000000000000000000000000 : ℝ)*base80 + (162308766086969/48577500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3364181/1250000000000000000000 : ℝ)*base89 + (3364181/1250000000000000000000 : ℝ)*base91 + (3364181/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1104972105789654492651922363/107950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1990253893/100000000000000 : ℝ)*(base19) + (1694433847/100000000000000 : ℝ)*(base23) + (4942653/20000000000000 : ℝ)*(upper2) + (405496099/100000000000000 : ℝ)*(upper3) + (105446301/100000000000000 : ℝ)*(upper5) + (186416971980161/10000000000000 : ℝ)*(major0) + (186416971980161/10000000000000 : ℝ)*(major1) + (186416971980161/10000000000000 : ℝ)*(major2) + (1914335099/12500000000000 : ℝ)*(sp1) + (14729678409/100000000000000 : ℝ)*(sp2) + (666962801949191/25000000000000 : ℝ)*(sp4) + (2084245236611/78125000000 : ℝ)*(sp5) + (2667834783684509/100000000000000 : ℝ)*(sp6) + (530243945303857/50000000000000 : ℝ)*(sp7) + (530243945303857/50000000000000 : ℝ)*(f.failure) + (666962801949191/25000000000000 : ℝ)*(f.sum) + (42348445367507/9715500000000000000000000000 : ℝ)*base66 + (13335008966182967089/1943100000000000000000000000000000 : ℝ)*base67 + (16478361987744767089/1943100000000000000000000000000000 : ℝ)*base69 + (6360300496256232911/1943100000000000000000000000000000 : ℝ)*base72 + (5888859693113/1943100000000000000000000000 : ℝ)*base73 + (2943510393274032911/1943100000000000000000000000000000 : ℝ)*base76 + (6749961313885032911/1943100000000000000000000000000000 : ℝ)*base78 + (14552311025359632911/1943100000000000000000000000000000 : ℝ)*base80 + (32843076338557/9715500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2201263/5000000000000000000000 : ℝ)*base89 + (2201263/5000000000000000000000 : ℝ)*base91 + (2201263/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1628_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4767/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17559/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1628_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1628_s2_0 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-829473711/5000000000 : ℝ)*x 0 + (218372837/400000000 : ℝ)*x 1 + (258888251/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829473711/5000000000 : ℝ)^4831 ≤ (2046513444197/20000000000000 : ℝ)^3807 := by
    have hnat : (829473711 : ℕ)^4831*20000000000000^3807 ≤ 2046513444197^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829473711 5000000000 2046513444197 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218372837/400000000 : ℝ)^4831 ≤ (46391097391179/100000000000000 : ℝ)^3807 := by
    have hnat : (218372837 : ℕ)^4831*100000000000000^3807 ≤ 46391097391179^3807*400000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218372837 400000000 46391097391179 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258888251/500000000 : ℝ)^4831 ≤ (21688167688281/50000000000000 : ℝ)^3807 := by
    have hnat : (258888251 : ℕ)^4831*50000000000000^3807 ≤ 21688167688281^3807*500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258888251 500000000 21688167688281 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-829473711/5000000000 : ℝ), (218372837/400000000 : ℝ), (258888251/500000000 : ℝ)] ![(2046513444197/20000000000000 : ℝ), (46391097391179/100000000000000 : ℝ), (21688167688281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-829473711/5000000000 : ℝ)|^4831 ≤ (2046513444197/20000000000000 : ℝ)^3807
        have hw : |(-829473711/5000000000 : ℝ)|=(829473711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218372837/400000000 : ℝ)|^4831 ≤ (46391097391179/100000000000000 : ℝ)^3807
        have hw : |(218372837/400000000 : ℝ)|=(218372837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258888251/500000000 : ℝ)|^4831 ≤ (21688167688281/50000000000000 : ℝ)^3807
        have hw : |(258888251/500000000 : ℝ)|=(258888251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s2_1 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352406979/10000000000 : ℝ)*x 0 + (-1804174631/10000000000 : ℝ)*x 1 + (1035553013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352406979/10000000000 : ℝ)^4831 ≤ (45241267308261/100000000000000 : ℝ)^3807 := by
    have hnat : (5352406979 : ℕ)^4831*100000000000000^3807 ≤ 45241267308261^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352406979 10000000000 45241267308261 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804174631/10000000000 : ℝ)^4831 ≤ (88924975157/781250000000 : ℝ)^3807 := by
    have hnat : (1804174631 : ℕ)^4831*781250000000^3807 ≤ 88924975157^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804174631 10000000000 88924975157 781250000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035553013/2000000000 : ℝ)^4831 ≤ (43376335854947/100000000000000 : ℝ)^3807 := by
    have hnat : (1035553013 : ℕ)^4831*100000000000000^3807 ≤ 43376335854947^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035553013 2000000000 43376335854947 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352406979/10000000000 : ℝ), (-1804174631/10000000000 : ℝ), (1035553013/2000000000 : ℝ)] ![(45241267308261/100000000000000 : ℝ), (88924975157/781250000000 : ℝ), (43376335854947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352406979/10000000000 : ℝ)|^4831 ≤ (45241267308261/100000000000000 : ℝ)^3807
        have hw : |(5352406979/10000000000 : ℝ)|=(5352406979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1804174631/10000000000 : ℝ)|^4831 ≤ (88924975157/781250000000 : ℝ)^3807
        have hw : |(-1804174631/10000000000 : ℝ)|=(1804174631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035553013/2000000000 : ℝ)|^4831 ≤ (43376335854947/100000000000000 : ℝ)^3807
        have hw : |(1035553013/2000000000 : ℝ)|=(1035553013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s2_2 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352407057/10000000000 : ℝ)*x 0 + (2588882469/5000000000 : ℝ)*x 1 + (-360834939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352407057/10000000000 : ℝ)^4831 ≤ (45241268144893/100000000000000 : ℝ)^3807 := by
    have hnat : (5352407057 : ℕ)^4831*100000000000000^3807 ≤ 45241268144893^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352407057 10000000000 45241268144893 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588882469/5000000000 : ℝ)^4831 ≤ (43376334504839/100000000000000 : ℝ)^3807 := by
    have hnat : (2588882469 : ℕ)^4831*100000000000000^3807 ≤ 43376334504839^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588882469 5000000000 43376334504839 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360834939/2000000000 : ℝ)^4831 ≤ (11382397332473/100000000000000 : ℝ)^3807 := by
    have hnat : (360834939 : ℕ)^4831*100000000000000^3807 ≤ 11382397332473^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360834939 2000000000 11382397332473 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352407057/10000000000 : ℝ), (2588882469/5000000000 : ℝ), (-360834939/2000000000 : ℝ)] ![(45241268144893/100000000000000 : ℝ), (43376334504839/100000000000000 : ℝ), (11382397332473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352407057/10000000000 : ℝ)|^4831 ≤ (45241268144893/100000000000000 : ℝ)^3807
        have hw : |(5352407057/10000000000 : ℝ)|=(5352407057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588882469/5000000000 : ℝ)|^4831 ≤ (43376334504839/100000000000000 : ℝ)^3807
        have hw : |(2588882469/5000000000 : ℝ)|=(2588882469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-360834939/2000000000 : ℝ)|^4831 ≤ (11382397332473/100000000000000 : ℝ)^3807
        have hw : |(-360834939/2000000000 : ℝ)|=(360834939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s2_3 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4197239977/10000000000 : ℝ)*x 0 + (3854280159/10000000000 : ℝ)*x 1 + (7300137/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197239977/10000000000 : ℝ)^4831 ≤ (33231449370507/100000000000000 : ℝ)^3807 := by
    have hnat : (4197239977 : ℕ)^4831*100000000000000^3807 ≤ 33231449370507^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197239977 10000000000 33231449370507 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3854280159/10000000000 : ℝ)^4831 ≤ (14912177109531/50000000000000 : ℝ)^3807 := by
    have hnat : (3854280159 : ℕ)^4831*50000000000000^3807 ≤ 14912177109531^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3854280159 10000000000 14912177109531 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7300137/16000000 : ℝ)^4831 ≤ (36944196387697/100000000000000 : ℝ)^3807 := by
    have hnat : (7300137 : ℕ)^4831*100000000000000^3807 ≤ 36944196387697^3807*16000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7300137 16000000 36944196387697 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197239977/10000000000 : ℝ), (3854280159/10000000000 : ℝ), (7300137/16000000 : ℝ)] ![(33231449370507/100000000000000 : ℝ), (14912177109531/50000000000000 : ℝ), (36944196387697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197239977/10000000000 : ℝ)|^4831 ≤ (33231449370507/100000000000000 : ℝ)^3807
        have hw : |(4197239977/10000000000 : ℝ)|=(4197239977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3854280159/10000000000 : ℝ)|^4831 ≤ (14912177109531/50000000000000 : ℝ)^3807
        have hw : |(3854280159/10000000000 : ℝ)|=(3854280159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7300137/16000000 : ℝ)|^4831 ≤ (36944196387697/100000000000000 : ℝ)^3807
        have hw : |(7300137/16000000 : ℝ)|=(7300137/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s2_4 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-829511083/5000000000 : ℝ)*x 0 + (5179951227/10000000000 : ℝ)*x 1 + (5457111137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829511083/5000000000 : ℝ)^4831 ≤ (5116576130191/50000000000000 : ℝ)^3807 := by
    have hnat : (829511083 : ℕ)^4831*50000000000000^3807 ≤ 5116576130191^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829511083 5000000000 5116576130191 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179951227/10000000000 : ℝ)^4831 ≤ (21699788878899/50000000000000 : ℝ)^3807 := by
    have hnat : (5179951227 : ℕ)^4831*50000000000000^3807 ≤ 21699788878899^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179951227 10000000000 21699788878899 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457111137/10000000000 : ℝ)^4831 ≤ (46367269964183/100000000000000 : ℝ)^3807 := by
    have hnat : (5457111137 : ℕ)^4831*100000000000000^3807 ≤ 46367269964183^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457111137 10000000000 46367269964183 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-829511083/5000000000 : ℝ), (5179951227/10000000000 : ℝ), (5457111137/10000000000 : ℝ)] ![(5116576130191/50000000000000 : ℝ), (21699788878899/50000000000000 : ℝ), (46367269964183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-829511083/5000000000 : ℝ)|^4831 ≤ (5116576130191/50000000000000 : ℝ)^3807
        have hw : |(-829511083/5000000000 : ℝ)|=(829511083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179951227/10000000000 : ℝ)|^4831 ≤ (21699788878899/50000000000000 : ℝ)^3807
        have hw : |(5179951227/10000000000 : ℝ)|=(5179951227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457111137/10000000000 : ℝ)|^4831 ≤ (46367269964183/100000000000000 : ℝ)^3807
        have hw : |(5457111137/10000000000 : ℝ)|=(5457111137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s2_5 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277402749/10000000000 : ℝ)*x 0 + (-1524828447/10000000000 : ℝ)*x 1 + (170534727/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277402749/10000000000 : ℝ)^4831 ≤ (2221914480643/5000000000000 : ℝ)^3807 := by
    have hnat : (5277402749 : ℕ)^4831*5000000000000^3807 ≤ 2221914480643^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277402749 10000000000 2221914480643 5000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1524828447/10000000000 : ℝ)^4831 ≤ (1838887809063/20000000000000 : ℝ)^3807 := by
    have hnat : (1524828447 : ℕ)^4831*20000000000000^3807 ≤ 1838887809063^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524828447 10000000000 1838887809063 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170534727/312500000 : ℝ)^4831 ≤ (11591817833377/25000000000000 : ℝ)^3807 := by
    have hnat : (170534727 : ℕ)^4831*25000000000000^3807 ≤ 11591817833377^3807*312500000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170534727 312500000 11591817833377 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277402749/10000000000 : ℝ), (-1524828447/10000000000 : ℝ), (170534727/312500000 : ℝ)] ![(2221914480643/5000000000000 : ℝ), (1838887809063/20000000000000 : ℝ), (11591817833377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277402749/10000000000 : ℝ)|^4831 ≤ (2221914480643/5000000000000 : ℝ)^3807
        have hw : |(5277402749/10000000000 : ℝ)|=(5277402749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1524828447/10000000000 : ℝ)|^4831 ≤ (1838887809063/20000000000000 : ℝ)^3807
        have hw : |(-1524828447/10000000000 : ℝ)|=(1524828447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170534727/312500000 : ℝ)|^4831 ≤ (11591817833377/25000000000000 : ℝ)^3807
        have hw : |(170534727/312500000 : ℝ)|=(170534727/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s2_6 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277403759/10000000000 : ℝ)*x 0 + (5457110037/10000000000 : ℝ)*x 1 + (-381207191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277403759/10000000000 : ℝ)^4831 ≤ (22219150202563/50000000000000 : ℝ)^3807 := by
    have hnat : (5277403759 : ℕ)^4831*50000000000000^3807 ≤ 22219150202563^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277403759 10000000000 22219150202563 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457110037/10000000000 : ℝ)^4831 ≤ (23183629051943/50000000000000 : ℝ)^3807 := by
    have hnat : (5457110037 : ℕ)^4831*50000000000000^3807 ≤ 23183629051943^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457110037 10000000000 23183629051943 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381207191/2500000000 : ℝ)^4831 ≤ (4597220735453/50000000000000 : ℝ)^3807 := by
    have hnat : (381207191 : ℕ)^4831*50000000000000^3807 ≤ 4597220735453^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381207191 2500000000 4597220735453 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277403759/10000000000 : ℝ), (5457110037/10000000000 : ℝ), (-381207191/2500000000 : ℝ)] ![(22219150202563/50000000000000 : ℝ), (23183629051943/50000000000000 : ℝ), (4597220735453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277403759/10000000000 : ℝ)|^4831 ≤ (22219150202563/50000000000000 : ℝ)^3807
        have hw : |(5277403759/10000000000 : ℝ)|=(5277403759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457110037/10000000000 : ℝ)|^4831 ≤ (23183629051943/50000000000000 : ℝ)^3807
        have hw : |(5457110037/10000000000 : ℝ)|=(5457110037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381207191/2500000000 : ℝ)|^4831 ≤ (4597220735453/50000000000000 : ℝ)^3807
        have hw : |(-381207191/2500000000 : ℝ)|=(381207191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s2_7 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209871431/500000000 : ℝ)*x 0 + (1139271887/2500000000 : ℝ)*x 1 + (1929919223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209871431/500000000 : ℝ)^4831 ≤ (4154168086541/12500000000000 : ℝ)^3807 := by
    have hnat : (209871431 : ℕ)^4831*12500000000000^3807 ≤ 4154168086541^3807*500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209871431 500000000 4154168086541 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139271887/2500000000 : ℝ)^4831 ≤ (3688771182577/10000000000000 : ℝ)^3807 := by
    have hnat : (1139271887 : ℕ)^4831*10000000000000^3807 ≤ 3688771182577^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139271887 2500000000 3688771182577 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929919223/5000000000 : ℝ)^4831 ≤ (29878943464389/100000000000000 : ℝ)^3807 := by
    have hnat : (1929919223 : ℕ)^4831*100000000000000^3807 ≤ 29878943464389^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929919223 5000000000 29878943464389 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209871431/500000000 : ℝ), (1139271887/2500000000 : ℝ), (1929919223/5000000000 : ℝ)] ![(4154168086541/12500000000000 : ℝ), (3688771182577/10000000000000 : ℝ), (29878943464389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209871431/500000000 : ℝ)|^4831 ≤ (4154168086541/12500000000000 : ℝ)^3807
        have hw : |(209871431/500000000 : ℝ)|=(209871431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139271887/2500000000 : ℝ)|^4831 ≤ (3688771182577/10000000000000 : ℝ)^3807
        have hw : |(1139271887/2500000000 : ℝ)|=(1139271887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1929919223/5000000000 : ℝ)|^4831 ≤ (29878943464389/100000000000000 : ℝ)^3807
        have hw : |(1929919223/5000000000 : ℝ)|=(1929919223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1628_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17559/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10447/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8211/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17559/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17559/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17559/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17559/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17559/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17559/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4717/50000 : ℝ) ^ (4827/1024 : ℝ) ≤ (293685502854827/20000000000000000000 : ℝ) := by
    have hpowers : (4717/50000 : ℝ)^4827 ≤ (293685502854827/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4717 : ℕ)^4827*20000000000000000000^1024 ≤ 293685502854827^1024*50000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4717 50000 293685502854827 20000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4717/50000 : ℝ)) (X := (293685502854827/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17559/100000 : ℝ) ^ (4827/1024 : ℝ) ≤ (27458214749350633/100000000000000000000 : ℝ) := by
    have hpowers : (17559/100000 : ℝ)^4827 ≤ (27458214749350633/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17559 : ℕ)^4827*100000000000000000000^1024 ≤ 27458214749350633^1024*100000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17559 100000 27458214749350633 100000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17559/100000 : ℝ)) (X := (27458214749350633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000293685502854827/10000000000000000000 : ℝ) ≤ (10000062301735187/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (10000293685502854827/10000000000000000000 : ℝ)^1024 ≤ (10000062301735187/10000000000000000 : ℝ)^4827 := by
      have hnat : (10000293685502854827 : ℕ)^1024*10000000000000000^4827 ≤ 10000062301735187^4827*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000293685502854827 10000000000000000000 10000062301735187 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062301735187/10000000000000000 : ℝ)) (X := (10000293685502854827/10000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1562951978785369137/1562500000000000000 : ℝ) ≤ (400024543200281/400000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (1562951978785369137/1562500000000000000 : ℝ)^1024 ≤ (400024543200281/400000000000000 : ℝ)^4827 := by
      have hnat : (1562951978785369137 : ℕ)^1024*400000000000000^4827 ≤ 400024543200281^4827*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562951978785369137 1562500000000000000 400024543200281 400000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400024543200281/400000000000000 : ℝ)) (X := (1562951978785369137/1562500000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027458214749350633/50000000000000000000 : ℝ) ≤ (10001164858278863/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (50027458214749350633/50000000000000000000 : ℝ)^1024 ≤ (10001164858278863/10000000000000000 : ℝ)^4827 := by
      have hnat : (50027458214749350633 : ℕ)^1024*10000000000000000^4827 ≤ 10001164858278863^4827*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027458214749350633 50000000000000000000 10001164858278863 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001164858278863/10000000000000000 : ℝ)) (X := (50027458214749350633/50000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(293685502854827/20000000000000000000 : ℝ) ≤ ((81240104683165354991/81250000000000000000 : ℝ)+2*(275639135919/406250000000000 : ℝ)*(4717/50000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (81240104683165354991/81250000000000000000 : ℝ)+2*(275639135919/406250000000000 : ℝ)*(4717/50000 : ℝ)=(10000062301735187/10000000000000000 : ℝ) by norm_num, show 1+2*(293685502854827/20000000000000000000 : ℝ)=(10000293685502854827/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27458214749350633/100000000000000000000 : ℝ)+(293685502854827/20000000000000000000 : ℝ) ≤ ((81240104683165354991/81250000000000000000 : ℝ)+(275639135919/406250000000000 : ℝ)*((17559/100000 : ℝ)+(4717/50000 : ℝ)))^(4827/1024 : ℝ) := by
    rw [show (81240104683165354991/81250000000000000000 : ℝ)+(275639135919/406250000000000 : ℝ)*((17559/100000 : ℝ)+(4717/50000 : ℝ))=(400024543200281/400000000000000 : ℝ) by norm_num, show 1+(27458214749350633/100000000000000000000 : ℝ)+(293685502854827/20000000000000000000 : ℝ)=(1562951978785369137/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27458214749350633/100000000000000000000 : ℝ) ≤ ((81240104683165354991/81250000000000000000 : ℝ)+2*(275639135919/406250000000000 : ℝ)*(17559/100000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (81240104683165354991/81250000000000000000 : ℝ)+2*(275639135919/406250000000000 : ℝ)*(17559/100000 : ℝ)=(10001164858278863/10000000000000000 : ℝ) by norm_num, show 1+2*(27458214749350633/100000000000000000000 : ℝ)=(50027458214749350633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (81240104683165354991/81250000000000000000 : ℝ)*(X 1 0+X 2 0)+(275639135919/406250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (4717/50000 : ℝ)) (hi := (17559/100000 : ℝ)) (c := (81240104683165354991/81250000000000000000 : ℝ)) (alpha := (275639135919/406250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (81240104683165354991/81250000000000000000 : ℝ)*(X 0 1+X 2 1)+(275639135919/406250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (4717/50000 : ℝ)) (hi := (17559/100000 : ℝ)) (c := (81240104683165354991/81250000000000000000 : ℝ)) (alpha := (275639135919/406250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (81240104683165354991/81250000000000000000 : ℝ)*(X 0 2+X 1 2)+(275639135919/406250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (4717/50000 : ℝ)) (hi := (17559/100000 : ℝ)) (c := (81240104683165354991/81250000000000000000 : ℝ)) (alpha := (275639135919/406250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-829473711/5000000000 : ℝ)*X 0 0+(218372837/400000000 : ℝ)*X 0 1+(258888251/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352406979/10000000000 : ℝ)*X 1 0+(-1804174631/10000000000 : ℝ)*X 1 1+(1035553013/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352407057/10000000000 : ℝ)*X 2 0+(2588882469/5000000000 : ℝ)*X 2 1+(-360834939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197239977/10000000000 : ℝ)*X 0 0+(3854280159/10000000000 : ℝ)*X 0 1+(7300137/16000000 : ℝ)*X 0 2+(4197239977/10000000000 : ℝ)*X 1 0+(3854280159/10000000000 : ℝ)*X 1 1+(7300137/16000000 : ℝ)*X 1 2+(4197239977/10000000000 : ℝ)*X 2 0+(3854280159/10000000000 : ℝ)*X 2 1+(7300137/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-829511083/5000000000 : ℝ)*X 0 0+(5179951227/10000000000 : ℝ)*X 0 1+(5457111137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277402749/10000000000 : ℝ)*X 1 0+(-1524828447/10000000000 : ℝ)*X 1 1+(170534727/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277403759/10000000000 : ℝ)*X 2 0+(5457110037/10000000000 : ℝ)*X 2 1+(-381207191/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((209871431/500000000 : ℝ)*X 0 0+(1139271887/2500000000 : ℝ)*X 0 1+(1929919223/5000000000 : ℝ)*X 0 2+(209871431/500000000 : ℝ)*X 1 0+(1139271887/2500000000 : ℝ)*X 1 1+(1929919223/5000000000 : ℝ)*X 1 2+(209871431/500000000 : ℝ)*X 2 0+(1139271887/2500000000 : ℝ)*X 2 1+(1929919223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2713755884443716399989433171/1015625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188522007/50000000000000 : ℝ)*(base19) + (382852679/100000000000000 : ℝ)*(base23) + (6148559/25000000000000 : ℝ)*(lower2) + (42578479/50000000000000 : ℝ)*(upper3) + (10354111/100000000000000 : ℝ)*(upper5) + (1240881426744327/50000000000000 : ℝ)*(major0) + (1240881426744327/50000000000000 : ℝ)*(major1) + (1240881426744327/50000000000000 : ℝ)*(major2) + (1775848818743777/50000000000000 : ℝ)*(sp0) + (110990665403209/3125000000000 : ℝ)*(sp1) + (3551701287094023/100000000000000 : ℝ)*(sp2) + (1411821706448593/100000000000000 : ℝ)*(sp3) + (4032459147/100000000000000 : ℝ)*(sp4) + (448303029/20000000000000 : ℝ)*(sp7) + (705911973981869/50000000000000 : ℝ)*(f.failure) + (1775850834973351/50000000000000 : ℝ)*(f.sum) + (215974110908323/40625000000000000000000000000 : ℝ)*base66 + (8554089234222013943/4062500000000000000000000000000000 : ℝ)*base68 + (12682020352027986057/4062500000000000000000000000000000 : ℝ)*base69 + (53870221487659513943/4062500000000000000000000000000000 : ℝ)*base72 + (115064448079177/40625000000000000000000000000 : ℝ)*base73 + (36040409495784513943/4062500000000000000000000000000000 : ℝ)*base76 + (59186655821097013943/4062500000000000000000000000000000 : ℝ)*base78 + (48730080426409513943/4062500000000000000000000000000000 : ℝ)*base80 + (107130886566151/20312500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (23413171/5000000000000000000000 : ℝ)*base89 + (23413171/5000000000000000000000 : ℝ)*base91 + (23413171/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14566969554134019686079746769/4062500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229755591/100000000000000 : ℝ)*(base19) + (572945231/50000000000000 : ℝ)*(base23) + (117344989/100000000000000 : ℝ)*(lower4) + (27739923/100000000000000 : ℝ)*(lower5) + (2521119402981547/100000000000000 : ℝ)*(major0) + (2521119402981547/100000000000000 : ℝ)*(major1) + (2521119402981547/100000000000000 : ℝ)*(major2) + (2688372593/50000000000000 : ℝ)*(sp1) + (44855279/800000000000 : ℝ)*(sp2) + (294955133/12500000000000 : ℝ)*(sp3) + (3608025605281251/100000000000000 : ℝ)*(sp4) + (1804009999390237/50000000000000 : ℝ)*(sp5) + (1804009426240457/50000000000000 : ℝ)*(sp6) + (717105360758459/50000000000000 : ℝ)*(sp7) + (717106540578991/50000000000000 : ℝ)*(f.failure) + (3608025605281251/100000000000000 : ℝ)*(f.sum) + (34777919626159/10156250000000000000000000000 : ℝ)*base65 + (34710759779290951077/8125000000000000000000000000000000 : ℝ)*base67 + (7828420545540951077/8125000000000000000000000000000000 : ℝ)*base69 + (12109824352415951077/8125000000000000000000000000000000 : ℝ)*base71 + (80031666342943/20312500000000000000000000000 : ℝ)*base73 + (53572154396334048923/8125000000000000000000000000000000 : ℝ)*base76 + (44327786430709048923/8125000000000000000000000000000000 : ℝ)*base78 + (70105278102415951077/8125000000000000000000000000000000 : ℝ)*base79 + (151002129114011/40625000000000000000000000000 : ℝ)*base81 + (43996431/5000000000000000000000 : ℝ)*base90 + (43996431/5000000000000000000000 : ℝ)*base92 + (43996431/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1628_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17559/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8211/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1628_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1628_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8211/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1628_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1628_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1628_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8211/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1628_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
