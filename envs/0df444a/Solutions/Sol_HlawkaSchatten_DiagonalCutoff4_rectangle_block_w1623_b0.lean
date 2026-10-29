-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1623_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:24.387965+00:00
-- url     : https://prove2.me/submissions/a999da12-2cf2-4aef-bfc1-bc9dc8af6bd7

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
theorem support_rectangle_w1623_s0_0 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1541240209/10000000000 : ℝ)*x 0 + (11366739/19531250 : ℝ)*x 1 + (980519341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1541240209/10000000000 : ℝ)^4811 ≤ (1859094615957/20000000000000 : ℝ)^3787 := by
    have hnat : (1541240209 : ℕ)^4811*20000000000000^3787 ≤ 1859094615957^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541240209 10000000000 1859094615957 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11366739/19531250 : ℝ)^4811 ≤ (25136609177013/50000000000000 : ℝ)^3787 := by
    have hnat : (11366739 : ℕ)^4811*50000000000000^3787 ≤ 25136609177013^3787*19531250^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11366739 19531250 25136609177013 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980519341/2000000000 : ℝ)^4811 ≤ (20215654278437/50000000000000 : ℝ)^3787 := by
    have hnat : (980519341 : ℕ)^4811*50000000000000^3787 ≤ 20215654278437^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980519341 2000000000 20215654278437 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1541240209/10000000000 : ℝ), (11366739/19531250 : ℝ), (980519341/2000000000 : ℝ)] ![(1859094615957/20000000000000 : ℝ), (25136609177013/50000000000000 : ℝ), (20215654278437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1541240209/10000000000 : ℝ)|^4811 ≤ (1859094615957/20000000000000 : ℝ)^3787
        have hw : |(-1541240209/10000000000 : ℝ)|=(1541240209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11366739/19531250 : ℝ)|^4811 ≤ (25136609177013/50000000000000 : ℝ)^3787
        have hw : |(11366739/19531250 : ℝ)|=(11366739/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(980519341/2000000000 : ℝ)|^4811 ≤ (20215654278437/50000000000000 : ℝ)^3787
        have hw : |(980519341/2000000000 : ℝ)|=(980519341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s0_1 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2724195149/5000000000 : ℝ)*x 0 + (-409517693/2000000000 : ℝ)*x 1 + (2451298651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2724195149/5000000000 : ℝ)^4811 ≤ (2311668066901/5000000000000 : ℝ)^3787 := by
    have hnat : (2724195149 : ℕ)^4811*5000000000000^3787 ≤ 2311668066901^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724195149 5000000000 2311668066901 5000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409517693/2000000000 : ℝ)^4811 ≤ (13335323831111/100000000000000 : ℝ)^3787 := by
    have hnat : (409517693 : ℕ)^4811*100000000000000^3787 ≤ 13335323831111^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409517693 2000000000 13335323831111 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2451298651/5000000000 : ℝ)^4811 ≤ (40431314811567/100000000000000 : ℝ)^3787 := by
    have hnat : (2451298651 : ℕ)^4811*100000000000000^3787 ≤ 40431314811567^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451298651 5000000000 40431314811567 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2724195149/5000000000 : ℝ), (-409517693/2000000000 : ℝ), (2451298651/5000000000 : ℝ)] ![(2311668066901/5000000000000 : ℝ), (13335323831111/100000000000000 : ℝ), (40431314811567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2724195149/5000000000 : ℝ)|^4811 ≤ (2311668066901/5000000000000 : ℝ)^3787
        have hw : |(2724195149/5000000000 : ℝ)|=(2724195149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409517693/2000000000 : ℝ)|^4811 ≤ (13335323831111/100000000000000 : ℝ)^3787
        have hw : |(-409517693/2000000000 : ℝ)|=(409517693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2451298651/5000000000 : ℝ)|^4811 ≤ (40431314811567/100000000000000 : ℝ)^3787
        have hw : |(2451298651/5000000000 : ℝ)|=(2451298651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s0_2 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1362097507/2500000000 : ℝ)*x 0 + (612824629/1250000000 : ℝ)*x 1 + (-51189729/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362097507/2500000000 : ℝ)^4811 ≤ (46233358427363/100000000000000 : ℝ)^3787 := by
    have hnat : (1362097507 : ℕ)^4811*100000000000000^3787 ≤ 46233358427363^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362097507 2500000000 46233358427363 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (612824629/1250000000 : ℝ)^4811 ≤ (40431311982811/100000000000000 : ℝ)^3787 := by
    have hnat : (612824629 : ℕ)^4811*100000000000000^3787 ≤ 40431311982811^3787*1250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612824629 1250000000 40431311982811 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51189729/250000000 : ℝ)^4811 ≤ (3333832395337/25000000000000 : ℝ)^3787 := by
    have hnat : (51189729 : ℕ)^4811*25000000000000^3787 ≤ 3333832395337^3787*250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51189729 250000000 3333832395337 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1362097507/2500000000 : ℝ), (612824629/1250000000 : ℝ), (-51189729/250000000 : ℝ)] ![(46233358427363/100000000000000 : ℝ), (40431311982811/100000000000000 : ℝ), (3333832395337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1362097507/2500000000 : ℝ)|^4811 ≤ (46233358427363/100000000000000 : ℝ)^3787
        have hw : |(1362097507/2500000000 : ℝ)|=(1362097507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(612824629/1250000000 : ℝ)|^4811 ≤ (40431311982811/100000000000000 : ℝ)^3787
        have hw : |(612824629/1250000000 : ℝ)|=(612824629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51189729/250000000 : ℝ)|^4811 ≤ (3333832395337/25000000000000 : ℝ)^3787
        have hw : |(-51189729/250000000 : ℝ)|=(51189729/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s0_3 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025862693/2500000000 : ℝ)*x 0 + (3076612281/10000000000 : ℝ)*x 1 + (1342262741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025862693/2500000000 : ℝ)^4811 ≤ (4031394344139/12500000000000 : ℝ)^3787 := by
    have hnat : (1025862693 : ℕ)^4811*12500000000000^3787 ≤ 4031394344139^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025862693 2500000000 4031394344139 12500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3076612281/10000000000 : ℝ)^4811 ≤ (22369088872751/100000000000000 : ℝ)^3787 := by
    have hnat : (3076612281 : ℕ)^4811*100000000000000^3787 ≤ 22369088872751^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3076612281 10000000000 22369088872751 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1342262741/2500000000 : ℝ)^4811 ≤ (45379756360671/100000000000000 : ℝ)^3787 := by
    have hnat : (1342262741 : ℕ)^4811*100000000000000^3787 ≤ 45379756360671^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342262741 2500000000 45379756360671 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025862693/2500000000 : ℝ), (3076612281/10000000000 : ℝ), (1342262741/2500000000 : ℝ)] ![(4031394344139/12500000000000 : ℝ), (22369088872751/100000000000000 : ℝ), (45379756360671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025862693/2500000000 : ℝ)|^4811 ≤ (4031394344139/12500000000000 : ℝ)^3787
        have hw : |(1025862693/2500000000 : ℝ)|=(1025862693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3076612281/10000000000 : ℝ)|^4811 ≤ (22369088872751/100000000000000 : ℝ)^3787
        have hw : |(3076612281/10000000000 : ℝ)|=(3076612281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1342262741/2500000000 : ℝ)|^4811 ≤ (45379756360671/100000000000000 : ℝ)^3787
        have hw : |(1342262741/2500000000 : ℝ)|=(1342262741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s0_4 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-771931081/5000000000 : ℝ)*x 0 + (4925666887/10000000000 : ℝ)*x 1 + (5795887287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (771931081/5000000000 : ℝ)^4811 ≤ (1164445882419/12500000000000 : ℝ)^3787 := by
    have hnat : (771931081 : ℕ)^4811*12500000000000^3787 ≤ 1164445882419^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771931081 5000000000 1164445882419 12500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925666887/10000000000 : ℝ)^4811 ≤ (813463310447/2000000000000 : ℝ)^3787 := by
    have hnat : (4925666887 : ℕ)^4811*2000000000000^3787 ≤ 813463310447^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925666887 10000000000 813463310447 2000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5795887287/10000000000 : ℝ)^4811 ≤ (25005633702627/50000000000000 : ℝ)^3787 := by
    have hnat : (5795887287 : ℕ)^4811*50000000000000^3787 ≤ 25005633702627^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5795887287 10000000000 25005633702627 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-771931081/5000000000 : ℝ), (4925666887/10000000000 : ℝ), (5795887287/10000000000 : ℝ)] ![(1164445882419/12500000000000 : ℝ), (813463310447/2000000000000 : ℝ), (25005633702627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-771931081/5000000000 : ℝ)|^4811 ≤ (1164445882419/12500000000000 : ℝ)^3787
        have hw : |(-771931081/5000000000 : ℝ)|=(771931081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4925666887/10000000000 : ℝ)|^4811 ≤ (813463310447/2000000000000 : ℝ)^3787
        have hw : |(4925666887/10000000000 : ℝ)|=(4925666887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5795887287/10000000000 : ℝ)|^4811 ≤ (25005633702627/50000000000000 : ℝ)^3787
        have hw : |(5795887287/10000000000 : ℝ)|=(5795887287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s0_5 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197942191/10000000000 : ℝ)*x 0 + (-1154298541/10000000000 : ℝ)*x 1 + (1159177457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197942191/10000000000 : ℝ)^4811 ≤ (43550448122073/100000000000000 : ℝ)^3787 := by
    have hnat : (5197942191 : ℕ)^4811*100000000000000^3787 ≤ 43550448122073^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197942191 10000000000 43550448122073 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1154298541/10000000000 : ℝ)^4811 ≤ (6438284476021/100000000000000 : ℝ)^3787 := by
    have hnat : (1154298541 : ℕ)^4811*100000000000000^3787 ≤ 6438284476021^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154298541 10000000000 6438284476021 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159177457/2000000000 : ℝ)^4811 ≤ (5001126738333/10000000000000 : ℝ)^3787 := by
    have hnat : (1159177457 : ℕ)^4811*10000000000000^3787 ≤ 5001126738333^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159177457 2000000000 5001126738333 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197942191/10000000000 : ℝ), (-1154298541/10000000000 : ℝ), (1159177457/2000000000 : ℝ)] ![(43550448122073/100000000000000 : ℝ), (6438284476021/100000000000000 : ℝ), (5001126738333/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197942191/10000000000 : ℝ)|^4811 ≤ (43550448122073/100000000000000 : ℝ)^3787
        have hw : |(5197942191/10000000000 : ℝ)|=(5197942191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1154298541/10000000000 : ℝ)|^4811 ≤ (6438284476021/100000000000000 : ℝ)^3787
        have hw : |(-1154298541/10000000000 : ℝ)|=(1154298541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1159177457/2000000000 : ℝ)|^4811 ≤ (5001126738333/10000000000000 : ℝ)^3787
        have hw : |(1159177457/2000000000 : ℝ)|=(1159177457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s0_6 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299485539/2500000000 : ℝ)*x 0 + (289794381/500000000 : ℝ)*x 1 + (-1154298077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299485539/2500000000 : ℝ)^4811 ≤ (1360951492173/3125000000000 : ℝ)^3787 := by
    have hnat : (1299485539 : ℕ)^4811*3125000000000^3787 ≤ 1360951492173^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299485539 2500000000 1360951492173 3125000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289794381/500000000 : ℝ)^4811 ≤ (10002254211117/20000000000000 : ℝ)^3787 := by
    have hnat : (289794381 : ℕ)^4811*20000000000000^3787 ≤ 10002254211117^3787*500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289794381 500000000 10002254211117 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154298077/10000000000 : ℝ)^4811 ≤ (3219140594093/50000000000000 : ℝ)^3787 := by
    have hnat : (1154298077 : ℕ)^4811*50000000000000^3787 ≤ 3219140594093^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154298077 10000000000 3219140594093 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299485539/2500000000 : ℝ), (289794381/500000000 : ℝ), (-1154298077/10000000000 : ℝ)] ![(1360951492173/3125000000000 : ℝ), (10002254211117/20000000000000 : ℝ), (3219140594093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299485539/2500000000 : ℝ)|^4811 ≤ (1360951492173/3125000000000 : ℝ)^3787
        have hw : |(1299485539/2500000000 : ℝ)|=(1299485539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(289794381/500000000 : ℝ)|^4811 ≤ (10002254211117/20000000000000 : ℝ)^3787
        have hw : |(289794381/500000000 : ℝ)|=(289794381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1154298077/10000000000 : ℝ)|^4811 ≤ (3219140594093/50000000000000 : ℝ)^3787
        have hw : |(-1154298077/10000000000 : ℝ)|=(1154298077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s0_7 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4110004659/10000000000 : ℝ)*x 0 + (331961611/625000000 : ℝ)*x 1 + (313630781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4110004659/10000000000 : ℝ)^4811 ≤ (16158303817673/50000000000000 : ℝ)^3787 := by
    have hnat : (4110004659 : ℕ)^4811*50000000000000^3787 ≤ 16158303817673^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110004659 10000000000 16158303817673 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331961611/625000000 : ℝ)^4811 ≤ (44761475715963/100000000000000 : ℝ)^3787 := by
    have hnat : (331961611 : ℕ)^4811*100000000000000^3787 ≤ 44761475715963^3787*625000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331961611 625000000 44761475715963 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313630781/1000000000 : ℝ)^4811 ≤ (22921916637961/100000000000000 : ℝ)^3787 := by
    have hnat : (313630781 : ℕ)^4811*100000000000000^3787 ≤ 22921916637961^3787*1000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313630781 1000000000 22921916637961 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4110004659/10000000000 : ℝ), (331961611/625000000 : ℝ), (313630781/1000000000 : ℝ)] ![(16158303817673/50000000000000 : ℝ), (44761475715963/100000000000000 : ℝ), (22921916637961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4110004659/10000000000 : ℝ)|^4811 ≤ (16158303817673/50000000000000 : ℝ)^3787
        have hw : |(4110004659/10000000000 : ℝ)|=(4110004659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(331961611/625000000 : ℝ)|^4811 ≤ (44761475715963/100000000000000 : ℝ)^3787
        have hw : |(331961611/625000000 : ℝ)|=(331961611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313630781/1000000000 : ℝ)|^4811 ≤ (22921916637961/100000000000000 : ℝ)^3787
        have hw : |(313630781/1000000000 : ℝ)|=(313630781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1623_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (43/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23947/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4807/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4807 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4807*1^1024 ≤ 0^1024*1^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4807/1024 : ℝ) ≤ (338747364474753147/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4807 ≤ (338747364474753147/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4807*25000000000000000000^1024 ≤ 338747364474753147^1024*5^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 338747364474753147 25000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (338747364474753147/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4807 := by
      have hnat : (1 : ℕ)^1024*1^4807 ≤ 1^4807*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25338747364474753147/25000000000000000000 : ℝ) ≤ (5014355840766821/5000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (25338747364474753147/25000000000000000000 : ℝ)^1024 ≤ (5014355840766821/5000000000000000 : ℝ)^4807 := by
      have hnat : (25338747364474753147 : ℕ)^1024*5000000000000000^4807 ≤ 5014355840766821^4807*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25338747364474753147 25000000000000000000 5014355840766821 5000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014355840766821/5000000000000000 : ℝ)) (X := (25338747364474753147/25000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12838747364474753147/12500000000000000000 : ℝ) ≤ (2514355840766821/2500000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (12838747364474753147/12500000000000000000 : ℝ)^1024 ≤ (2514355840766821/2500000000000000 : ℝ)^4807 := by
      have hnat : (12838747364474753147 : ℕ)^1024*2500000000000000^4807 ≤ 2514355840766821^4807*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12838747364474753147 12500000000000000000 2514355840766821 2500000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514355840766821/2500000000000000 : ℝ)) (X := (12838747364474753147/12500000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14355840766821/2000000000000000 : ℝ)*(0 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14355840766821/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(338747364474753147/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14355840766821/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4807/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14355840766821/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014355840766821/5000000000000000 : ℝ) by norm_num, show 1+(338747364474753147/25000000000000000000 : ℝ)+(0 : ℝ)=(25338747364474753147/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(338747364474753147/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14355840766821/2000000000000000 : ℝ)*(2/5 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14355840766821/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514355840766821/2500000000000000 : ℝ) by norm_num, show 1+2*(338747364474753147/25000000000000000000 : ℝ)=(12838747364474753147/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14355840766821/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14355840766821/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14355840766821/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14355840766821/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14355840766821/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14355840766821/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1541240209/10000000000 : ℝ)*X 0 0+(11366739/19531250 : ℝ)*X 0 1+(980519341/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2724195149/5000000000 : ℝ)*X 1 0+(-409517693/2000000000 : ℝ)*X 1 1+(2451298651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1362097507/2500000000 : ℝ)*X 2 0+(612824629/1250000000 : ℝ)*X 2 1+(-51189729/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1025862693/2500000000 : ℝ)*X 0 0+(3076612281/10000000000 : ℝ)*X 0 1+(1342262741/2500000000 : ℝ)*X 0 2+(1025862693/2500000000 : ℝ)*X 1 0+(3076612281/10000000000 : ℝ)*X 1 1+(1342262741/2500000000 : ℝ)*X 1 2+(1025862693/2500000000 : ℝ)*X 2 0+(3076612281/10000000000 : ℝ)*X 2 1+(1342262741/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-771931081/5000000000 : ℝ)*X 0 0+(4925666887/10000000000 : ℝ)*X 0 1+(5795887287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197942191/10000000000 : ℝ)*X 1 0+(-1154298541/10000000000 : ℝ)*X 1 1+(1159177457/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299485539/2500000000 : ℝ)*X 2 0+(289794381/500000000 : ℝ)*X 2 1+(-1154298077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4110004659/10000000000 : ℝ)*X 0 0+(331961611/625000000 : ℝ)*X 0 1+(313630781/1000000000 : ℝ)*X 0 2+(4110004659/10000000000 : ℝ)*X 1 0+(331961611/625000000 : ℝ)*X 1 1+(313630781/1000000000 : ℝ)*X 1 2+(4110004659/10000000000 : ℝ)*X 2 0+(331961611/625000000 : ℝ)*X 2 1+(313630781/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5532352447966691481/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111019711/10000000000000 : ℝ)*(base19) + (978211787/100000000000000 : ℝ)*(base23) + (306632357/100000000000000 : ℝ)*(upper3) + (21236133/50000000000000 : ℝ)*(upper4) + (2415971/100000000000000 : ℝ)*(upper5) + (76326825006961/10000000000000 : ℝ)*(major0) + (76326825006961/10000000000000 : ℝ)*(major1) + (76326825006961/10000000000000 : ℝ)*(major2) + (1090311764589619/100000000000000 : ℝ)*(sp0) + (545157142796089/50000000000000 : ℝ)*(sp1) + (1090314417577501/100000000000000 : ℝ)*(sp2) + (218109147680321/50000000000000 : ℝ)*(sp3) + (3631199669/100000000000000 : ℝ)*(sp4) + (2624577539/100000000000000 : ℝ)*(sp7) + (436220919938181/100000000000000 : ℝ)*(f.failure) + (136289424473661/12500000000000 : ℝ)*(f.sum) + (55208352080981/10000000000000000000000000000 : ℝ)*base65 + (120123094379019/20000000000000000000000000000 : ℝ)*base68 + (1753865320981/20000000000000000000000000000 : ℝ)*base69 + (5318274539019/20000000000000000000000000000 : ℝ)*base72 + (14598126119019/10000000000000000000000000000 : ℝ)*base74 + (13098058160981/20000000000000000000000000000 : ℝ)*base75 + (16631694219019/20000000000000000000000000000 : ℝ)*base78 + (100469231119019/20000000000000000000000000000 : ℝ)*base80 + (36615409660981/10000000000000000000000000000 : ℝ)*base81 + (7665073/10000000000000000000000 : ℝ)*base90 + (7665073/10000000000000000000000 : ℝ)*base92 + (7665073/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (970636903142013296817483/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2133746571/100000000000000 : ℝ)*(base19) + (436804127/20000000000000 : ℝ)*(base23) + (36709541/100000000000000 : ℝ)*(base39) + (306728323/100000000000000 : ℝ)*(upper3) + (168323189/50000000000000 : ℝ)*(upper5) + (100555498590093/12500000000000 : ℝ)*(major0) + (100555498590093/12500000000000 : ℝ)*(major1) + (804443952011203/100000000000000 : ℝ)*(major2) + (3302919379/50000000000000 : ℝ)*(sp1) + (70584829/1000000000000 : ℝ)*(sp2) + (574567027548941/50000000000000 : ℝ)*(sp4) + (1149125315512553/100000000000000 : ℝ)*(sp5) + (1149124849303887/100000000000000 : ℝ)*(sp6) + (229876781044213/50000000000000 : ℝ)*(sp7) + (229876781044213/50000000000000 : ℝ)*(f.failure) + (574567045903711/50000000000000 : ℝ)*(f.sum) + (307146677669513/200000000000000000000000000000 : ℝ)*base66 + (1499828320695663/200000000000000000000000000000 : ℝ)*base67 + (86293356145647/25000000000000000000000000000 : ℝ)*base70 + (644526654495663/200000000000000000000000000000 : ℝ)*base71 + (56657105730487/200000000000000000000000000000 : ℝ)*base73 + (80893190820647/25000000000000000000000000000 : ℝ)*base76 + (86416016054353/25000000000000000000000000000 : ℝ)*base77 + (244813465804353/25000000000000000000000000000 : ℝ)*base79 + (40526498308147/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2368671/5000000000000000000000 : ℝ)*base89 + (2368671/5000000000000000000000 : ℝ)*base91 + (2368671/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1623_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23947/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1623_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1623_s1_0 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-66349109/400000000 : ℝ)*x 0 + (1379535649/2500000000 : ℝ)*x 1 + (1282030097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66349109/400000000 : ℝ)^4811 ≤ (5102385704383/50000000000000 : ℝ)^3787 := by
    have hnat : (66349109 : ℕ)^4811*50000000000000^3787 ≤ 5102385704383^3787*400000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66349109 400000000 5102385704383 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379535649/2500000000 : ℝ)^4811 ≤ (46986603402743/100000000000000 : ℝ)^3787 := by
    have hnat : (1379535649 : ℕ)^4811*100000000000000^3787 ≤ 46986603402743^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379535649 2500000000 46986603402743 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282030097/2500000000 : ℝ)^4811 ≤ (42808625166377/100000000000000 : ℝ)^3787 := by
    have hnat : (1282030097 : ℕ)^4811*100000000000000^3787 ≤ 42808625166377^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282030097 2500000000 42808625166377 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66349109/400000000 : ℝ), (1379535649/2500000000 : ℝ), (1282030097/2500000000 : ℝ)] ![(5102385704383/50000000000000 : ℝ), (46986603402743/100000000000000 : ℝ), (42808625166377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66349109/400000000 : ℝ)|^4811 ≤ (5102385704383/50000000000000 : ℝ)^3787
        have hw : |(-66349109/400000000 : ℝ)|=(66349109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379535649/2500000000 : ℝ)|^4811 ≤ (46986603402743/100000000000000 : ℝ)^3787
        have hw : |(1379535649/2500000000 : ℝ)|=(1379535649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1282030097/2500000000 : ℝ)|^4811 ≤ (42808625166377/100000000000000 : ℝ)^3787
        have hw : |(1282030097/2500000000 : ℝ)|=(1282030097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s1_1 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684075553/5000000000 : ℝ)*x 0 + (-1862275059/10000000000 : ℝ)*x 1 + (5128120181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684075553/5000000000 : ℝ)^4811 ≤ (45370094320787/100000000000000 : ℝ)^3787 := by
    have hnat : (2684075553 : ℕ)^4811*100000000000000^3787 ≤ 45370094320787^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684075553 5000000000 45370094320787 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862275059/10000000000 : ℝ)^4811 ≤ (369415083971/3125000000000 : ℝ)^3787 := by
    have hnat : (1862275059 : ℕ)^4811*3125000000000^3787 ≤ 369415083971^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862275059 10000000000 369415083971 3125000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128120181/10000000000 : ℝ)^4811 ≤ (4280862297113/10000000000000 : ℝ)^3787 := by
    have hnat : (5128120181 : ℕ)^4811*10000000000000^3787 ≤ 4280862297113^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128120181 10000000000 4280862297113 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684075553/5000000000 : ℝ), (-1862275059/10000000000 : ℝ), (5128120181/10000000000 : ℝ)] ![(45370094320787/100000000000000 : ℝ), (369415083971/3125000000000 : ℝ), (4280862297113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684075553/5000000000 : ℝ)|^4811 ≤ (45370094320787/100000000000000 : ℝ)^3787
        have hw : |(2684075553/5000000000 : ℝ)|=(2684075553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1862275059/10000000000 : ℝ)|^4811 ≤ (369415083971/3125000000000 : ℝ)^3787
        have hw : |(-1862275059/10000000000 : ℝ)|=(1862275059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128120181/10000000000 : ℝ)|^4811 ≤ (4280862297113/10000000000000 : ℝ)^3787
        have hw : |(5128120181/10000000000 : ℝ)|=(5128120181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s1_2 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342037861/2500000000 : ℝ)*x 0 + (2564059857/5000000000 : ℝ)*x 1 + (-232784403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342037861/2500000000 : ℝ)^4811 ≤ (4537009794991/10000000000000 : ℝ)^3787 := by
    have hnat : (1342037861 : ℕ)^4811*10000000000000^3787 ≤ 4537009794991^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342037861 2500000000 4537009794991 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564059857/5000000000 : ℝ)^4811 ≤ (42808618018567/100000000000000 : ℝ)^3787 := by
    have hnat : (2564059857 : ℕ)^4811*100000000000000^3787 ≤ 42808618018567^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564059857 5000000000 42808618018567 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232784403/1250000000 : ℝ)^4811 ≤ (23088445347/195312500000 : ℝ)^3787 := by
    have hnat : (232784403 : ℕ)^4811*195312500000^3787 ≤ 23088445347^3787*1250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232784403 1250000000 23088445347 195312500000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342037861/2500000000 : ℝ), (2564059857/5000000000 : ℝ), (-232784403/1250000000 : ℝ)] ![(4537009794991/10000000000000 : ℝ), (42808618018567/100000000000000 : ℝ), (23088445347/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342037861/2500000000 : ℝ)|^4811 ≤ (4537009794991/10000000000000 : ℝ)^3787
        have hw : |(1342037861/2500000000 : ℝ)|=(1342037861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564059857/5000000000 : ℝ)|^4811 ≤ (42808618018567/100000000000000 : ℝ)^3787
        have hw : |(2564059857/5000000000 : ℝ)|=(2564059857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232784403/1250000000 : ℝ)|^4811 ≤ (23088445347/195312500000 : ℝ)^3787
        have hw : |(-232784403/1250000000 : ℝ)|=(232784403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s1_3 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838427091/2000000000 : ℝ)*x 0 + (3726046829/10000000000 : ℝ)*x 1 + (2350446071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838427091/2000000000 : ℝ)^4811 ≤ (2071201299499/6250000000000 : ℝ)^3787 := by
    have hnat : (838427091 : ℕ)^4811*6250000000000^3787 ≤ 2071201299499^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838427091 2000000000 2071201299499 6250000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3726046829/10000000000 : ℝ)^4811 ≤ (28530829271293/100000000000000 : ℝ)^3787 := by
    have hnat : (3726046829 : ℕ)^4811*100000000000000^3787 ≤ 28530829271293^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726046829 10000000000 28530829271293 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2350446071/5000000000 : ℝ)^4811 ≤ (766598998419/2000000000000 : ℝ)^3787 := by
    have hnat : (2350446071 : ℕ)^4811*2000000000000^3787 ≤ 766598998419^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350446071 5000000000 766598998419 2000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838427091/2000000000 : ℝ), (3726046829/10000000000 : ℝ), (2350446071/5000000000 : ℝ)] ![(2071201299499/6250000000000 : ℝ), (28530829271293/100000000000000 : ℝ), (766598998419/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838427091/2000000000 : ℝ)|^4811 ≤ (2071201299499/6250000000000 : ℝ)^3787
        have hw : |(838427091/2000000000 : ℝ)|=(838427091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3726046829/10000000000 : ℝ)|^4811 ≤ (28530829271293/100000000000000 : ℝ)^3787
        have hw : |(3726046829/10000000000 : ℝ)|=(3726046829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2350446071/5000000000 : ℝ)|^4811 ≤ (766598998419/2000000000000 : ℝ)^3787
        have hw : |(2350446071/5000000000 : ℝ)|=(2350446071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s1_4 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1658925487/10000000000 : ℝ)*x 0 + (5132263353/10000000000 : ℝ)*x 1 + (689242147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1658925487/10000000000 : ℝ)^4811 ≤ (5103158541691/50000000000000 : ℝ)^3787 := by
    have hnat : (1658925487 : ℕ)^4811*50000000000000^3787 ≤ 5103158541691^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658925487 10000000000 5103158541691 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132263353/10000000000 : ℝ)^4811 ≤ (21426283177921/50000000000000 : ℝ)^3787 := by
    have hnat : (5132263353 : ℕ)^4811*50000000000000^3787 ≤ 21426283177921^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132263353 10000000000 21426283177921 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689242147/1250000000 : ℝ)^4811 ≤ (23470558279581/50000000000000 : ℝ)^3787 := by
    have hnat : (689242147 : ℕ)^4811*50000000000000^3787 ≤ 23470558279581^3787*1250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689242147 1250000000 23470558279581 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1658925487/10000000000 : ℝ), (5132263353/10000000000 : ℝ), (689242147/1250000000 : ℝ)] ![(5103158541691/50000000000000 : ℝ), (21426283177921/50000000000000 : ℝ), (23470558279581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1658925487/10000000000 : ℝ)|^4811 ≤ (5103158541691/50000000000000 : ℝ)^3787
        have hw : |(-1658925487/10000000000 : ℝ)|=(1658925487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132263353/10000000000 : ℝ)|^4811 ≤ (21426283177921/50000000000000 : ℝ)^3787
        have hw : |(5132263353/10000000000 : ℝ)|=(5132263353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689242147/1250000000 : ℝ)|^4811 ≤ (23470558279581/50000000000000 : ℝ)^3787
        have hw : |(689242147/1250000000 : ℝ)|=(689242147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s1_5 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632100907/5000000000 : ℝ)*x 0 + (-1476457401/10000000000 : ℝ)*x 1 + (1102787503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632100907/5000000000 : ℝ)^4811 ≤ (44256921369819/100000000000000 : ℝ)^3787 := by
    have hnat : (2632100907 : ℕ)^4811*100000000000000^3787 ≤ 44256921369819^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632100907 5000000000 44256921369819 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1476457401/10000000000 : ℝ)^4811 ≤ (8801958391251/100000000000000 : ℝ)^3787 := by
    have hnat : (1476457401 : ℕ)^4811*100000000000000^3787 ≤ 8801958391251^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476457401 10000000000 8801958391251 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102787503/2000000000 : ℝ)^4811 ≤ (4694112022549/10000000000000 : ℝ)^3787 := by
    have hnat : (1102787503 : ℕ)^4811*10000000000000^3787 ≤ 4694112022549^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102787503 2000000000 4694112022549 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632100907/5000000000 : ℝ), (-1476457401/10000000000 : ℝ), (1102787503/2000000000 : ℝ)] ![(44256921369819/100000000000000 : ℝ), (8801958391251/100000000000000 : ℝ), (4694112022549/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632100907/5000000000 : ℝ)|^4811 ≤ (44256921369819/100000000000000 : ℝ)^3787
        have hw : |(2632100907/5000000000 : ℝ)|=(2632100907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1476457401/10000000000 : ℝ)|^4811 ≤ (8801958391251/100000000000000 : ℝ)^3787
        have hw : |(-1476457401/10000000000 : ℝ)|=(1476457401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102787503/2000000000 : ℝ)|^4811 ≤ (4694112022549/10000000000000 : ℝ)^3787
        have hw : |(1102787503/2000000000 : ℝ)|=(1102787503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s1_6 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052840233/2000000000 : ℝ)*x 0 + (5513937757/10000000000 : ℝ)*x 1 + (-147645797/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052840233/2000000000 : ℝ)^4811 ≤ (2212845721911/5000000000000 : ℝ)^3787 := by
    have hnat : (1052840233 : ℕ)^4811*5000000000000^3787 ≤ 2212845721911^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052840233 2000000000 2212845721911 5000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513937757/10000000000 : ℝ)^4811 ≤ (46941122842751/100000000000000 : ℝ)^3787 := by
    have hnat : (5513937757 : ℕ)^4811*100000000000000^3787 ≤ 46941122842751^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513937757 10000000000 46941122842751 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147645797/1000000000 : ℝ)^4811 ≤ (8801962700591/100000000000000 : ℝ)^3787 := by
    have hnat : (147645797 : ℕ)^4811*100000000000000^3787 ≤ 8801962700591^3787*1000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147645797 1000000000 8801962700591 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052840233/2000000000 : ℝ), (5513937757/10000000000 : ℝ), (-147645797/1000000000 : ℝ)] ![(2212845721911/5000000000000 : ℝ), (46941122842751/100000000000000 : ℝ), (8801962700591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052840233/2000000000 : ℝ)|^4811 ≤ (2212845721911/5000000000000 : ℝ)^3787
        have hw : |(1052840233/2000000000 : ℝ)|=(1052840233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513937757/10000000000 : ℝ)|^4811 ≤ (46941122842751/100000000000000 : ℝ)^3787
        have hw : |(5513937757/10000000000 : ℝ)|=(5513937757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147645797/1000000000 : ℝ)|^4811 ≤ (8801962700591/100000000000000 : ℝ)^3787
        have hw : |(-147645797/1000000000 : ℝ)|=(147645797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s1_7 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262039219/625000000 : ℝ)*x 0 + (2345268987/5000000000 : ℝ)*x 1 + (3736557271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262039219/625000000 : ℝ)^4811 ≤ (8286040582903/25000000000000 : ℝ)^3787 := by
    have hnat : (262039219 : ℕ)^4811*25000000000000^3787 ≤ 8286040582903^3787*625000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262039219 625000000 8286040582903 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2345268987/5000000000 : ℝ)^4811 ≤ (38222727944827/100000000000000 : ℝ)^3787 := by
    have hnat : (2345268987 : ℕ)^4811*100000000000000^3787 ≤ 38222727944827^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345268987 5000000000 38222727944827 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3736557271/10000000000 : ℝ)^4811 ≤ (28633109714221/100000000000000 : ℝ)^3787 := by
    have hnat : (3736557271 : ℕ)^4811*100000000000000^3787 ≤ 28633109714221^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736557271 10000000000 28633109714221 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262039219/625000000 : ℝ), (2345268987/5000000000 : ℝ), (3736557271/10000000000 : ℝ)] ![(8286040582903/25000000000000 : ℝ), (38222727944827/100000000000000 : ℝ), (28633109714221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262039219/625000000 : ℝ)|^4811 ≤ (8286040582903/25000000000000 : ℝ)^3787
        have hw : |(262039219/625000000 : ℝ)|=(262039219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2345268987/5000000000 : ℝ)|^4811 ≤ (38222727944827/100000000000000 : ℝ)^3787
        have hw : |(2345268987/5000000000 : ℝ)|=(2345268987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3736557271/10000000000 : ℝ)|^4811 ≤ (28633109714221/100000000000000 : ℝ)^3787
        have hw : |(3736557271/10000000000 : ℝ)|=(3736557271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1623_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (4677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (43/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (43/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (43/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (43/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (43/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (43/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (43/1000 : ℝ) ^ (4807/1024 : ℝ) ≤ (2403930339551/6250000000000000000 : ℝ) := by
    have hpowers : (43/1000 : ℝ)^4807 ≤ (2403930339551/6250000000000000000 : ℝ)^1024 := by
      have hnat : (43 : ℕ)^4807*6250000000000000000^1024 ≤ 2403930339551^1024*1000^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43 1000 2403930339551 6250000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43/1000 : ℝ)) (X := (2403930339551/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23947/100000 : ℝ) ^ (4807/1024 : ℝ) ≤ (121897892523276431/100000000000000000000 : ℝ) := by
    have hpowers : (23947/100000 : ℝ)^4807 ≤ (121897892523276431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23947 : ℕ)^4807*100000000000000000000^1024 ≤ 121897892523276431^1024*100000^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23947 100000 121897892523276431 100000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23947/100000 : ℝ)) (X := (121897892523276431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125002403930339551/3125000000000000000 : ℝ) ≤ (2000000327738571/2000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (3125002403930339551/3125000000000000000 : ℝ)^1024 ≤ (2000000327738571/2000000000000000 : ℝ)^4807 := by
      have hnat : (3125002403930339551 : ℕ)^1024*2000000000000000^4807 ≤ 2000000327738571^4807*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125002403930339551 3125000000000000000 2000000327738571 2000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000327738571/2000000000000000 : ℝ)) (X := (3125002403930339551/3125000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100121936355408709247/100000000000000000000 : ℝ) ≤ (1250324534432897/1250000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (100121936355408709247/100000000000000000000 : ℝ)^1024 ≤ (1250324534432897/1250000000000000 : ℝ)^4807 := by
      have hnat : (100121936355408709247 : ℕ)^1024*1250000000000000^4807 ≤ 1250324534432897^4807*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100121936355408709247 100000000000000000000 1250324534432897 1250000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250324534432897/1250000000000000 : ℝ)) (X := (100121936355408709247/100000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50121897892523276431/50000000000000000000 : ℝ) ≤ (10005190912233497/10000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (50121897892523276431/50000000000000000000 : ℝ)^1024 ≤ (10005190912233497/10000000000000000 : ℝ)^4807 := by
      have hnat : (50121897892523276431 : ℕ)^1024*10000000000000000^4807 ≤ 10005190912233497^4807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50121897892523276431 50000000000000000000 10005190912233497 10000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005190912233497/10000000000000000 : ℝ)) (X := (50121897892523276431/50000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2403930339551/6250000000000000000 : ℝ) ≤ ((39289543663834752317/39294000000000000000 : ℝ)+2*(2594636770321/1964700000000000 : ℝ)*(43/1000 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (39289543663834752317/39294000000000000000 : ℝ)+2*(2594636770321/1964700000000000 : ℝ)*(43/1000 : ℝ)=(2000000327738571/2000000000000000 : ℝ) by norm_num, show 1+2*(2403930339551/6250000000000000000 : ℝ)=(3125002403930339551/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(121897892523276431/100000000000000000000 : ℝ)+(2403930339551/6250000000000000000 : ℝ) ≤ ((39289543663834752317/39294000000000000000 : ℝ)+(2594636770321/1964700000000000 : ℝ)*((23947/100000 : ℝ)+(43/1000 : ℝ)))^(4807/1024 : ℝ) := by
    rw [show (39289543663834752317/39294000000000000000 : ℝ)+(2594636770321/1964700000000000 : ℝ)*((23947/100000 : ℝ)+(43/1000 : ℝ))=(1250324534432897/1250000000000000 : ℝ) by norm_num, show 1+(121897892523276431/100000000000000000000 : ℝ)+(2403930339551/6250000000000000000 : ℝ)=(100121936355408709247/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(121897892523276431/100000000000000000000 : ℝ) ≤ ((39289543663834752317/39294000000000000000 : ℝ)+2*(2594636770321/1964700000000000 : ℝ)*(23947/100000 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (39289543663834752317/39294000000000000000 : ℝ)+2*(2594636770321/1964700000000000 : ℝ)*(23947/100000 : ℝ)=(10005190912233497/10000000000000000 : ℝ) by norm_num, show 1+2*(121897892523276431/100000000000000000000 : ℝ)=(50121897892523276431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39289543663834752317/39294000000000000000 : ℝ)*(X 1 0+X 2 0)+(2594636770321/1964700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (43/1000 : ℝ)) (hi := (23947/100000 : ℝ)) (c := (39289543663834752317/39294000000000000000 : ℝ)) (alpha := (2594636770321/1964700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39289543663834752317/39294000000000000000 : ℝ)*(X 0 1+X 2 1)+(2594636770321/1964700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (43/1000 : ℝ)) (hi := (23947/100000 : ℝ)) (c := (39289543663834752317/39294000000000000000 : ℝ)) (alpha := (2594636770321/1964700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39289543663834752317/39294000000000000000 : ℝ)*(X 0 2+X 1 2)+(2594636770321/1964700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (43/1000 : ℝ)) (hi := (23947/100000 : ℝ)) (c := (39289543663834752317/39294000000000000000 : ℝ)) (alpha := (2594636770321/1964700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66349109/400000000 : ℝ)*X 0 0+(1379535649/2500000000 : ℝ)*X 0 1+(1282030097/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684075553/5000000000 : ℝ)*X 1 0+(-1862275059/10000000000 : ℝ)*X 1 1+(5128120181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342037861/2500000000 : ℝ)*X 2 0+(2564059857/5000000000 : ℝ)*X 2 1+(-232784403/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838427091/2000000000 : ℝ)*X 0 0+(3726046829/10000000000 : ℝ)*X 0 1+(2350446071/5000000000 : ℝ)*X 0 2+(838427091/2000000000 : ℝ)*X 1 0+(3726046829/10000000000 : ℝ)*X 1 1+(2350446071/5000000000 : ℝ)*X 1 2+(838427091/2000000000 : ℝ)*X 2 0+(3726046829/10000000000 : ℝ)*X 2 1+(2350446071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1658925487/10000000000 : ℝ)*X 0 0+(5132263353/10000000000 : ℝ)*X 0 1+(689242147/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632100907/5000000000 : ℝ)*X 1 0+(-1476457401/10000000000 : ℝ)*X 1 1+(1102787503/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052840233/2000000000 : ℝ)*X 2 0+(5513937757/10000000000 : ℝ)*X 2 1+(-147645797/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((262039219/625000000 : ℝ)*X 0 0+(2345268987/5000000000 : ℝ)*X 0 1+(3736557271/10000000000 : ℝ)*X 0 2+(262039219/625000000 : ℝ)*X 1 0+(2345268987/5000000000 : ℝ)*X 1 1+(3736557271/10000000000 : ℝ)*X 1 2+(262039219/625000000 : ℝ)*X 2 0+(2345268987/5000000000 : ℝ)*X 2 1+(3736557271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1192242713076658892551129319/654900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187071513/100000000000000 : ℝ)*(base1) + (36659137/10000000000000 : ℝ)*(base19) + (624436817/100000000000000 : ℝ)*(base23) + (7398123/25000000000000 : ℝ)*(upper3) + (51753633/100000000000000 : ℝ)*(lower4) + (41912477/100000000000000 : ℝ)*(upper5) + (1794880722925231/100000000000000 : ℝ)*(major0) + (1794880722925231/100000000000000 : ℝ)*(major1) + (1794880722925231/100000000000000 : ℝ)*(major2) + (2563956398156999/100000000000000 : ℝ)*(sp0) + (640988961123529/25000000000000 : ℝ)*(sp1) + (2563955586648669/100000000000000 : ℝ)*(sp2) + (102580440760829/10000000000000 : ℝ)*(sp3) + (579401977/100000000000000 : ℝ)*(sp7) + (51290258704089/5000000000000 : ℝ)*(f.failure) + (1281978105542743/50000000000000 : ℝ)*(f.sum) + (100154985142177/49117500000000000000000000000 : ℝ)*base66 + (14978846872665230227/3929400000000000000000000000000000 : ℝ)*base67 + (7362643521643430227/3929400000000000000000000000000000 : ℝ)*base69 + (5248971735550430227/3929400000000000000000000000000000 : ℝ)*base71 + (64950652268611/98235000000000000000000000000 : ℝ)*base73 + (295384278153830227/3929400000000000000000000000000000 : ℝ)*base75 + (17834306558794430227/3929400000000000000000000000000000 : ℝ)*base77 + (4710023011762430227/3929400000000000000000000000000000 : ℝ)*base79 + (13507049372617/49117500000000000000000000000 : ℝ)*base82 + (1953163/500000000000000000000 : ℝ)*base89 + (1953163/500000000000000000000 : ℝ)*base91 + (1953163/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21297155663117576008879/5457500000000000000000000000 : ℝ) := by norm_num
    linear_combination (227604667/25000000000000 : ℝ)*(base19) + (85506581/12500000000000 : ℝ)*(base23) + (7466761/12500000000000 : ℝ)*(upper2) + (222468883/100000000000000 : ℝ)*(upper3) + (1834136622123909/100000000000000 : ℝ)*(major0) + (1834136622123909/100000000000000 : ℝ)*(major1) + (1834136622123909/100000000000000 : ℝ)*(major2) + (356087841/5000000000000 : ℝ)*(sp1) + (313479169/5000000000000 : ℝ)*(sp2) + (296175621/100000000000000 : ℝ)*(sp3) + (1310016259586051/50000000000000 : ℝ)*(sp4) + (1310012243498307/50000000000000 : ℝ)*(sp5) + (2620025565536073/100000000000000 : ℝ)*(sp6) + (209648059764253/20000000000000 : ℝ)*(sp7) + (524120297498443/50000000000000 : ℝ)*(f.failure) + (1310016259586051/50000000000000 : ℝ)*(f.sum) + (45888303566359/16372500000000000000000000000 : ℝ)*base65 + (6129340172366790949/1309800000000000000000000000000000 : ℝ)*base68 + (2356659083601990949/1309800000000000000000000000000000 : ℝ)*base70 + (8985051146245590949/1309800000000000000000000000000000 : ℝ)*base72 + (7344078586931/16372500000000000000000000000 : ℝ)*base74 + (2268120707153609051/1309800000000000000000000000000000 : ℝ)*base75 + (5180665004574209051/1309800000000000000000000000000000 : ℝ)*base77 + (5121339421098209051/1309800000000000000000000000000000 : ℝ)*base79 + (11633402707663/8186250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (49746081/5000000000000000000000 : ℝ)*base89 + (49746081/5000000000000000000000 : ℝ)*base91 + (49746081/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1623_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1623_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1623_s2_0 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-167094651/1000000000 : ℝ)*x 0 + (5461307459/10000000000 : ℝ)*x 1 + (5176935731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167094651/1000000000 : ℝ)^4811 ≤ (10300364782811/100000000000000 : ℝ)^3787 := by
    have hnat : (167094651 : ℕ)^4811*100000000000000^3787 ≤ 10300364782811^3787*1000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167094651 1000000000 10300364782811 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461307459/10000000000 : ℝ)^4811 ≤ (46372655683323/100000000000000 : ℝ)^3787 := by
    have hnat : (5461307459 : ℕ)^4811*100000000000000^3787 ≤ 46372655683323^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461307459 10000000000 46372655683323 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176935731/10000000000 : ℝ)^4811 ≤ (541587243969/1250000000000 : ℝ)^3787 := by
    have hnat : (5176935731 : ℕ)^4811*1250000000000^3787 ≤ 541587243969^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176935731 10000000000 541587243969 1250000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167094651/1000000000 : ℝ), (5461307459/10000000000 : ℝ), (5176935731/10000000000 : ℝ)] ![(10300364782811/100000000000000 : ℝ), (46372655683323/100000000000000 : ℝ), (541587243969/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167094651/1000000000 : ℝ)|^4811 ≤ (10300364782811/100000000000000 : ℝ)^3787
        have hw : |(-167094651/1000000000 : ℝ)|=(167094651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461307459/10000000000 : ℝ)|^4811 ≤ (46372655683323/100000000000000 : ℝ)^3787
        have hw : |(5461307459/10000000000 : ℝ)|=(5461307459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176935731/10000000000 : ℝ)|^4811 ≤ (541587243969/1250000000000 : ℝ)^3787
        have hw : |(5176935731/10000000000 : ℝ)|=(5176935731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s2_1 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676629467/5000000000 : ℝ)*x 0 + (-1817671599/10000000000 : ℝ)*x 1 + (5176935797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676629467/5000000000 : ℝ)^4811 ≤ (45210256328597/100000000000000 : ℝ)^3787 := by
    have hnat : (2676629467 : ℕ)^4811*100000000000000^3787 ≤ 45210256328597^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676629467 5000000000 45210256328597 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1817671599/10000000000 : ℝ)^4811 ≤ (11462763442947/100000000000000 : ℝ)^3787 := by
    have hnat : (1817671599 : ℕ)^4811*100000000000000^3787 ≤ 11462763442947^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817671599 10000000000 11462763442947 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176935797/10000000000 : ℝ)^4811 ≤ (43326980219249/100000000000000 : ℝ)^3787 := by
    have hnat : (5176935797 : ℕ)^4811*100000000000000^3787 ≤ 43326980219249^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176935797 10000000000 43326980219249 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676629467/5000000000 : ℝ), (-1817671599/10000000000 : ℝ), (5176935797/10000000000 : ℝ)] ![(45210256328597/100000000000000 : ℝ), (11462763442947/100000000000000 : ℝ), (43326980219249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676629467/5000000000 : ℝ)|^4811 ≤ (45210256328597/100000000000000 : ℝ)^3787
        have hw : |(2676629467/5000000000 : ℝ)|=(2676629467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1817671599/10000000000 : ℝ)|^4811 ≤ (11462763442947/100000000000000 : ℝ)^3787
        have hw : |(-1817671599/10000000000 : ℝ)|=(1817671599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176935797/10000000000 : ℝ)|^4811 ≤ (43326980219249/100000000000000 : ℝ)^3787
        have hw : |(5176935797/10000000000 : ℝ)|=(5176935797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s2_2 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353259031/10000000000 : ℝ)*x 0 + (5176935587/10000000000 : ℝ)*x 1 + (-1817671747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353259031/10000000000 : ℝ)^4811 ≤ (11302564342327/25000000000000 : ℝ)^3787 := by
    have hnat : (5353259031 : ℕ)^4811*25000000000000^3787 ≤ 11302564342327^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353259031 10000000000 11302564342327 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176935587/10000000000 : ℝ)^4811 ≤ (21663488993237/50000000000000 : ℝ)^3787 := by
    have hnat : (5176935587 : ℕ)^4811*50000000000000^3787 ≤ 21663488993237^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176935587 10000000000 21663488993237 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1817671747/10000000000 : ℝ)^4811 ≤ (229255292573/2000000000000 : ℝ)^3787 := by
    have hnat : (1817671747 : ℕ)^4811*2000000000000^3787 ≤ 229255292573^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817671747 10000000000 229255292573 2000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353259031/10000000000 : ℝ), (5176935587/10000000000 : ℝ), (-1817671747/10000000000 : ℝ)] ![(11302564342327/25000000000000 : ℝ), (21663488993237/50000000000000 : ℝ), (229255292573/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353259031/10000000000 : ℝ)|^4811 ≤ (11302564342327/25000000000000 : ℝ)^3787
        have hw : |(5353259031/10000000000 : ℝ)|=(5353259031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176935587/10000000000 : ℝ)|^4811 ≤ (21663488993237/50000000000000 : ℝ)^3787
        have hw : |(5176935587/10000000000 : ℝ)|=(5176935587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1817671747/10000000000 : ℝ)|^4811 ≤ (229255292573/2000000000000 : ℝ)^3787
        have hw : |(-1817671747/10000000000 : ℝ)|=(1817671747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s2_3 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65643483/156250000 : ℝ)*x 0 + (3857140763/10000000000 : ℝ)*x 1 + (4567916027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65643483/156250000 : ℝ)^4811 ≤ (33230107464083/100000000000000 : ℝ)^3787 := by
    have hnat : (65643483 : ℕ)^4811*100000000000000^3787 ≤ 33230107464083^3787*156250000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65643483 156250000 33230107464083 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3857140763/10000000000 : ℝ)^4811 ≤ (14906037351461/50000000000000 : ℝ)^3787 := by
    have hnat : (3857140763 : ℕ)^4811*50000000000000^3787 ≤ 14906037351461^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3857140763 10000000000 14906037351461 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4567916027/10000000000 : ℝ)^4811 ≤ (1847890890729/5000000000000 : ℝ)^3787 := by
    have hnat : (4567916027 : ℕ)^4811*5000000000000^3787 ≤ 1847890890729^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567916027 10000000000 1847890890729 5000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65643483/156250000 : ℝ), (3857140763/10000000000 : ℝ), (4567916027/10000000000 : ℝ)] ![(33230107464083/100000000000000 : ℝ), (14906037351461/50000000000000 : ℝ), (1847890890729/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65643483/156250000 : ℝ)|^4811 ≤ (33230107464083/100000000000000 : ℝ)^3787
        have hw : |(65643483/156250000 : ℝ)|=(65643483/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3857140763/10000000000 : ℝ)|^4811 ≤ (14906037351461/50000000000000 : ℝ)^3787
        have hw : |(3857140763/10000000000 : ℝ)|=(3857140763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4567916027/10000000000 : ℝ)|^4811 ≤ (1847890890729/5000000000000 : ℝ)^3787
        have hw : |(4567916027/10000000000 : ℝ)|=(4567916027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s2_4 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208877893/1250000000 : ℝ)*x 0 + (129478621/250000000 : ℝ)*x 1 + (5459074179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208877893/1250000000 : ℝ)^4811 ≤ (1287620615649/12500000000000 : ℝ)^3787 := by
    have hnat : (208877893 : ℕ)^4811*12500000000000^3787 ≤ 1287620615649^3787*1250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208877893 1250000000 1287620615649 12500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129478621/250000000 : ℝ)^4811 ≤ (1734018747973/4000000000000 : ℝ)^3787 := by
    have hnat : (129478621 : ℕ)^4811*4000000000000^3787 ≤ 1734018747973^3787*250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129478621 250000000 1734018747973 4000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459074179/10000000000 : ℝ)^4811 ≤ (5793570795313/12500000000000 : ℝ)^3787 := by
    have hnat : (5459074179 : ℕ)^4811*12500000000000^3787 ≤ 5793570795313^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459074179 10000000000 5793570795313 12500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208877893/1250000000 : ℝ), (129478621/250000000 : ℝ), (5459074179/10000000000 : ℝ)] ![(1287620615649/12500000000000 : ℝ), (1734018747973/4000000000000 : ℝ), (5793570795313/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208877893/1250000000 : ℝ)|^4811 ≤ (1287620615649/12500000000000 : ℝ)^3787
        have hw : |(-208877893/1250000000 : ℝ)|=(208877893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129478621/250000000 : ℝ)|^4811 ≤ (1734018747973/4000000000000 : ℝ)^3787
        have hw : |(129478621/250000000 : ℝ)|=(129478621/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459074179/10000000000 : ℝ)|^4811 ≤ (5793570795313/12500000000000 : ℝ)^3787
        have hw : |(5459074179/10000000000 : ℝ)|=(5459074179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s2_5 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277562311/10000000000 : ℝ)*x 0 + (-767766633/5000000000 : ℝ)*x 1 + (1091814817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277562311/10000000000 : ℝ)^4811 ≤ (4439966615101/10000000000000 : ℝ)^3787 := by
    have hnat : (5277562311 : ℕ)^4811*10000000000000^3787 ≤ 4439966615101^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277562311 10000000000 4439966615101 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (767766633/5000000000 : ℝ)^4811 ≤ (9251768486153/100000000000000 : ℝ)^3787 := by
    have hnat : (767766633 : ℕ)^4811*100000000000000^3787 ≤ 9251768486153^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767766633 5000000000 9251768486153 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091814817/2000000000 : ℝ)^4811 ≤ (46348565348627/100000000000000 : ℝ)^3787 := by
    have hnat : (1091814817 : ℕ)^4811*100000000000000^3787 ≤ 46348565348627^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091814817 2000000000 46348565348627 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277562311/10000000000 : ℝ), (-767766633/5000000000 : ℝ), (1091814817/2000000000 : ℝ)] ![(4439966615101/10000000000000 : ℝ), (9251768486153/100000000000000 : ℝ), (46348565348627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277562311/10000000000 : ℝ)|^4811 ≤ (4439966615101/10000000000000 : ℝ)^3787
        have hw : |(5277562311/10000000000 : ℝ)|=(5277562311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-767766633/5000000000 : ℝ)|^4811 ≤ (9251768486153/100000000000000 : ℝ)^3787
        have hw : |(-767766633/5000000000 : ℝ)|=(767766633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091814817/2000000000 : ℝ)|^4811 ≤ (46348565348627/100000000000000 : ℝ)^3787
        have hw : |(1091814817/2000000000 : ℝ)|=(1091814817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s2_6 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277562213/10000000000 : ℝ)*x 0 + (5459074273/10000000000 : ℝ)*x 1 + (-767766569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277562213/10000000000 : ℝ)^4811 ≤ (44399665103611/100000000000000 : ℝ)^3787 := by
    have hnat : (5277562213 : ℕ)^4811*100000000000000^3787 ≤ 44399665103611^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277562213 10000000000 44399665103611 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459074273/10000000000 : ℝ)^4811 ≤ (46348567376381/100000000000000 : ℝ)^3787 := by
    have hnat : (5459074273 : ℕ)^4811*100000000000000^3787 ≤ 46348567376381^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459074273 10000000000 46348567376381 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767766569/5000000000 : ℝ)^4811 ≤ (4625883753201/50000000000000 : ℝ)^3787 := by
    have hnat : (767766569 : ℕ)^4811*50000000000000^3787 ≤ 4625883753201^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767766569 5000000000 4625883753201 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277562213/10000000000 : ℝ), (5459074273/10000000000 : ℝ), (-767766569/5000000000 : ℝ)] ![(44399665103611/100000000000000 : ℝ), (46348567376381/100000000000000 : ℝ), (4625883753201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277562213/10000000000 : ℝ)|^4811 ≤ (44399665103611/100000000000000 : ℝ)^3787
        have hw : |(5277562213/10000000000 : ℝ)|=(5277562213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459074273/10000000000 : ℝ)|^4811 ≤ (46348567376381/100000000000000 : ℝ)^3787
        have hw : |(5459074273/10000000000 : ℝ)|=(5459074273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-767766569/5000000000 : ℝ)|^4811 ≤ (4625883753201/50000000000000 : ℝ)^3787
        have hw : |(-767766569/5000000000 : ℝ)|=(767766569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s2_7 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201374377/10000000000 : ℝ)*x 0 + (456239417/1000000000 : ℝ)*x 1 + (965680759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201374377/10000000000 : ℝ)^4811 ≤ (8308007851857/25000000000000 : ℝ)^3787 := by
    have hnat : (4201374377 : ℕ)^4811*25000000000000^3787 ≤ 8308007851857^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201374377 10000000000 8308007851857 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456239417/1000000000 : ℝ)^4811 ≤ (18450535439699/50000000000000 : ℝ)^3787 := by
    have hnat : (456239417 : ℕ)^4811*50000000000000^3787 ≤ 18450535439699^3787*1000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456239417 1000000000 18450535439699 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965680759/2500000000 : ℝ)^4811 ≤ (14933448850091/50000000000000 : ℝ)^3787 := by
    have hnat : (965680759 : ℕ)^4811*50000000000000^3787 ≤ 14933448850091^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965680759 2500000000 14933448850091 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201374377/10000000000 : ℝ), (456239417/1000000000 : ℝ), (965680759/2500000000 : ℝ)] ![(8308007851857/25000000000000 : ℝ), (18450535439699/50000000000000 : ℝ), (14933448850091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201374377/10000000000 : ℝ)|^4811 ≤ (8308007851857/25000000000000 : ℝ)^3787
        have hw : |(4201374377/10000000000 : ℝ)|=(4201374377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456239417/1000000000 : ℝ)|^4811 ≤ (18450535439699/50000000000000 : ℝ)^3787
        have hw : |(456239417/1000000000 : ℝ)|=(456239417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965680759/2500000000 : ℝ)|^4811 ≤ (14933448850091/50000000000000 : ℝ)^3787
        have hw : |(965680759/2500000000 : ℝ)|=(965680759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1623_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1301/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16441/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4677/50000 : ℝ) ^ (4807/1024 : ℝ) ≤ (1477460753810451/100000000000000000000 : ℝ) := by
    have hpowers : (4677/50000 : ℝ)^4807 ≤ (1477460753810451/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4677 : ℕ)^4807*100000000000000000000^1024 ≤ 1477460753810451^1024*50000^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4677 50000 1477460753810451 100000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4677/50000 : ℝ)) (X := (1477460753810451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (141/800 : ℝ) ^ (4807/1024 : ℝ) ≤ (28911915263551963/100000000000000000000 : ℝ) := by
    have hpowers : (141/800 : ℝ)^4807 ≤ (28911915263551963/100000000000000000000 : ℝ)^1024 := by
      have hnat : (141 : ℕ)^4807*100000000000000000000^1024 ≤ 28911915263551963^1024*800^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 800 28911915263551963 100000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/800 : ℝ)) (X := (28911915263551963/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001477460753810451/50000000000000000000 : ℝ) ≤ (625003934112287/625000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (50001477460753810451/50000000000000000000 : ℝ)^1024 ≤ (625003934112287/625000000000000 : ℝ)^4807 := by
      have hnat : (50001477460753810451 : ℕ)^1024*625000000000000^4807 ≤ 625003934112287^4807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001477460753810451 50000000000000000000 625003934112287 625000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625003934112287/625000000000000 : ℝ)) (X := (50001477460753810451/50000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015194688008681207/50000000000000000000 : ℝ) ≤ (2500161821305271/2500000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (50015194688008681207/50000000000000000000 : ℝ)^1024 ≤ (2500161821305271/2500000000000000 : ℝ)^4807 := by
      have hnat : (50015194688008681207 : ℕ)^1024*2500000000000000^4807 ≤ 2500161821305271^4807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015194688008681207 50000000000000000000 2500161821305271 2500000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500161821305271/2500000000000000 : ℝ)) (X := (50015194688008681207/50000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028911915263551963/50000000000000000000 : ℝ) ≤ (1250153953080697/1250000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (50028911915263551963/50000000000000000000 : ℝ)^1024 ≤ (1250153953080697/1250000000000000 : ℝ)^4807 := by
      have hnat : (50028911915263551963 : ℕ)^1024*1250000000000000^4807 ≤ 1250153953080697^4807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028911915263551963 50000000000000000000 1250153953080697 1250000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250153953080697/1250000000000000 : ℝ)) (X := (50028911915263551963/50000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1477460753810451/100000000000000000000 : ℝ) ≤ ((287151350009479917/287187500000000000 : ℝ)+2*(48694952041/68925000000000 : ℝ)*(4677/50000 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (287151350009479917/287187500000000000 : ℝ)+2*(48694952041/68925000000000 : ℝ)*(4677/50000 : ℝ)=(625003934112287/625000000000000 : ℝ) by norm_num, show 1+2*(1477460753810451/100000000000000000000 : ℝ)=(50001477460753810451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28911915263551963/100000000000000000000 : ℝ)+(1477460753810451/100000000000000000000 : ℝ) ≤ ((287151350009479917/287187500000000000 : ℝ)+(48694952041/68925000000000 : ℝ)*((141/800 : ℝ)+(4677/50000 : ℝ)))^(4807/1024 : ℝ) := by
    rw [show (287151350009479917/287187500000000000 : ℝ)+(48694952041/68925000000000 : ℝ)*((141/800 : ℝ)+(4677/50000 : ℝ))=(2500161821305271/2500000000000000 : ℝ) by norm_num, show 1+(28911915263551963/100000000000000000000 : ℝ)+(1477460753810451/100000000000000000000 : ℝ)=(50015194688008681207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28911915263551963/100000000000000000000 : ℝ) ≤ ((287151350009479917/287187500000000000 : ℝ)+2*(48694952041/68925000000000 : ℝ)*(141/800 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (287151350009479917/287187500000000000 : ℝ)+2*(48694952041/68925000000000 : ℝ)*(141/800 : ℝ)=(1250153953080697/1250000000000000 : ℝ) by norm_num, show 1+2*(28911915263551963/100000000000000000000 : ℝ)=(50028911915263551963/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (287151350009479917/287187500000000000 : ℝ)*(X 1 0+X 2 0)+(48694952041/68925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (4677/50000 : ℝ)) (hi := (141/800 : ℝ)) (c := (287151350009479917/287187500000000000 : ℝ)) (alpha := (48694952041/68925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (287151350009479917/287187500000000000 : ℝ)*(X 0 1+X 2 1)+(48694952041/68925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (4677/50000 : ℝ)) (hi := (141/800 : ℝ)) (c := (287151350009479917/287187500000000000 : ℝ)) (alpha := (48694952041/68925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (287151350009479917/287187500000000000 : ℝ)*(X 0 2+X 1 2)+(48694952041/68925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (4677/50000 : ℝ)) (hi := (141/800 : ℝ)) (c := (287151350009479917/287187500000000000 : ℝ)) (alpha := (48694952041/68925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-167094651/1000000000 : ℝ)*X 0 0+(5461307459/10000000000 : ℝ)*X 0 1+(5176935731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676629467/5000000000 : ℝ)*X 1 0+(-1817671599/10000000000 : ℝ)*X 1 1+(5176935797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353259031/10000000000 : ℝ)*X 2 0+(5176935587/10000000000 : ℝ)*X 2 1+(-1817671747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((65643483/156250000 : ℝ)*X 0 0+(3857140763/10000000000 : ℝ)*X 0 1+(4567916027/10000000000 : ℝ)*X 0 2+(65643483/156250000 : ℝ)*X 1 0+(3857140763/10000000000 : ℝ)*X 1 1+(4567916027/10000000000 : ℝ)*X 1 2+(65643483/156250000 : ℝ)*X 2 0+(3857140763/10000000000 : ℝ)*X 2 1+(4567916027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208877893/1250000000 : ℝ)*X 0 0+(129478621/250000000 : ℝ)*X 0 1+(5459074179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277562311/10000000000 : ℝ)*X 1 0+(-767766633/5000000000 : ℝ)*X 1 1+(1091814817/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277562213/10000000000 : ℝ)*X 2 0+(5459074273/10000000000 : ℝ)*X 2 1+(-767766569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4201374377/10000000000 : ℝ)*X 0 0+(456239417/1000000000 : ℝ)*X 0 1+(965680759/2500000000 : ℝ)*X 0 2+(4201374377/10000000000 : ℝ)*X 1 0+(456239417/1000000000 : ℝ)*X 1 1+(965680759/2500000000 : ℝ)*X 1 2+(4201374377/10000000000 : ℝ)*X 2 0+(456239417/1000000000 : ℝ)*X 2 1+(965680759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (190050030747909160809369/56091308593750000000000000000 : ℝ) := by norm_num
    linear_combination (432880413/100000000000000 : ℝ)*(base19) + (458332857/100000000000000 : ℝ)*(base23) + (10242507/50000000000000 : ℝ)*(lower2) + (27205319/20000000000000 : ℝ)*(upper3) + (3021853/50000000000000 : ℝ)*(upper5) + (615431491883259/25000000000000 : ℝ)*(major0) + (615431491883259/25000000000000 : ℝ)*(major1) + (615431491883259/25000000000000 : ℝ)*(major2) + (1758264865622003/50000000000000 : ℝ)*(sp0) + (879133174913899/25000000000000 : ℝ)*(sp1) + (219783292137697/6250000000000 : ℝ)*(sp2) + (17586449688537/1250000000000 : ℝ)*(sp3) + (1700646001/50000000000000 : ℝ)*(sp4) + (271450623/10000000000000 : ℝ)*(sp7) + (140691868958919/10000000000000 : ℝ)*(f.failure) + (439566641567001/12500000000000 : ℝ)*(f.sum) + (12122423890411/2297500000000000000000000000 : ℝ)*base66 + (33860775458453189/3589843750000000000000000000000 : ℝ)*base67 + (109517233458547003/7179687500000000000000000000000 : ℝ)*base69 + (6745052666578189/3589843750000000000000000000000 : ℝ)*base71 + (697336593719/574375000000000000000000000 : ℝ)*base74 + (29807296785921747/7179687500000000000000000000000 : ℝ)*base76 + (15377614494015561/3589843750000000000000000000000 : ℝ)*base78 + (12811589612140753/7179687500000000000000000000000 : ℝ)*base79 + (2218416015331/574375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2650773/1000000000000000000000 : ℝ)*base89 + (2650773/1000000000000000000000 : ℝ)*base91 + (2650773/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3190965904304158106733/574375000000000000000000000 : ℝ) := by norm_num
    linear_combination (777859067/100000000000000 : ℝ)*(base19) + (772017909/100000000000000 : ℝ)*(base23) + (100188739/100000000000000 : ℝ)*(upper3) + (2668757/12500000000000 : ℝ)*(lower4) + (67393999/50000000000000 : ℝ)*(upper5) + (1250393273524581/50000000000000 : ℝ)*(major0) + (1250393273524581/50000000000000 : ℝ)*(major1) + (1250393273524581/50000000000000 : ℝ)*(major2) + (3889075033/50000000000000 : ℝ)*(sp1) + (4587645707/50000000000000 : ℝ)*(sp2) + (893082606740977/25000000000000 : ℝ)*(sp4) + (142892874838191/4000000000000 : ℝ)*(sp5) + (1786160239827293/50000000000000 : ℝ)*(sp6) + (714621240974797/50000000000000 : ℝ)*(sp7) + (714621240974797/50000000000000 : ℝ)*(f.failure) + (893082606740977/25000000000000 : ℝ)*(f.sum) + (8228808235907/2297500000000000000000000000 : ℝ)*base66 + (56048180746989777/14359375000000000000000000000000 : ℝ)*base67 + (29725782714010223/14359375000000000000000000000000 : ℝ)*base70 + (14825410778415413/3589843750000000000000000000000 : ℝ)*base71 + (69618817329/287187500000000000000000000 : ℝ)*base74 + (29186992157434799/7179687500000000000000000000000 : ℝ)*base76 + (19464468142228973/14359375000000000000000000000000 : ℝ)*base78 + (32975805861927277/14359375000000000000000000000000 : ℝ)*base79 + (4327722326327/2297500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5832999/5000000000000000000000 : ℝ)*base89 + (5832999/5000000000000000000000 : ℝ)*base91 + (5832999/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1623_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1623_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1623_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1623_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1623_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1623_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1623_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
