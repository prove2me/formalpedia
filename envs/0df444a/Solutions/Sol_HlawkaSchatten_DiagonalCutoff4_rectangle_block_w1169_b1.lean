-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1169_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:55.711714+00:00
-- url     : https://prove2.me/submissions/c1e0563b-20d3-4198-b692-fcb04e863b46

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
theorem support_rectangle_w1169_s3_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-268815661/1250000000 : ℝ)*x 0 + (5426447603/10000000000 : ℝ)*x 1 + (5234564147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268815661/1250000000 : ℝ)^4181 ≤ (1632900318997/12500000000000 : ℝ)^3157 := by
    have hnat : (268815661 : ℕ)^4181*12500000000000^3157 ≤ 1632900318997^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268815661 1250000000 1632900318997 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426447603/10000000000 : ℝ)^4181 ≤ (4450445412423/10000000000000 : ℝ)^3157 := by
    have hnat : (5426447603 : ℕ)^4181*10000000000000^3157 ≤ 4450445412423^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426447603 10000000000 4450445412423 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234564147/10000000000 : ℝ)^4181 ≤ (1697293732563/4000000000000 : ℝ)^3157 := by
    have hnat : (5234564147 : ℕ)^4181*4000000000000^3157 ≤ 1697293732563^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234564147 10000000000 1697293732563 4000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268815661/1250000000 : ℝ), (5426447603/10000000000 : ℝ), (5234564147/10000000000 : ℝ)] ![(1632900318997/12500000000000 : ℝ), (4450445412423/10000000000000 : ℝ), (1697293732563/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268815661/1250000000 : ℝ)|^4181 ≤ (1632900318997/12500000000000 : ℝ)^3157
        have hw : |(-268815661/1250000000 : ℝ)|=(268815661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426447603/10000000000 : ℝ)|^4181 ≤ (4450445412423/10000000000000 : ℝ)^3157
        have hw : |(5426447603/10000000000 : ℝ)|=(5426447603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234564147/10000000000 : ℝ)|^4181 ≤ (1697293732563/4000000000000 : ℝ)^3157
        have hw : |(5234564147/10000000000 : ℝ)|=(5234564147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s3_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353150677/10000000000 : ℝ)*x 0 + (-2248552733/10000000000 : ℝ)*x 1 + (104691279/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353150677/10000000000 : ℝ)^4181 ≤ (8742016442313/20000000000000 : ℝ)^3157 := by
    have hnat : (5353150677 : ℕ)^4181*20000000000000^3157 ≤ 8742016442313^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353150677 10000000000 8742016442313 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248552733/10000000000 : ℝ)^4181 ≤ (13857576573559/100000000000000 : ℝ)^3157 := by
    have hnat : (2248552733 : ℕ)^4181*100000000000000^3157 ≤ 13857576573559^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248552733 10000000000 13857576573559 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104691279/200000000 : ℝ)^4181 ≤ (21216170599591/50000000000000 : ℝ)^3157 := by
    have hnat : (104691279 : ℕ)^4181*50000000000000^3157 ≤ 21216170599591^3157*200000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104691279 200000000 21216170599591 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353150677/10000000000 : ℝ), (-2248552733/10000000000 : ℝ), (104691279/200000000 : ℝ)] ![(8742016442313/20000000000000 : ℝ), (13857576573559/100000000000000 : ℝ), (21216170599591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353150677/10000000000 : ℝ)|^4181 ≤ (8742016442313/20000000000000 : ℝ)^3157
        have hw : |(5353150677/10000000000 : ℝ)|=(5353150677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2248552733/10000000000 : ℝ)|^4181 ≤ (13857576573559/100000000000000 : ℝ)^3157
        have hw : |(-2248552733/10000000000 : ℝ)|=(2248552733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104691279/200000000 : ℝ)|^4181 ≤ (21216170599591/50000000000000 : ℝ)^3157
        have hw : |(104691279/200000000 : ℝ)|=(104691279/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s3_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353150761/10000000000 : ℝ)*x 0 + (327160247/625000000 : ℝ)*x 1 + (-2248552619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353150761/10000000000 : ℝ)^4181 ≤ (43710083119923/100000000000000 : ℝ)^3157 := by
    have hnat : (5353150761 : ℕ)^4181*100000000000000^3157 ≤ 43710083119923^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353150761 10000000000 43710083119923 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327160247/625000000 : ℝ)^4181 ≤ (42432341220653/100000000000000 : ℝ)^3157 := by
    have hnat : (327160247 : ℕ)^4181*100000000000000^3157 ≤ 42432341220653^3157*625000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327160247 625000000 42432341220653 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248552619/10000000000 : ℝ)^4181 ≤ (2771515128621/20000000000000 : ℝ)^3157 := by
    have hnat : (2248552619 : ℕ)^4181*20000000000000^3157 ≤ 2771515128621^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248552619 10000000000 2771515128621 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353150761/10000000000 : ℝ), (327160247/625000000 : ℝ), (-2248552619/10000000000 : ℝ)] ![(43710083119923/100000000000000 : ℝ), (42432341220653/100000000000000 : ℝ), (2771515128621/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353150761/10000000000 : ℝ)|^4181 ≤ (43710083119923/100000000000000 : ℝ)^3157
        have hw : |(5353150761/10000000000 : ℝ)|=(5353150761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327160247/625000000 : ℝ)|^4181 ≤ (42432341220653/100000000000000 : ℝ)^3157
        have hw : |(327160247/625000000 : ℝ)|=(327160247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248552619/10000000000 : ℝ)|^4181 ≤ (2771515128621/20000000000000 : ℝ)^3157
        have hw : |(-2248552619/10000000000 : ℝ)|=(2248552619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s3_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2179396423/5000000000 : ℝ)*x 0 + (1042769733/2500000000 : ℝ)*x 1 + (4554848871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179396423/5000000000 : ℝ)^4181 ≤ (33295962668581/100000000000000 : ℝ)^3157 := by
    have hnat : (2179396423 : ℕ)^4181*100000000000000^3157 ≤ 33295962668581^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179396423 5000000000 33295962668581 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042769733/2500000000 : ℝ)^4181 ≤ (1963146649453/6250000000000 : ℝ)^3157 := by
    have hnat : (1042769733 : ℕ)^4181*6250000000000^3157 ≤ 1963146649453^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042769733 2500000000 1963146649453 6250000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4554848871/10000000000 : ℝ)^4181 ≤ (35293690928051/100000000000000 : ℝ)^3157 := by
    have hnat : (4554848871 : ℕ)^4181*100000000000000^3157 ≤ 35293690928051^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554848871 10000000000 35293690928051 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179396423/5000000000 : ℝ), (1042769733/2500000000 : ℝ), (4554848871/10000000000 : ℝ)] ![(33295962668581/100000000000000 : ℝ), (1963146649453/6250000000000 : ℝ), (35293690928051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179396423/5000000000 : ℝ)|^4181 ≤ (33295962668581/100000000000000 : ℝ)^3157
        have hw : |(2179396423/5000000000 : ℝ)|=(2179396423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042769733/2500000000 : ℝ)|^4181 ≤ (1963146649453/6250000000000 : ℝ)^3157
        have hw : |(1042769733/2500000000 : ℝ)|=(1042769733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4554848871/10000000000 : ℝ)|^4181 ≤ (35293690928051/100000000000000 : ℝ)^3157
        have hw : |(4554848871/10000000000 : ℝ)|=(4554848871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s3_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075271039/5000000000 : ℝ)*x 0 + (32720593/62500000 : ℝ)*x 1 + (1356428221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075271039/5000000000 : ℝ)^4181 ≤ (13063337622921/100000000000000 : ℝ)^3157 := by
    have hnat : (1075271039 : ℕ)^4181*100000000000000^3157 ≤ 13063337622921^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075271039 5000000000 13063337622921 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32720593/62500000 : ℝ)^4181 ≤ (42440188272171/100000000000000 : ℝ)^3157 := by
    have hnat : (32720593 : ℕ)^4181*100000000000000^3157 ≤ 42440188272171^3157*62500000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32720593 62500000 42440188272171 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356428221/2500000000 : ℝ)^4181 ≤ (2781029630131/6250000000000 : ℝ)^3157 := by
    have hnat : (1356428221 : ℕ)^4181*6250000000000^3157 ≤ 2781029630131^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356428221 2500000000 2781029630131 6250000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075271039/5000000000 : ℝ), (32720593/62500000 : ℝ), (1356428221/2500000000 : ℝ)] ![(13063337622921/100000000000000 : ℝ), (42440188272171/100000000000000 : ℝ), (2781029630131/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075271039/5000000000 : ℝ)|^4181 ≤ (13063337622921/100000000000000 : ℝ)^3157
        have hw : |(-1075271039/5000000000 : ℝ)|=(1075271039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32720593/62500000 : ℝ)|^4181 ≤ (42440188272171/100000000000000 : ℝ)^3157
        have hw : |(32720593/62500000 : ℝ)|=(32720593/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356428221/2500000000 : ℝ)|^4181 ≤ (2781029630131/6250000000000 : ℝ)^3157
        have hw : |(1356428221/2500000000 : ℝ)|=(1356428221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s3_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304442789/10000000000 : ℝ)*x 0 + (-514351043/2500000000 : ℝ)*x 1 + (1356428191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304442789/10000000000 : ℝ)^4181 ≤ (8636828884347/20000000000000 : ℝ)^3157 := by
    have hnat : (5304442789 : ℕ)^4181*20000000000000^3157 ≤ 8636828884347^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304442789 10000000000 8636828884347 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514351043/2500000000 : ℝ)^4181 ≤ (2463876558571/20000000000000 : ℝ)^3157 := by
    have hnat : (514351043 : ℕ)^4181*20000000000000^3157 ≤ 2463876558571^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514351043 2500000000 2463876558571 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356428191/2500000000 : ℝ)^4181 ≤ (44496472778763/100000000000000 : ℝ)^3157 := by
    have hnat : (1356428191 : ℕ)^4181*100000000000000^3157 ≤ 44496472778763^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356428191 2500000000 44496472778763 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304442789/10000000000 : ℝ), (-514351043/2500000000 : ℝ), (1356428191/2500000000 : ℝ)] ![(8636828884347/20000000000000 : ℝ), (2463876558571/20000000000000 : ℝ), (44496472778763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304442789/10000000000 : ℝ)|^4181 ≤ (8636828884347/20000000000000 : ℝ)^3157
        have hw : |(5304442789/10000000000 : ℝ)|=(5304442789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514351043/2500000000 : ℝ)|^4181 ≤ (2463876558571/20000000000000 : ℝ)^3157
        have hw : |(-514351043/2500000000 : ℝ)|=(514351043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356428191/2500000000 : ℝ)|^4181 ≤ (44496472778763/100000000000000 : ℝ)^3157
        have hw : |(1356428191/2500000000 : ℝ)|=(1356428191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s3_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530444341/1000000000 : ℝ)*x 0 + (1356428067/2500000000 : ℝ)*x 1 + (-1028702003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530444341/1000000000 : ℝ)^4181 ≤ (8636830223443/20000000000000 : ℝ)^3157 := by
    have hnat : (530444341 : ℕ)^4181*20000000000000^3157 ≤ 8636830223443^3157*1000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530444341 1000000000 8636830223443 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356428067/2500000000 : ℝ)^4181 ≤ (889929347833/2000000000000 : ℝ)^3157 := by
    have hnat : (1356428067 : ℕ)^4181*2000000000000^3157 ≤ 889929347833^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356428067 2500000000 889929347833 2000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028702003/5000000000 : ℝ)^4181 ≤ (1231938147647/10000000000000 : ℝ)^3157 := by
    have hnat : (1028702003 : ℕ)^4181*10000000000000^3157 ≤ 1231938147647^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028702003 5000000000 1231938147647 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530444341/1000000000 : ℝ), (1356428067/2500000000 : ℝ), (-1028702003/5000000000 : ℝ)] ![(8636830223443/20000000000000 : ℝ), (889929347833/2000000000000 : ℝ), (1231938147647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530444341/1000000000 : ℝ)|^4181 ≤ (8636830223443/20000000000000 : ℝ)^3157
        have hw : |(530444341/1000000000 : ℝ)|=(530444341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356428067/2500000000 : ℝ)|^4181 ≤ (889929347833/2000000000000 : ℝ)^3157
        have hw : |(1356428067/2500000000 : ℝ)|=(1356428067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028702003/5000000000 : ℝ)|^4181 ≤ (1231938147647/10000000000000 : ℝ)^3157
        have hw : |(-1028702003/5000000000 : ℝ)|=(1028702003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s3_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108970657/250000000 : ℝ)*x 0 + (1138346873/2500000000 : ℝ)*x 1 + (4172548557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108970657/250000000 : ℝ)^4181 ≤ (16648150452283/50000000000000 : ℝ)^3157 := by
    have hnat : (108970657 : ℕ)^4181*50000000000000^3157 ≤ 16648150452283^3157*250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108970657 250000000 16648150452283 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138346873/2500000000 : ℝ)^4181 ≤ (8819673787929/25000000000000 : ℝ)^3157 := by
    have hnat : (1138346873 : ℕ)^4181*25000000000000^3157 ≤ 8819673787929^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138346873 2500000000 8819673787929 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172548557/10000000000 : ℝ)^4181 ≤ (15712501968323/50000000000000 : ℝ)^3157 := by
    have hnat : (4172548557 : ℕ)^4181*50000000000000^3157 ≤ 15712501968323^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172548557 10000000000 15712501968323 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108970657/250000000 : ℝ), (1138346873/2500000000 : ℝ), (4172548557/10000000000 : ℝ)] ![(16648150452283/50000000000000 : ℝ), (8819673787929/25000000000000 : ℝ), (15712501968323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108970657/250000000 : ℝ)|^4181 ≤ (16648150452283/50000000000000 : ℝ)^3157
        have hw : |(108970657/250000000 : ℝ)|=(108970657/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1138346873/2500000000 : ℝ)|^4181 ≤ (8819673787929/25000000000000 : ℝ)^3157
        have hw : |(1138346873/2500000000 : ℝ)|=(1138346873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172548557/10000000000 : ℝ)|^4181 ≤ (15712501968323/50000000000000 : ℝ)^3157
        have hw : |(4172548557/10000000000 : ℝ)|=(4172548557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16423/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5357/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16423/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16423/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16423/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16423/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16423/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16423/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9191/100000 : ℝ) ^ (8361/2048 : ℝ) ≤ (1465035857737329/25000000000000000000 : ℝ) := by
    have hpowers : (9191/100000 : ℝ)^8361 ≤ (1465035857737329/25000000000000000000 : ℝ)^2048 := by
      have hnat : (9191 : ℕ)^8361*25000000000000000000^2048 ≤ 1465035857737329^2048*100000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9191 100000 1465035857737329 25000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9191/100000 : ℝ)) (X := (1465035857737329/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16423/100000 : ℝ) ^ (8361/2048 : ℝ) ≤ (31335705960085029/50000000000000000000 : ℝ) := by
    have hpowers : (16423/100000 : ℝ)^8361 ≤ (31335705960085029/50000000000000000000 : ℝ)^2048 := by
      have hnat : (16423 : ℕ)^8361*50000000000000000000^2048 ≤ 31335705960085029^2048*100000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16423 100000 31335705960085029 50000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16423/100000 : ℝ)) (X := (31335705960085029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501465035857737329/12500000000000000000 : ℝ) ≤ (10000287071947063/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (12501465035857737329/12500000000000000000 : ℝ)^2048 ≤ (10000287071947063/10000000000000000 : ℝ)^8361 := by
      have hnat : (12501465035857737329 : ℕ)^2048*10000000000000000^8361 ≤ 10000287071947063^8361*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501465035857737329 12500000000000000000 10000287071947063 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000287071947063/10000000000000000 : ℝ)) (X := (12501465035857737329/12500000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034265777675559687/50000000000000000000 : ℝ) ≤ (2000335644844391/2000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50034265777675559687/50000000000000000000 : ℝ)^2048 ≤ (2000335644844391/2000000000000000 : ℝ)^8361 := by
      have hnat : (50034265777675559687 : ℕ)^2048*2000000000000000^8361 ≤ 2000335644844391^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034265777675559687 50000000000000000000 2000335644844391 2000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000335644844391/2000000000000000 : ℝ)) (X := (50034265777675559687/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25031335705960085029/25000000000000000000 : ℝ) ≤ (10003069376496847/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (25031335705960085029/25000000000000000000 : ℝ)^2048 ≤ (10003069376496847/10000000000000000 : ℝ)^8361 := by
      have hnat : (25031335705960085029 : ℕ)^2048*10000000000000000^8361 ≤ 10003069376496847^8361*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25031335705960085029 25000000000000000000 10003069376496847 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003069376496847/10000000000000000 : ℝ)) (X := (25031335705960085029/25000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1465035857737329/25000000000000000000 : ℝ) ≤ ((9037062992900511859/9040000000000000000 : ℝ)+2*(347788068723/180800000000000 : ℝ)*(9191/100000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (9037062992900511859/9040000000000000000 : ℝ)+2*(347788068723/180800000000000 : ℝ)*(9191/100000 : ℝ)=(10000287071947063/10000000000000000 : ℝ) by norm_num, show 1+2*(1465035857737329/25000000000000000000 : ℝ)=(12501465035857737329/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31335705960085029/50000000000000000000 : ℝ)+(1465035857737329/25000000000000000000 : ℝ) ≤ ((9037062992900511859/9040000000000000000 : ℝ)+(347788068723/180800000000000 : ℝ)*((16423/100000 : ℝ)+(9191/100000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (9037062992900511859/9040000000000000000 : ℝ)+(347788068723/180800000000000 : ℝ)*((16423/100000 : ℝ)+(9191/100000 : ℝ))=(2000335644844391/2000000000000000 : ℝ) by norm_num, show 1+(31335705960085029/50000000000000000000 : ℝ)+(1465035857737329/25000000000000000000 : ℝ)=(50034265777675559687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31335705960085029/50000000000000000000 : ℝ) ≤ ((9037062992900511859/9040000000000000000 : ℝ)+2*(347788068723/180800000000000 : ℝ)*(16423/100000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (9037062992900511859/9040000000000000000 : ℝ)+2*(347788068723/180800000000000 : ℝ)*(16423/100000 : ℝ)=(10003069376496847/10000000000000000 : ℝ) by norm_num, show 1+2*(31335705960085029/50000000000000000000 : ℝ)=(25031335705960085029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9037062992900511859/9040000000000000000 : ℝ)*(X 1 0+X 2 0)+(347788068723/180800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (9191/100000 : ℝ)) (hi := (16423/100000 : ℝ)) (c := (9037062992900511859/9040000000000000000 : ℝ)) (alpha := (347788068723/180800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9037062992900511859/9040000000000000000 : ℝ)*(X 0 1+X 2 1)+(347788068723/180800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (9191/100000 : ℝ)) (hi := (16423/100000 : ℝ)) (c := (9037062992900511859/9040000000000000000 : ℝ)) (alpha := (347788068723/180800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9037062992900511859/9040000000000000000 : ℝ)*(X 0 2+X 1 2)+(347788068723/180800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (9191/100000 : ℝ)) (hi := (16423/100000 : ℝ)) (c := (9037062992900511859/9040000000000000000 : ℝ)) (alpha := (347788068723/180800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-268815661/1250000000 : ℝ)*X 0 0+(5426447603/10000000000 : ℝ)*X 0 1+(5234564147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353150677/10000000000 : ℝ)*X 1 0+(-2248552733/10000000000 : ℝ)*X 1 1+(104691279/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353150761/10000000000 : ℝ)*X 2 0+(327160247/625000000 : ℝ)*X 2 1+(-2248552619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179396423/5000000000 : ℝ)*X 0 0+(1042769733/2500000000 : ℝ)*X 0 1+(4554848871/10000000000 : ℝ)*X 0 2+(2179396423/5000000000 : ℝ)*X 1 0+(1042769733/2500000000 : ℝ)*X 1 1+(4554848871/10000000000 : ℝ)*X 1 2+(2179396423/5000000000 : ℝ)*X 2 0+(1042769733/2500000000 : ℝ)*X 2 1+(4554848871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1075271039/5000000000 : ℝ)*X 0 0+(32720593/62500000 : ℝ)*X 0 1+(1356428221/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304442789/10000000000 : ℝ)*X 1 0+(-514351043/2500000000 : ℝ)*X 1 1+(1356428191/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530444341/1000000000 : ℝ)*X 2 0+(1356428067/2500000000 : ℝ)*X 2 1+(-1028702003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108970657/250000000 : ℝ)*X 0 0+(1138346873/2500000000 : ℝ)*X 0 1+(4172548557/10000000000 : ℝ)*X 0 2+(108970657/250000000 : ℝ)*X 1 0+(1138346873/2500000000 : ℝ)*X 1 1+(4172548557/10000000000 : ℝ)*X 1 2+(108970657/250000000 : ℝ)*X 2 0+(1138346873/2500000000 : ℝ)*X 2 1+(4172548557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1288605610439497717110151173/452000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84943299/10000000000000 : ℝ)*(base19) + (847142259/100000000000000 : ℝ)*(base23) + (45003029/100000000000000 : ℝ)*(lower2) + (34202569/100000000000000 : ℝ)*(upper3) + (109561993/100000000000000 : ℝ)*(upper5) + (31269043204789/800000000000 : ℝ)*(major0) + (31269043204789/800000000000 : ℝ)*(major1) + (1954315200299313/50000000000000 : ℝ)*(major2) + (10178724006443/195312500000 : ℝ)*(sp0) + (81429997785907/1562500000000 : ℝ)*(sp1) + (260575993029439/5000000000000 : ℝ)*(sp2) + (1302867046324123/50000000000000 : ℝ)*(sp3) + (14016432223/100000000000000 : ℝ)*(sp4) + (2952894023/50000000000000 : ℝ)*(sp7) + (651434999609073/25000000000000 : ℝ)*(f.failure) + (5211520707731039/100000000000000 : ℝ)*(f.sum) + (40116376699047/18080000000000000000000000000 : ℝ)*base66 + (8778507661387951/7232000000000000000000000000000 : ℝ)*base67 + (1842712051008927867/452000000000000000000000000000000 : ℝ)*base69 + (68862359251787951/7232000000000000000000000000000 : ℝ)*base71 + (93869122977127/18080000000000000000000000000 : ℝ)*base74 + (1266340401776927867/452000000000000000000000000000000 : ℝ)*base75 + (16947628839189249/7232000000000000000000000000000 : ℝ)*base78 + (158307062402794751/7232000000000000000000000000000 : ℝ)*base79 + (10053508181769/1808000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (18904159/2500000000000000000000 : ℝ)*base89 + (18904159/2500000000000000000000 : ℝ)*base91 + (6095841/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (314151997931949259207049313/113000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44240561/12500000000000 : ℝ)*(base19) + (261730267/25000000000000 : ℝ)*(base23) + (23892991/100000000000000 : ℝ)*(upper3) + (6283027/100000000000000 : ℝ)*(lower4) + (35265729/100000000000000 : ℝ)*(upper5) + (1969348320846431/50000000000000 : ℝ)*(major0) + (1969348320846431/50000000000000 : ℝ)*(major1) + (1969348320846431/50000000000000 : ℝ)*(major2) + (31382011/800000000000 : ℝ)*(sp1) + (2229440709/20000000000000 : ℝ)*(sp2) + (2625804568089851/50000000000000 : ℝ)*(sp4) + (2625802429751919/50000000000000 : ℝ)*(sp5) + (5251596942055089/100000000000000 : ℝ)*(sp6) + (262578405453581/10000000000000 : ℝ)*(sp7) + (262578405453581/10000000000000 : ℝ)*(f.failure) + (2625804568089851/50000000000000 : ℝ)*(f.sum) + (22099348358733/4520000000000000000000000000 : ℝ)*base65 + (1492839309353975229/452000000000000000000000000000000 : ℝ)*base67 + (1101049681662024771/452000000000000000000000000000000 : ℝ)*base70 + (5303819644549975229/452000000000000000000000000000000 : ℝ)*base71 + (11007538383067/4520000000000000000000000000 : ℝ)*base74 + (6469571129209975229/452000000000000000000000000000000 : ℝ)*base75 + (1569935252093975229/452000000000000000000000000000000 : ℝ)*base77 + (2784557708089975229/452000000000000000000000000000000 : ℝ)*base79 + (10420330592507/4520000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (153923/1000000000000000000000 : ℝ)*base89 + (153923/1000000000000000000000 : ℝ)*base91 + (153923/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16423/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1169_s4_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-538329211/2500000000 : ℝ)*x 0 + (5400622567/10000000000 : ℝ)*x 1 + (5258562191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538329211/2500000000 : ℝ)^4181 ≤ (3271416138077/25000000000000 : ℝ)^3157 := by
    have hnat : (538329211 : ℕ)^4181*25000000000000^3157 ≤ 3271416138077^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538329211 2500000000 3271416138077 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400622567/10000000000 : ℝ)^4181 ≤ (22112084936711/50000000000000 : ℝ)^3157 := by
    have hnat : (5400622567 : ℕ)^4181*50000000000000^3157 ≤ 22112084936711^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400622567 10000000000 22112084936711 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258562191/10000000000 : ℝ)^4181 ≤ (4269016555187/10000000000000 : ℝ)^3157 := by
    have hnat : (5258562191 : ℕ)^4181*10000000000000^3157 ≤ 4269016555187^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258562191 10000000000 4269016555187 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538329211/2500000000 : ℝ), (5400622567/10000000000 : ℝ), (5258562191/10000000000 : ℝ)] ![(3271416138077/25000000000000 : ℝ), (22112084936711/50000000000000 : ℝ), (4269016555187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538329211/2500000000 : ℝ)|^4181 ≤ (3271416138077/25000000000000 : ℝ)^3157
        have hw : |(-538329211/2500000000 : ℝ)|=(538329211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400622567/10000000000 : ℝ)|^4181 ≤ (22112084936711/50000000000000 : ℝ)^3157
        have hw : |(5400622567/10000000000 : ℝ)|=(5400622567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258562191/10000000000 : ℝ)|^4181 ≤ (4269016555187/10000000000000 : ℝ)^3157
        have hw : |(5258562191/10000000000 : ℝ)|=(5258562191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s4_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346684497/10000000000 : ℝ)*x 0 + (-1112745723/5000000000 : ℝ)*x 1 + (2629280877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346684497/10000000000 : ℝ)^4181 ≤ (21820086015687/50000000000000 : ℝ)^3157 := by
    have hnat : (5346684497 : ℕ)^4181*50000000000000^3157 ≤ 21820086015687^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346684497 10000000000 21820086015687 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112745723/5000000000 : ℝ)^4181 ≤ (3417416773947/25000000000000 : ℝ)^3157 := by
    have hnat : (1112745723 : ℕ)^4181*25000000000000^3157 ≤ 3417416773947^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112745723 5000000000 3417416773947 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629280877/5000000000 : ℝ)^4181 ≤ (42690160853493/100000000000000 : ℝ)^3157 := by
    have hnat : (2629280877 : ℕ)^4181*100000000000000^3157 ≤ 42690160853493^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629280877 5000000000 42690160853493 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346684497/10000000000 : ℝ), (-1112745723/5000000000 : ℝ), (2629280877/5000000000 : ℝ)] ![(21820086015687/50000000000000 : ℝ), (3417416773947/25000000000000 : ℝ), (42690160853493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346684497/10000000000 : ℝ)|^4181 ≤ (21820086015687/50000000000000 : ℝ)^3157
        have hw : |(5346684497/10000000000 : ℝ)|=(5346684497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1112745723/5000000000 : ℝ)|^4181 ≤ (3417416773947/25000000000000 : ℝ)^3157
        have hw : |(-1112745723/5000000000 : ℝ)|=(1112745723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629280877/5000000000 : ℝ)|^4181 ≤ (42690160853493/100000000000000 : ℝ)^3157
        have hw : |(2629280877/5000000000 : ℝ)|=(2629280877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s4_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534668479/1000000000 : ℝ)*x 0 + (5258561191/10000000000 : ℝ)*x 1 + (-2225491801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534668479/1000000000 : ℝ)^4181 ≤ (43640175198571/100000000000000 : ℝ)^3157 := by
    have hnat : (534668479 : ℕ)^4181*100000000000000^3157 ≤ 43640175198571^3157*1000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534668479 1000000000 43640175198571 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258561191/10000000000 : ℝ)^4181 ≤ (8538030960087/20000000000000 : ℝ)^3157 := by
    have hnat : (5258561191 : ℕ)^4181*20000000000000^3157 ≤ 8538030960087^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258561191 10000000000 8538030960087 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225491801/10000000000 : ℝ)^4181 ≤ (683483499179/5000000000000 : ℝ)^3157 := by
    have hnat : (2225491801 : ℕ)^4181*5000000000000^3157 ≤ 683483499179^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225491801 10000000000 683483499179 5000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534668479/1000000000 : ℝ), (5258561191/10000000000 : ℝ), (-2225491801/10000000000 : ℝ)] ![(43640175198571/100000000000000 : ℝ), (8538030960087/20000000000000 : ℝ), (683483499179/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534668479/1000000000 : ℝ)|^4181 ≤ (43640175198571/100000000000000 : ℝ)^3157
        have hw : |(534668479/1000000000 : ℝ)|=(534668479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258561191/10000000000 : ℝ)|^4181 ≤ (8538030960087/20000000000000 : ℝ)^3157
        have hw : |(5258561191/10000000000 : ℝ)|=(5258561191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2225491801/10000000000 : ℝ)|^4181 ≤ (683483499179/5000000000000 : ℝ)^3157
        have hw : |(-2225491801/10000000000 : ℝ)|=(2225491801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s4_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360460669/10000000000 : ℝ)*x 0 + (4220686779/10000000000 : ℝ)*x 1 + (4504810857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360460669/10000000000 : ℝ)^4181 ≤ (8328209068003/25000000000000 : ℝ)^3157 := by
    have hnat : (4360460669 : ℕ)^4181*25000000000000^3157 ≤ 8328209068003^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360460669 10000000000 8328209068003 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4220686779/10000000000 : ℝ)^4181 ≤ (15953020921211/50000000000000 : ℝ)^3157 := by
    have hnat : (4220686779 : ℕ)^4181*50000000000000^3157 ≤ 15953020921211^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220686779 10000000000 15953020921211 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504810857/10000000000 : ℝ)^4181 ≤ (8695280469077/25000000000000 : ℝ)^3157 := by
    have hnat : (4504810857 : ℕ)^4181*25000000000000^3157 ≤ 8695280469077^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504810857 10000000000 8695280469077 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360460669/10000000000 : ℝ), (4220686779/10000000000 : ℝ), (4504810857/10000000000 : ℝ)] ![(8328209068003/25000000000000 : ℝ), (15953020921211/50000000000000 : ℝ), (8695280469077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360460669/10000000000 : ℝ)|^4181 ≤ (8328209068003/25000000000000 : ℝ)^3157
        have hw : |(4360460669/10000000000 : ℝ)|=(4360460669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4220686779/10000000000 : ℝ)|^4181 ≤ (15953020921211/50000000000000 : ℝ)^3157
        have hw : |(4220686779/10000000000 : ℝ)|=(4220686779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504810857/10000000000 : ℝ)|^4181 ≤ (8695280469077/25000000000000 : ℝ)^3157
        have hw : |(4504810857/10000000000 : ℝ)|=(4504810857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s4_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153324177/10000000000 : ℝ)*x 0 + (5258963007/10000000000 : ℝ)*x 1 + (21600879/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153324177/10000000000 : ℝ)^4181 ≤ (13085723569067/100000000000000 : ℝ)^3157 := by
    have hnat : (2153324177 : ℕ)^4181*100000000000000^3157 ≤ 13085723569067^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153324177 10000000000 13085723569067 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258963007/10000000000 : ℝ)^4181 ≤ (42694474952077/100000000000000 : ℝ)^3157 := by
    have hnat : (5258963007 : ℕ)^4181*100000000000000^3157 ≤ 42694474952077^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258963007 10000000000 42694474952077 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21600879/40000000 : ℝ)^4181 ≤ (22109900728729/50000000000000 : ℝ)^3157 := by
    have hnat : (21600879 : ℕ)^4181*50000000000000^3157 ≤ 22109900728729^3157*40000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21600879 40000000 22109900728729 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153324177/10000000000 : ℝ), (5258963007/10000000000 : ℝ), (21600879/40000000 : ℝ)] ![(13085723569067/100000000000000 : ℝ), (42694474952077/100000000000000 : ℝ), (22109900728729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153324177/10000000000 : ℝ)|^4181 ≤ (13085723569067/100000000000000 : ℝ)^3157
        have hw : |(-2153324177/10000000000 : ℝ)|=(2153324177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258963007/10000000000 : ℝ)|^4181 ≤ (42694474952077/100000000000000 : ℝ)^3157
        have hw : |(5258963007/10000000000 : ℝ)|=(5258963007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21600879/40000000 : ℝ)|^4181 ≤ (22109900728729/50000000000000 : ℝ)^3157
        have hw : |(21600879/40000000 : ℝ)|=(21600879/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s4_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310623529/10000000000 : ℝ)*x 0 + (-1041916673/5000000000 : ℝ)*x 1 + (2700109867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310623529/10000000000 : ℝ)^4181 ≤ (8650159267919/20000000000000 : ℝ)^3157 := by
    have hnat : (5310623529 : ℕ)^4181*20000000000000^3157 ≤ 8650159267919^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310623529 10000000000 8650159267919 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041916673/5000000000 : ℝ)^4181 ≤ (3132350589113/25000000000000 : ℝ)^3157 := by
    have hnat : (1041916673 : ℕ)^4181*25000000000000^3157 ≤ 3132350589113^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041916673 5000000000 3132350589113 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700109867/5000000000 : ℝ)^4181 ≤ (8843960256789/20000000000000 : ℝ)^3157 := by
    have hnat : (2700109867 : ℕ)^4181*20000000000000^3157 ≤ 8843960256789^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700109867 5000000000 8843960256789 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310623529/10000000000 : ℝ), (-1041916673/5000000000 : ℝ), (2700109867/5000000000 : ℝ)] ![(8650159267919/20000000000000 : ℝ), (3132350589113/25000000000000 : ℝ), (8843960256789/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310623529/10000000000 : ℝ)|^4181 ≤ (8650159267919/20000000000000 : ℝ)^3157
        have hw : |(5310623529/10000000000 : ℝ)|=(5310623529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041916673/5000000000 : ℝ)|^4181 ≤ (3132350589113/25000000000000 : ℝ)^3157
        have hw : |(-1041916673/5000000000 : ℝ)|=(1041916673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700109867/5000000000 : ℝ)|^4181 ≤ (8843960256789/20000000000000 : ℝ)^3157
        have hw : |(2700109867/5000000000 : ℝ)|=(2700109867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s4_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310623467/10000000000 : ℝ)*x 0 + (1350054927/2500000000 : ℝ)*x 1 + (-1041916733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310623467/10000000000 : ℝ)^4181 ≤ (43250795670873/100000000000000 : ℝ)^3157 := by
    have hnat : (5310623467 : ℕ)^4181*100000000000000^3157 ≤ 43250795670873^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310623467 10000000000 43250795670873 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350054927/2500000000 : ℝ)^4181 ≤ (44219801001987/100000000000000 : ℝ)^3157 := by
    have hnat : (1350054927 : ℕ)^4181*100000000000000^3157 ≤ 44219801001987^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350054927 2500000000 44219801001987 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041916733/5000000000 : ℝ)^4181 ≤ (3132350828001/25000000000000 : ℝ)^3157 := by
    have hnat : (1041916733 : ℕ)^4181*25000000000000^3157 ≤ 3132350828001^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041916733 5000000000 3132350828001 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310623467/10000000000 : ℝ), (1350054927/2500000000 : ℝ), (-1041916733/5000000000 : ℝ)] ![(43250795670873/100000000000000 : ℝ), (44219801001987/100000000000000 : ℝ), (3132350828001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310623467/10000000000 : ℝ)|^4181 ≤ (43250795670873/100000000000000 : ℝ)^3157
        have hw : |(5310623467/10000000000 : ℝ)|=(5310623467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350054927/2500000000 : ℝ)|^4181 ≤ (44219801001987/100000000000000 : ℝ)^3157
        have hw : |(1350054927/2500000000 : ℝ)|=(1350054927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041916733/5000000000 : ℝ)|^4181 ≤ (3132350828001/25000000000000 : ℝ)^3157
        have hw : |(-1041916733/5000000000 : ℝ)|=(1041916733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s4_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218023731/500000000 : ℝ)*x 0 + (4504007993/10000000000 : ℝ)*x 1 + (4221492641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218023731/500000000 : ℝ)^4181 ≤ (33312977425101/100000000000000 : ℝ)^3157 := by
    have hnat : (218023731 : ℕ)^4181*100000000000000^3157 ≤ 33312977425101^3157*500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218023731 500000000 33312977425101 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504007993/10000000000 : ℝ)^4181 ≤ (434661408169/1250000000000 : ℝ)^3157 := by
    have hnat : (4504007993 : ℕ)^4181*1250000000000^3157 ≤ 434661408169^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504007993 10000000000 434661408169 1250000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221492641/10000000000 : ℝ)^4181 ≤ (7978527477451/25000000000000 : ℝ)^3157 := by
    have hnat : (4221492641 : ℕ)^4181*25000000000000^3157 ≤ 7978527477451^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221492641 10000000000 7978527477451 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218023731/500000000 : ℝ), (4504007993/10000000000 : ℝ), (4221492641/10000000000 : ℝ)] ![(33312977425101/100000000000000 : ℝ), (434661408169/1250000000000 : ℝ), (7978527477451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218023731/500000000 : ℝ)|^4181 ≤ (33312977425101/100000000000000 : ℝ)^3157
        have hw : |(218023731/500000000 : ℝ)|=(218023731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504007993/10000000000 : ℝ)|^4181 ≤ (434661408169/1250000000000 : ℝ)^3157
        have hw : |(4504007993/10000000000 : ℝ)|=(4504007993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221492641/10000000000 : ℝ)|^4181 ≤ (7978527477451/25000000000000 : ℝ)^3157
        have hw : |(4221492641/10000000000 : ℝ)|=(4221492641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5357/50000 : ℝ) ^ (8361/2048 : ℝ) ≤ (10958689762762719/100000000000000000000 : ℝ) := by
    have hpowers : (5357/50000 : ℝ)^8361 ≤ (10958689762762719/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5357 : ℕ)^8361*100000000000000000000^2048 ≤ 10958689762762719^2048*50000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5357 50000 10958689762762719 100000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5357/50000 : ℝ)) (X := (10958689762762719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7387/50000 : ℝ) ^ (8361/2048 : ℝ) ≤ (4068738241421573/10000000000000000000 : ℝ) := by
    have hpowers : (7387/50000 : ℝ)^8361 ≤ (4068738241421573/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7387 : ℕ)^8361*10000000000000000000^2048 ≤ 4068738241421573^2048*50000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7387 50000 4068738241421573 10000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7387/50000 : ℝ)) (X := (4068738241421573/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010958689762762719/50000000000000000000 : ℝ) ≤ (5000268407365353/5000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50010958689762762719/50000000000000000000 : ℝ)^2048 ≤ (5000268407365353/5000000000000000 : ℝ)^8361 := by
      have hnat : (50010958689762762719 : ℕ)^2048*5000000000000000^8361 ≤ 5000268407365353^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010958689762762719 50000000000000000000 5000268407365353 5000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268407365353/5000000000000000 : ℝ)) (X := (50010958689762762719/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051646072176978449/100000000000000000000 : ℝ) ≤ (10001264807308147/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (100051646072176978449/100000000000000000000 : ℝ)^2048 ≤ (10001264807308147/10000000000000000 : ℝ)^8361 := by
      have hnat : (100051646072176978449 : ℕ)^2048*10000000000000000^8361 ≤ 10001264807308147^8361*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051646072176978449 100000000000000000000 10001264807308147 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001264807308147/10000000000000000 : ℝ)) (X := (100051646072176978449/100000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5004068738241421573/5000000000000000000 : ℝ) ≤ (2500498199971397/2500000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (5004068738241421573/5000000000000000000 : ℝ)^2048 ≤ (2500498199971397/2500000000000000 : ℝ)^8361 := by
      have hnat : (5004068738241421573 : ℕ)^2048*2500000000000000^8361 ≤ 2500498199971397^8361*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5004068738241421573 5000000000000000000 2500498199971397 2500000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500498199971397/2500000000000000 : ℝ)) (X := (5004068738241421573/5000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10958689762762719/100000000000000000000 : ℝ) ≤ ((10146645010714315153/10150000000000000000 : ℝ)+2*(727992577441/406000000000000 : ℝ)*(5357/50000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (10146645010714315153/10150000000000000000 : ℝ)+2*(727992577441/406000000000000 : ℝ)*(5357/50000 : ℝ)=(5000268407365353/5000000000000000 : ℝ) by norm_num, show 1+2*(10958689762762719/100000000000000000000 : ℝ)=(50010958689762762719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4068738241421573/10000000000000000000 : ℝ)+(10958689762762719/100000000000000000000 : ℝ) ≤ ((10146645010714315153/10150000000000000000 : ℝ)+(727992577441/406000000000000 : ℝ)*((7387/50000 : ℝ)+(5357/50000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (10146645010714315153/10150000000000000000 : ℝ)+(727992577441/406000000000000 : ℝ)*((7387/50000 : ℝ)+(5357/50000 : ℝ))=(10001264807308147/10000000000000000 : ℝ) by norm_num, show 1+(4068738241421573/10000000000000000000 : ℝ)+(10958689762762719/100000000000000000000 : ℝ)=(100051646072176978449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4068738241421573/10000000000000000000 : ℝ) ≤ ((10146645010714315153/10150000000000000000 : ℝ)+2*(727992577441/406000000000000 : ℝ)*(7387/50000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (10146645010714315153/10150000000000000000 : ℝ)+2*(727992577441/406000000000000 : ℝ)*(7387/50000 : ℝ)=(2500498199971397/2500000000000000 : ℝ) by norm_num, show 1+2*(4068738241421573/10000000000000000000 : ℝ)=(5004068738241421573/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10146645010714315153/10150000000000000000 : ℝ)*(X 1 0+X 2 0)+(727992577441/406000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (10146645010714315153/10150000000000000000 : ℝ)) (alpha := (727992577441/406000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10146645010714315153/10150000000000000000 : ℝ)*(X 0 1+X 2 1)+(727992577441/406000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (10146645010714315153/10150000000000000000 : ℝ)) (alpha := (727992577441/406000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10146645010714315153/10150000000000000000 : ℝ)*(X 0 2+X 1 2)+(727992577441/406000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (10146645010714315153/10150000000000000000 : ℝ)) (alpha := (727992577441/406000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-538329211/2500000000 : ℝ)*X 0 0+(5400622567/10000000000 : ℝ)*X 0 1+(5258562191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346684497/10000000000 : ℝ)*X 1 0+(-1112745723/5000000000 : ℝ)*X 1 1+(2629280877/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534668479/1000000000 : ℝ)*X 2 0+(5258561191/10000000000 : ℝ)*X 2 1+(-2225491801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360460669/10000000000 : ℝ)*X 0 0+(4220686779/10000000000 : ℝ)*X 0 1+(4504810857/10000000000 : ℝ)*X 0 2+(4360460669/10000000000 : ℝ)*X 1 0+(4220686779/10000000000 : ℝ)*X 1 1+(4504810857/10000000000 : ℝ)*X 1 2+(4360460669/10000000000 : ℝ)*X 2 0+(4220686779/10000000000 : ℝ)*X 2 1+(4504810857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153324177/10000000000 : ℝ)*X 0 0+(5258963007/10000000000 : ℝ)*X 0 1+(21600879/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310623529/10000000000 : ℝ)*X 1 0+(-1041916673/5000000000 : ℝ)*X 1 1+(2700109867/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310623467/10000000000 : ℝ)*X 2 0+(1350054927/2500000000 : ℝ)*X 2 1+(-1041916733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218023731/500000000 : ℝ)*X 0 0+(4504007993/10000000000 : ℝ)*X 0 1+(4221492641/10000000000 : ℝ)*X 0 2+(218023731/500000000 : ℝ)*X 1 0+(4504007993/10000000000 : ℝ)*X 1 1+(4221492641/10000000000 : ℝ)*X 1 2+(218023731/500000000 : ℝ)*X 2 0+(4504007993/10000000000 : ℝ)*X 2 1+(4221492641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45627173703561648963244977/9062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131714363/50000000000000 : ℝ)*(base19) + (836030973/100000000000000 : ℝ)*(base23) + (121983/781250000000 : ℝ)*(lower2) + (91356147/50000000000000 : ℝ)*(lower3) + (169857829/100000000000000 : ℝ)*(lower4) + (1319856697702821/25000000000000 : ℝ)*(major0) + (1319856697702821/25000000000000 : ℝ)*(major1) + (1055885358162257/20000000000000 : ℝ)*(major2) + (3519626962783473/50000000000000 : ℝ)*(sp0) + (7039253662138221/100000000000000 : ℝ)*(sp1) + (1759809505067717/25000000000000 : ℝ)*(sp2) + (3519595883692959/100000000000000 : ℝ)*(sp3) + (3013853021/20000000000000 : ℝ)*(sp6) + (3604538569/100000000000000 : ℝ)*(sp7) + (439949936028941/12500000000000 : ℝ)*(f.failure) + (3519626962783473/50000000000000 : ℝ)*(f.sum) + (44407222829729/40600000000000000000000000000 : ℝ)*base65 + (1707944150008322137/253750000000000000000000000000000 : ℝ)*base68 + (1999981484195000321/203000000000000000000000000000000 : ℝ)*base69 + (682202082238322137/253750000000000000000000000000000 : ℝ)*base72 + (99688037278729/40600000000000000000000000000 : ℝ)*base73 + (1316482488248999679/203000000000000000000000000000000 : ℝ)*base76 + (2356695228789828387/253750000000000000000000000000000 : ℝ)*base78 + (3243495425414828387/253750000000000000000000000000000 : ℝ)*base80 + (26887774486511/5075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10660803/1250000000000000000000 : ℝ)*base89 + (10660803/1250000000000000000000 : ℝ)*base91 + (1839197/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (229302688054927661299853421/72500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115105549/10000000000000 : ℝ)*(base19) + (58576399/5000000000000 : ℝ)*(base23) + (40121867/50000000000000 : ℝ)*(upper2) + (2089187/6250000000000 : ℝ)*(upper3) + (37297453/25000000000000 : ℝ)*(upper5) + (5309468579601767/100000000000000 : ℝ)*(major0) + (5309468579601767/100000000000000 : ℝ)*(major1) + (5309468579601767/100000000000000 : ℝ)*(major2) + (17108331817/50000000000000 : ℝ)*(sp1) + (27150625891/100000000000000 : ℝ)*(sp2) + (110614215795261/1562500000000 : ℝ)*(sp4) + (353963722158879/5000000000000 : ℝ)*(sp5) + (3539640744371417/50000000000000 : ℝ)*(sp6) + (221226702680019/6250000000000 : ℝ)*(sp7) + (221226702680019/6250000000000 : ℝ)*(f.failure) + (110614215795261/1562500000000 : ℝ)*(f.sum) + (1122981580479/2900000000000000000000000000 : ℝ)*base66 + (10384069238592807/145000000000000000000000000000000 : ℝ)*base68 + (267776961481407193/145000000000000000000000000000000 : ℝ)*base69 + (86106529051407193/145000000000000000000000000000000 : ℝ)*base71 + (294130807121/2900000000000000000000000000 : ℝ)*base73 + (519103466861407193/145000000000000000000000000000000 : ℝ)*base75 + (69631418801407193/145000000000000000000000000000000 : ℝ)*base77 + (336451329363592807/145000000000000000000000000000000 : ℝ)*base80 + (1897480685779/2900000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4704877/625000000000000000000 : ℝ)*base89 + (4704877/625000000000000000000 : ℝ)*base91 + (4704877/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1169_s5_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153897211/10000000000 : ℝ)*x 0 + (1348552909/2500000000 : ℝ)*x 1 + (5264591969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153897211/10000000000 : ℝ)^4181 ≤ (6545167804419/50000000000000 : ℝ)^3157 := by
    have hnat : (2153897211 : ℕ)^4181*50000000000000^3157 ≤ 6545167804419^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153897211 10000000000 6545167804419 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348552909/2500000000 : ℝ)^4181 ≤ (8830931602641/20000000000000 : ℝ)^3157 := by
    have hnat : (1348552909 : ℕ)^4181*20000000000000^3157 ≤ 8830931602641^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348552909 2500000000 8830931602641 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264591969/10000000000 : ℝ)^4181 ≤ (21377503183659/50000000000000 : ℝ)^3157 := by
    have hnat : (5264591969 : ℕ)^4181*50000000000000^3157 ≤ 21377503183659^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264591969 10000000000 21377503183659 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153897211/10000000000 : ℝ), (1348552909/2500000000 : ℝ), (5264591969/10000000000 : ℝ)] ![(6545167804419/50000000000000 : ℝ), (8830931602641/20000000000000 : ℝ), (21377503183659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153897211/10000000000 : ℝ)|^4181 ≤ (6545167804419/50000000000000 : ℝ)^3157
        have hw : |(-2153897211/10000000000 : ℝ)|=(2153897211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348552909/2500000000 : ℝ)|^4181 ≤ (8830931602641/20000000000000 : ℝ)^3157
        have hw : |(1348552909/2500000000 : ℝ)|=(1348552909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264591969/10000000000 : ℝ)|^4181 ≤ (21377503183659/50000000000000 : ℝ)^3157
        have hw : |(5264591969/10000000000 : ℝ)|=(5264591969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s5_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668134063/1250000000 : ℝ)*x 0 + (-2219659209/10000000000 : ℝ)*x 1 + (5264592103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668134063/1250000000 : ℝ)^4181 ≤ (43622747969831/100000000000000 : ℝ)^3157 := by
    have hnat : (668134063 : ℕ)^4181*100000000000000^3157 ≤ 43622747969831^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668134063 1250000000 43622747969831 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219659209/10000000000 : ℝ)^4181 ≤ (2724448840913/20000000000000 : ℝ)^3157 := by
    have hnat : (2219659209 : ℕ)^4181*20000000000000^3157 ≤ 2724448840913^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219659209 10000000000 2724448840913 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264592103/10000000000 : ℝ)^4181 ≤ (21377503904273/50000000000000 : ℝ)^3157 := by
    have hnat : (5264592103 : ℕ)^4181*50000000000000^3157 ≤ 21377503904273^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264592103 10000000000 21377503904273 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668134063/1250000000 : ℝ), (-2219659209/10000000000 : ℝ), (5264592103/10000000000 : ℝ)] ![(43622747969831/100000000000000 : ℝ), (2724448840913/20000000000000 : ℝ), (21377503904273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668134063/1250000000 : ℝ)|^4181 ≤ (43622747969831/100000000000000 : ℝ)^3157
        have hw : |(668134063/1250000000 : ℝ)|=(668134063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2219659209/10000000000 : ℝ)|^4181 ≤ (2724448840913/20000000000000 : ℝ)^3157
        have hw : |(-2219659209/10000000000 : ℝ)|=(2219659209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264592103/10000000000 : ℝ)|^4181 ≤ (21377503904273/50000000000000 : ℝ)^3157
        have hw : |(5264592103/10000000000 : ℝ)|=(5264592103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s5_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336268203/2500000000 : ℝ)*x 0 + (5264592181/10000000000 : ℝ)*x 1 + (-277457337/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336268203/2500000000 : ℝ)^4181 ≤ (21811375649423/50000000000000 : ℝ)^3157 := by
    have hnat : (1336268203 : ℕ)^4181*50000000000000^3157 ≤ 21811375649423^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336268203 2500000000 21811375649423 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264592181/10000000000 : ℝ)^4181 ≤ (42755008647469/100000000000000 : ℝ)^3157 := by
    have hnat : (5264592181 : ℕ)^4181*100000000000000^3157 ≤ 42755008647469^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264592181 10000000000 42755008647469 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277457337/1250000000 : ℝ)^4181 ≤ (3405560008763/25000000000000 : ℝ)^3157 := by
    have hnat : (277457337 : ℕ)^4181*25000000000000^3157 ≤ 3405560008763^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277457337 1250000000 3405560008763 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336268203/2500000000 : ℝ), (5264592181/10000000000 : ℝ), (-277457337/1250000000 : ℝ)] ![(21811375649423/50000000000000 : ℝ), (42755008647469/100000000000000 : ℝ), (3405560008763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336268203/2500000000 : ℝ)|^4181 ≤ (21811375649423/50000000000000 : ℝ)^3157
        have hw : |(1336268203/2500000000 : ℝ)|=(1336268203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264592181/10000000000 : ℝ)|^4181 ≤ (42755008647469/100000000000000 : ℝ)^3157
        have hw : |(5264592181/10000000000 : ℝ)|=(5264592181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277457337/1250000000 : ℝ)|^4181 ≤ (3405560008763/25000000000000 : ℝ)^3157
        have hw : |(-277457337/1250000000 : ℝ)|=(277457337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s5_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360800313/10000000000 : ℝ)*x 0 + (211654221/500000000 : ℝ)*x 1 + (1123081243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360800313/10000000000 : ℝ)^4181 ≤ (8329068188863/25000000000000 : ℝ)^3157 := by
    have hnat : (4360800313 : ℕ)^4181*25000000000000^3157 ≤ 8329068188863^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360800313 10000000000 8329068188863 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211654221/500000000 : ℝ)^4181 ≤ (32030218838749/100000000000000 : ℝ)^3157 := by
    have hnat : (211654221 : ℕ)^4181*100000000000000^3157 ≤ 32030218838749^3157*500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211654221 500000000 32030218838749 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123081243/2500000000 : ℝ)^4181 ≤ (17326754197517/50000000000000 : ℝ)^3157 := by
    have hnat : (1123081243 : ℕ)^4181*50000000000000^3157 ≤ 17326754197517^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123081243 2500000000 17326754197517 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360800313/10000000000 : ℝ), (211654221/500000000 : ℝ), (1123081243/2500000000 : ℝ)] ![(8329068188863/25000000000000 : ℝ), (32030218838749/100000000000000 : ℝ), (17326754197517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360800313/10000000000 : ℝ)|^4181 ≤ (8329068188863/25000000000000 : ℝ)^3157
        have hw : |(4360800313/10000000000 : ℝ)|=(4360800313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211654221/500000000 : ℝ)|^4181 ≤ (32030218838749/100000000000000 : ℝ)^3157
        have hw : |(211654221/500000000 : ℝ)|=(211654221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123081243/2500000000 : ℝ)|^4181 ≤ (17326754197517/50000000000000 : ℝ)^3157
        have hw : |(1123081243/2500000000 : ℝ)|=(1123081243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s5_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153901759/10000000000 : ℝ)*x 0 + (32905791/62500000 : ℝ)*x 1 + (539387629/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153901759/10000000000 : ℝ)^4181 ≤ (6545186107407/50000000000000 : ℝ)^3157 := by
    have hnat : (2153901759 : ℕ)^4181*50000000000000^3157 ≤ 6545186107407^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153901759 10000000000 6545186107407 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32905791/62500000 : ℝ)^4181 ≤ (42758605075037/100000000000000 : ℝ)^3157 := by
    have hnat : (32905791 : ℕ)^4181*100000000000000^3157 ≤ 42758605075037^3157*62500000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32905791 62500000 42758605075037 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539387629/1000000000 : ℝ)^4181 ≤ (22075511345617/50000000000000 : ℝ)^3157 := by
    have hnat : (539387629 : ℕ)^4181*50000000000000^3157 ≤ 22075511345617^3157*1000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539387629 1000000000 22075511345617 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153901759/10000000000 : ℝ), (32905791/62500000 : ℝ), (539387629/1000000000 : ℝ)] ![(6545186107407/50000000000000 : ℝ), (42758605075037/100000000000000 : ℝ), (22075511345617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153901759/10000000000 : ℝ)|^4181 ≤ (6545186107407/50000000000000 : ℝ)^3157
        have hw : |(-2153901759/10000000000 : ℝ)|=(2153901759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32905791/62500000 : ℝ)|^4181 ≤ (42758605075037/100000000000000 : ℝ)^3157
        have hw : |(32905791/62500000 : ℝ)|=(32905791/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539387629/1000000000 : ℝ)|^4181 ≤ (22075511345617/50000000000000 : ℝ)^3157
        have hw : |(539387629/1000000000 : ℝ)|=(539387629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s5_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664021053/1250000000 : ℝ)*x 0 + (-1045187393/5000000000 : ℝ)*x 1 + (5393876223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664021053/1250000000 : ℝ)^4181 ≤ (21633730061919/50000000000000 : ℝ)^3157 := by
    have hnat : (664021053 : ℕ)^4181*50000000000000^3157 ≤ 21633730061919^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664021053 1250000000 21633730061919 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045187393/5000000000 : ℝ)^4181 ≤ (12581517892459/100000000000000 : ℝ)^3157 := by
    have hnat : (1045187393 : ℕ)^4181*100000000000000^3157 ≤ 12581517892459^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045187393 5000000000 12581517892459 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393876223/10000000000 : ℝ)^4181 ≤ (344929859101/781250000000 : ℝ)^3157 := by
    have hnat : (5393876223 : ℕ)^4181*781250000000^3157 ≤ 344929859101^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393876223 10000000000 344929859101 781250000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664021053/1250000000 : ℝ), (-1045187393/5000000000 : ℝ), (5393876223/10000000000 : ℝ)] ![(21633730061919/50000000000000 : ℝ), (12581517892459/100000000000000 : ℝ), (344929859101/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664021053/1250000000 : ℝ)|^4181 ≤ (21633730061919/50000000000000 : ℝ)^3157
        have hw : |(664021053/1250000000 : ℝ)|=(664021053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045187393/5000000000 : ℝ)|^4181 ≤ (12581517892459/100000000000000 : ℝ)^3157
        have hw : |(-1045187393/5000000000 : ℝ)|=(1045187393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393876223/10000000000 : ℝ)|^4181 ≤ (344929859101/781250000000 : ℝ)^3157
        have hw : |(5393876223/10000000000 : ℝ)|=(5393876223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s5_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312168439/10000000000 : ℝ)*x 0 + (1078775249/2000000000 : ℝ)*x 1 + (-2090374737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312168439/10000000000 : ℝ)^4181 ≤ (43267460285641/100000000000000 : ℝ)^3157 := by
    have hnat : (5312168439 : ℕ)^4181*100000000000000^3157 ≤ 43267460285641^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312168439 10000000000 43267460285641 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078775249/2000000000 : ℝ)^4181 ≤ (5518877775427/12500000000000 : ℝ)^3157 := by
    have hnat : (1078775249 : ℕ)^4181*12500000000000^3157 ≤ 5518877775427^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078775249 2000000000 5518877775427 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090374737/10000000000 : ℝ)^4181 ≤ (12581517501879/100000000000000 : ℝ)^3157 := by
    have hnat : (2090374737 : ℕ)^4181*100000000000000^3157 ≤ 12581517501879^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090374737 10000000000 12581517501879 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312168439/10000000000 : ℝ), (1078775249/2000000000 : ℝ), (-2090374737/10000000000 : ℝ)] ![(43267460285641/100000000000000 : ℝ), (5518877775427/12500000000000 : ℝ), (12581517501879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312168439/10000000000 : ℝ)|^4181 ≤ (43267460285641/100000000000000 : ℝ)^3157
        have hw : |(5312168439/10000000000 : ℝ)|=(5312168439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078775249/2000000000 : ℝ)|^4181 ≤ (5518877775427/12500000000000 : ℝ)^3157
        have hw : |(1078775249/2000000000 : ℝ)|=(1078775249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090374737/10000000000 : ℝ)|^4181 ≤ (12581517501879/100000000000000 : ℝ)^3157
        have hw : |(-2090374737/10000000000 : ℝ)|=(2090374737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s5_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360810387/10000000000 : ℝ)*x 0 + (561457111/1250000000 : ℝ)*x 1 + (4233755303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360810387/10000000000 : ℝ)^4181 ≤ (6663274936897/20000000000000 : ℝ)^3157 := by
    have hnat : (4360810387 : ℕ)^4181*20000000000000^3157 ≤ 6663274936897^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360810387 10000000000 6663274936897 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561457111/1250000000 : ℝ)^4181 ≤ (4330835425223/12500000000000 : ℝ)^3157 := by
    have hnat : (561457111 : ℕ)^4181*12500000000000^3157 ≤ 4330835425223^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561457111 1250000000 4330835425223 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233755303/10000000000 : ℝ)^4181 ≤ (1601847094569/5000000000000 : ℝ)^3157 := by
    have hnat : (4233755303 : ℕ)^4181*5000000000000^3157 ≤ 1601847094569^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233755303 10000000000 1601847094569 5000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360810387/10000000000 : ℝ), (561457111/1250000000 : ℝ), (4233755303/10000000000 : ℝ)] ![(6663274936897/20000000000000 : ℝ), (4330835425223/12500000000000 : ℝ), (1601847094569/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360810387/10000000000 : ℝ)|^4181 ≤ (6663274936897/20000000000000 : ℝ)^3157
        have hw : |(4360810387/10000000000 : ℝ)|=(4360810387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561457111/1250000000 : ℝ)|^4181 ≤ (4330835425223/12500000000000 : ℝ)^3157
        have hw : |(561457111/1250000000 : ℝ)|=(561457111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233755303/10000000000 : ℝ)|^4181 ≤ (1601847094569/5000000000000 : ℝ)^3157
        have hw : |(4233755303/10000000000 : ℝ)|=(4233755303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5613/50000 : ℝ) ^ (8361/2048 : ℝ) ≤ (13259439524676097/100000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^8361 ≤ (13259439524676097/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5613 : ℕ)^8361*100000000000000000000^2048 ≤ 13259439524676097^2048*50000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 13259439524676097 100000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (13259439524676097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8361/2048 : ℝ) ≤ (6989897050610051/20000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8361 ≤ (6989897050610051/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8361*20000000000000000000^2048 ≤ 6989897050610051^2048*50000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 6989897050610051 20000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (6989897050610051/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013259439524676097/50000000000000000000 : ℝ) ≤ (10000649506372199/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50013259439524676097/50000000000000000000 : ℝ)^2048 ≤ (10000649506372199/10000000000000000 : ℝ)^8361 := by
      have hnat : (50013259439524676097 : ℕ)^2048*10000000000000000^8361 ≤ 10000649506372199^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013259439524676097 50000000000000000000 10000649506372199 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000649506372199/10000000000000000 : ℝ)) (X := (50013259439524676097/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253013057798607897/6250000000000000000 : ℝ) ≤ (2500295161803789/2500000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (6253013057798607897/6250000000000000000 : ℝ)^2048 ≤ (2500295161803789/2500000000000000 : ℝ)^8361 := by
      have hnat : (6253013057798607897 : ℕ)^2048*2500000000000000^8361 ≤ 2500295161803789^8361*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253013057798607897 6250000000000000000 2500295161803789 2500000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500295161803789/2500000000000000 : ℝ)) (X := (6253013057798607897/6250000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006989897050610051/10000000000000000000 : ℝ) ≤ (10001711788058113/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (10006989897050610051/10000000000000000000 : ℝ)^2048 ≤ (10001711788058113/10000000000000000 : ℝ)^8361 := by
      have hnat : (10006989897050610051 : ℕ)^2048*10000000000000000^8361 ≤ 10001711788058113^8361*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006989897050610051 10000000000000000000 10001711788058113 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001711788058113/10000000000000000 : ℝ)) (X := (10006989897050610051/10000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13259439524676097/100000000000000000000 : ℝ) ≤ ((7517507135240376007/7520000000000000000 : ℝ)+2*(531140842957/300800000000000 : ℝ)*(5613/50000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (7517507135240376007/7520000000000000000 : ℝ)+2*(531140842957/300800000000000 : ℝ)*(5613/50000 : ℝ)=(10000649506372199/10000000000000000 : ℝ) by norm_num, show 1+2*(13259439524676097/100000000000000000000 : ℝ)=(50013259439524676097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6989897050610051/20000000000000000000 : ℝ)+(13259439524676097/100000000000000000000 : ℝ) ≤ ((7517507135240376007/7520000000000000000 : ℝ)+(531140842957/300800000000000 : ℝ)*((7117/50000 : ℝ)+(5613/50000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (7517507135240376007/7520000000000000000 : ℝ)+(531140842957/300800000000000 : ℝ)*((7117/50000 : ℝ)+(5613/50000 : ℝ))=(2500295161803789/2500000000000000 : ℝ) by norm_num, show 1+(6989897050610051/20000000000000000000 : ℝ)+(13259439524676097/100000000000000000000 : ℝ)=(6253013057798607897/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6989897050610051/20000000000000000000 : ℝ) ≤ ((7517507135240376007/7520000000000000000 : ℝ)+2*(531140842957/300800000000000 : ℝ)*(7117/50000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (7517507135240376007/7520000000000000000 : ℝ)+2*(531140842957/300800000000000 : ℝ)*(7117/50000 : ℝ)=(10001711788058113/10000000000000000 : ℝ) by norm_num, show 1+2*(6989897050610051/20000000000000000000 : ℝ)=(10006989897050610051/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7517507135240376007/7520000000000000000 : ℝ)*(X 1 0+X 2 0)+(531140842957/300800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7517507135240376007/7520000000000000000 : ℝ)) (alpha := (531140842957/300800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7517507135240376007/7520000000000000000 : ℝ)*(X 0 1+X 2 1)+(531140842957/300800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7517507135240376007/7520000000000000000 : ℝ)) (alpha := (531140842957/300800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7517507135240376007/7520000000000000000 : ℝ)*(X 0 2+X 1 2)+(531140842957/300800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7517507135240376007/7520000000000000000 : ℝ)) (alpha := (531140842957/300800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2153897211/10000000000 : ℝ)*X 0 0+(1348552909/2500000000 : ℝ)*X 0 1+(5264591969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668134063/1250000000 : ℝ)*X 1 0+(-2219659209/10000000000 : ℝ)*X 1 1+(5264592103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336268203/2500000000 : ℝ)*X 2 0+(5264592181/10000000000 : ℝ)*X 2 1+(-277457337/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360800313/10000000000 : ℝ)*X 0 0+(211654221/500000000 : ℝ)*X 0 1+(1123081243/2500000000 : ℝ)*X 0 2+(4360800313/10000000000 : ℝ)*X 1 0+(211654221/500000000 : ℝ)*X 1 1+(1123081243/2500000000 : ℝ)*X 1 2+(4360800313/10000000000 : ℝ)*X 2 0+(211654221/500000000 : ℝ)*X 2 1+(1123081243/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153901759/10000000000 : ℝ)*X 0 0+(32905791/62500000 : ℝ)*X 0 1+(539387629/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664021053/1250000000 : ℝ)*X 1 0+(-1045187393/5000000000 : ℝ)*X 1 1+(5393876223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312168439/10000000000 : ℝ)*X 2 0+(1078775249/2000000000 : ℝ)*X 2 1+(-2090374737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360810387/10000000000 : ℝ)*X 0 0+(561457111/1250000000 : ℝ)*X 0 1+(4233755303/10000000000 : ℝ)*X 0 2+(4360810387/10000000000 : ℝ)*X 1 0+(561457111/1250000000 : ℝ)*X 1 1+(4233755303/10000000000 : ℝ)*X 1 2+(4360810387/10000000000 : ℝ)*X 2 0+(561457111/1250000000 : ℝ)*X 2 1+(4233755303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (583229723239367059021743981/94000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2486966549/100000000000000 : ℝ)*(base19) + (1168597481/50000000000000 : ℝ)*(base23) + (191033327/100000000000000 : ℝ)*(upper3) + (79419061/25000000000000 : ℝ)*(upper4) + (653929883/100000000000000 : ℝ)*(upper5) + (2893121383870761/50000000000000 : ℝ)*(major0) + (2893121383870761/50000000000000 : ℝ)*(major1) + (5786242767741523/100000000000000 : ℝ)*(major2) + (7714925973729277/100000000000000 : ℝ)*(sp0) + (1543001559844561/20000000000000 : ℝ)*(sp1) + (964375993624299/12500000000000 : ℝ)*(sp2) + (964362497481283/25000000000000 : ℝ)*(sp3) + (42156230039/50000000000000 : ℝ)*(sp4) + (3131568687/12500000000000 : ℝ)*(sp7) + (1928737521237313/50000000000000 : ℝ)*(f.failure) + (3857505143094677/50000000000000 : ℝ)*(f.sum) + (19808885603091/6016000000000000000000000000 : ℝ)*base66 + (3249461547962881173/376000000000000000000000000000000 : ℝ)*base68 + (415966875279311339/752000000000000000000000000000000 : ℝ)*base70 + (3953906665210881173/376000000000000000000000000000000 : ℝ)*base72 + (288010807819/240640000000000000000000000 : ℝ)*base74 + (10284705949456688661/752000000000000000000000000000000 : ℝ)*base75 + (3902046561331843673/376000000000000000000000000000000 : ℝ)*base78 + (8154219006099843673/376000000000000000000000000000000 : ℝ)*base80 + (7019610565077/7520000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (21183921/5000000000000000000000 : ℝ)*base90 + (21183921/5000000000000000000000 : ℝ)*base92 + (71183921/5000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3027518327934225114508523493/376000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (701739883/50000000000000 : ℝ)*(base19) + (100886341/6250000000000 : ℝ)*(base23) + (155487289/100000000000000 : ℝ)*(upper3) + (72911621/100000000000000 : ℝ)*(lower4) + (123762863/100000000000000 : ℝ)*(upper5) + (5816202807297611/100000000000000 : ℝ)*(major0) + (5816202807297611/100000000000000 : ℝ)*(major1) + (5816202807297611/100000000000000 : ℝ)*(major2) + (33957353157/100000000000000 : ℝ)*(sp1) + (8455883849/20000000000000 : ℝ)*(sp2) + (7754957048279903/100000000000000 : ℝ)*(sp4) + (7754921687446981/100000000000000 : ℝ)*(sp5) + (7754913154679203/100000000000000 : ℝ)*(sp6) + (3877448297918293/100000000000000 : ℝ)*(sp7) + (3877448297918293/100000000000000 : ℝ)*(f.failure) + (7754957048279903/100000000000000 : ℝ)*(f.sum) + (73861014334833/15040000000000000000000000000 : ℝ)*base66 + (7338656167642005723/752000000000000000000000000000000 : ℝ)*base68 + (10492605669962005723/752000000000000000000000000000000 : ℝ)*base70 + (12648796330090005723/752000000000000000000000000000000 : ℝ)*base72 + (2037468631473/15040000000000000000000000000 : ℝ)*base74 + (5558096022090005723/752000000000000000000000000000000 : ℝ)*base76 + (7538744254810005723/752000000000000000000000000000000 : ℝ)*base78 + (10712302932442005723/752000000000000000000000000000000 : ℝ)*base80 + (28279265790193/15040000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (120023419/10000000000000000000000 : ℝ)*base89 + (120023419/10000000000000000000000 : ℝ)*base91 + (120023419/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1169_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16423/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1169_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1169_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1169_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16423/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1169_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
