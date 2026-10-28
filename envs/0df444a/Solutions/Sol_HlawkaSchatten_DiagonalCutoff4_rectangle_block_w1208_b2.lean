-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1208_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:06:16.739889+00:00
-- url     : https://prove2.me/submissions/ebf97008-0d53-4d26-ab1a-11b494d22d87

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
theorem support_rectangle_w1208_s6_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135698089/10000000000 : ℝ)*x 0 + (2696033053/5000000000 : ℝ)*x 1 + (2633259509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135698089/10000000000 : ℝ)^8401 ≤ (12983906409313/100000000000000 : ℝ)^6353 := by
    have hnat : (2135698089 : ℕ)^8401*100000000000000^6353 ≤ 12983906409313^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135698089 10000000000 12983906409313 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696033053/5000000000 : ℝ)^8401 ≤ (44185709776461/100000000000000 : ℝ)^6353 := by
    have hnat : (2696033053 : ℕ)^8401*100000000000000^6353 ≤ 44185709776461^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696033053 5000000000 44185709776461 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633259509/5000000000 : ℝ)^8401 ≤ (10707595951011/25000000000000 : ℝ)^6353 := by
    have hnat : (2633259509 : ℕ)^8401*25000000000000^6353 ≤ 10707595951011^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633259509 5000000000 10707595951011 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135698089/10000000000 : ℝ), (2696033053/5000000000 : ℝ), (2633259509/5000000000 : ℝ)] ![(12983906409313/100000000000000 : ℝ), (44185709776461/100000000000000 : ℝ), (10707595951011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135698089/10000000000 : ℝ)|^8401 ≤ (12983906409313/100000000000000 : ℝ)^6353
        have hw : |(-2135698089/10000000000 : ℝ)|=(2135698089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696033053/5000000000 : ℝ)|^8401 ≤ (44185709776461/100000000000000 : ℝ)^6353
        have hw : |(2696033053/5000000000 : ℝ)|=(2696033053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633259509/5000000000 : ℝ)|^8401 ≤ (10707595951011/25000000000000 : ℝ)^6353
        have hw : |(2633259509/5000000000 : ℝ)|=(2633259509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s6_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344539261/10000000000 : ℝ)*x 0 + (-219936497/1000000000 : ℝ)*x 1 + (2633259501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344539261/10000000000 : ℝ)^8401 ≤ (349371443631/800000000000 : ℝ)^6353 := by
    have hnat : (5344539261 : ℕ)^8401*800000000000^6353 ≤ 349371443631^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344539261 10000000000 349371443631 800000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219936497/1000000000 : ℝ)^8401 ≤ (13498185897493/100000000000000 : ℝ)^6353 := by
    have hnat : (219936497 : ℕ)^8401*100000000000000^6353 ≤ 13498185897493^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219936497 1000000000 13498185897493 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633259501/5000000000 : ℝ)^8401 ≤ (5353797953997/12500000000000 : ℝ)^6353 := by
    have hnat : (2633259501 : ℕ)^8401*12500000000000^6353 ≤ 5353797953997^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633259501 5000000000 5353797953997 12500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344539261/10000000000 : ℝ), (-219936497/1000000000 : ℝ), (2633259501/5000000000 : ℝ)] ![(349371443631/800000000000 : ℝ), (13498185897493/100000000000000 : ℝ), (5353797953997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344539261/10000000000 : ℝ)|^8401 ≤ (349371443631/800000000000 : ℝ)^6353
        have hw : |(5344539261/10000000000 : ℝ)|=(5344539261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219936497/1000000000 : ℝ)|^8401 ≤ (13498185897493/100000000000000 : ℝ)^6353
        have hw : |(-219936497/1000000000 : ℝ)|=(219936497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633259501/5000000000 : ℝ)|^8401 ≤ (5353797953997/12500000000000 : ℝ)^6353
        have hw : |(2633259501/5000000000 : ℝ)|=(2633259501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s6_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344539247/10000000000 : ℝ)*x 0 + (2633259503/5000000000 : ℝ)*x 1 + (-274920623/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344539247/10000000000 : ℝ)^8401 ≤ (218357151513/500000000000 : ℝ)^6353 := by
    have hnat : (5344539247 : ℕ)^8401*500000000000^6353 ≤ 218357151513^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344539247 10000000000 218357151513 500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633259503/5000000000 : ℝ)^8401 ≤ (42830383674993/100000000000000 : ℝ)^6353 := by
    have hnat : (2633259503 : ℕ)^8401*100000000000000^6353 ≤ 42830383674993^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633259503 5000000000 42830383674993 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274920623/1250000000 : ℝ)^8401 ≤ (6749093005557/50000000000000 : ℝ)^6353 := by
    have hnat : (274920623 : ℕ)^8401*50000000000000^6353 ≤ 6749093005557^6353*1250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274920623 1250000000 6749093005557 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344539247/10000000000 : ℝ), (2633259503/5000000000 : ℝ), (-274920623/1250000000 : ℝ)] ![(218357151513/500000000000 : ℝ), (42830383674993/100000000000000 : ℝ), (6749093005557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344539247/10000000000 : ℝ)|^8401 ≤ (218357151513/500000000000 : ℝ)^6353
        have hw : |(5344539247/10000000000 : ℝ)|=(5344539247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633259503/5000000000 : ℝ)|^8401 ≤ (42830383674993/100000000000000 : ℝ)^6353
        have hw : |(2633259503/5000000000 : ℝ)|=(2633259503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274920623/1250000000 : ℝ)|^8401 ≤ (6749093005557/50000000000000 : ℝ)^6353
        have hw : |(-274920623/1250000000 : ℝ)|=(274920623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s6_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871089123/2000000000 : ℝ)*x 0 + (4230740833/10000000000 : ℝ)*x 1 + (4483751059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871089123/2000000000 : ℝ)^8401 ≤ (520581227017/1562500000000 : ℝ)^6353 := by
    have hnat : (871089123 : ℕ)^8401*1562500000000^6353 ≤ 520581227017^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871089123 2000000000 520581227017 1562500000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230740833/10000000000 : ℝ)^8401 ≤ (8015401278589/25000000000000 : ℝ)^6353 := by
    have hnat : (4230740833 : ℕ)^8401*25000000000000^6353 ≤ 8015401278589^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230740833 10000000000 8015401278589 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483751059/10000000000 : ℝ)^8401 ≤ (2163824771269/6250000000000 : ℝ)^6353 := by
    have hnat : (4483751059 : ℕ)^8401*6250000000000^6353 ≤ 2163824771269^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483751059 10000000000 2163824771269 6250000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871089123/2000000000 : ℝ), (4230740833/10000000000 : ℝ), (4483751059/10000000000 : ℝ)] ![(520581227017/1562500000000 : ℝ), (8015401278589/25000000000000 : ℝ), (2163824771269/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871089123/2000000000 : ℝ)|^8401 ≤ (520581227017/1562500000000 : ℝ)^6353
        have hw : |(871089123/2000000000 : ℝ)|=(871089123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230740833/10000000000 : ℝ)|^8401 ≤ (8015401278589/25000000000000 : ℝ)^6353
        have hw : |(4230740833/10000000000 : ℝ)|=(4230740833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483751059/10000000000 : ℝ)|^8401 ≤ (2163824771269/6250000000000 : ℝ)^6353
        have hw : |(4483751059/10000000000 : ℝ)|=(4483751059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s6_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266962861/1250000000 : ℝ)*x 0 + (5266836383/10000000000 : ℝ)*x 1 + (215669903/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266962861/1250000000 : ℝ)^8401 ≤ (3245986247469/25000000000000 : ℝ)^6353 := by
    have hnat : (266962861 : ℕ)^8401*25000000000000^6353 ≤ 3245986247469^6353*1250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266962861 1250000000 3245986247469 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266836383/10000000000 : ℝ)^8401 ≤ (42833796862187/100000000000000 : ℝ)^6353 := by
    have hnat : (5266836383 : ℕ)^8401*100000000000000^6353 ≤ 42833796862187^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266836383 10000000000 42833796862187 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215669903/400000000 : ℝ)^8401 ≤ (11045564532459/25000000000000 : ℝ)^6353 := by
    have hnat : (215669903 : ℕ)^8401*25000000000000^6353 ≤ 11045564532459^6353*400000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215669903 400000000 11045564532459 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266962861/1250000000 : ℝ), (5266836383/10000000000 : ℝ), (215669903/400000000 : ℝ)] ![(3245986247469/25000000000000 : ℝ), (42833796862187/100000000000000 : ℝ), (11045564532459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266962861/1250000000 : ℝ)|^8401 ≤ (3245986247469/25000000000000 : ℝ)^6353
        have hw : |(-266962861/1250000000 : ℝ)|=(266962861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266836383/10000000000 : ℝ)|^8401 ≤ (42833796862187/100000000000000 : ℝ)^6353
        have hw : |(5266836383/10000000000 : ℝ)|=(5266836383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215669903/400000000 : ℝ)|^8401 ≤ (11045564532459/25000000000000 : ℝ)^6353
        have hw : |(215669903/400000000 : ℝ)|=(215669903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s6_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328145009/2500000000 : ℝ)*x 0 + (-2074136381/10000000000 : ℝ)*x 1 + (1078349523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328145009/2500000000 : ℝ)^8401 ≤ (21663216395641/50000000000000 : ℝ)^6353 := by
    have hnat : (1328145009 : ℕ)^8401*50000000000000^6353 ≤ 21663216395641^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328145009 2500000000 21663216395641 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074136381/10000000000 : ℝ)^8401 ≤ (12491308626481/100000000000000 : ℝ)^6353 := by
    have hnat : (2074136381 : ℕ)^8401*100000000000000^6353 ≤ 12491308626481^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074136381 10000000000 12491308626481 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078349523/2000000000 : ℝ)^8401 ≤ (44182258563277/100000000000000 : ℝ)^6353 := by
    have hnat : (1078349523 : ℕ)^8401*100000000000000^6353 ≤ 44182258563277^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078349523 2000000000 44182258563277 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328145009/2500000000 : ℝ), (-2074136381/10000000000 : ℝ), (1078349523/2000000000 : ℝ)] ![(21663216395641/50000000000000 : ℝ), (12491308626481/100000000000000 : ℝ), (44182258563277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328145009/2500000000 : ℝ)|^8401 ≤ (21663216395641/50000000000000 : ℝ)^6353
        have hw : |(1328145009/2500000000 : ℝ)|=(1328145009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074136381/10000000000 : ℝ)|^8401 ≤ (12491308626481/100000000000000 : ℝ)^6353
        have hw : |(-2074136381/10000000000 : ℝ)|=(2074136381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078349523/2000000000 : ℝ)|^8401 ≤ (44182258563277/100000000000000 : ℝ)^6353
        have hw : |(1078349523/2000000000 : ℝ)|=(1078349523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s6_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312580013/10000000000 : ℝ)*x 0 + (1347936909/2500000000 : ℝ)*x 1 + (-2074136383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312580013/10000000000 : ℝ)^8401 ≤ (43326432543239/100000000000000 : ℝ)^6353 := by
    have hnat : (5312580013 : ℕ)^8401*100000000000000^6353 ≤ 43326432543239^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312580013 10000000000 43326432543239 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347936909/2500000000 : ℝ)^8401 ≤ (22091129395417/50000000000000 : ℝ)^6353 := by
    have hnat : (1347936909 : ℕ)^8401*50000000000000^6353 ≤ 22091129395417^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347936909 2500000000 22091129395417 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074136383/10000000000 : ℝ)^8401 ≤ (12491308642409/100000000000000 : ℝ)^6353 := by
    have hnat : (2074136383 : ℕ)^8401*100000000000000^6353 ≤ 12491308642409^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074136383 10000000000 12491308642409 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312580013/10000000000 : ℝ), (1347936909/2500000000 : ℝ), (-2074136383/10000000000 : ℝ)] ![(43326432543239/100000000000000 : ℝ), (22091129395417/50000000000000 : ℝ), (12491308642409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312580013/10000000000 : ℝ)|^8401 ≤ (43326432543239/100000000000000 : ℝ)^6353
        have hw : |(5312580013/10000000000 : ℝ)|=(5312580013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347936909/2500000000 : ℝ)|^8401 ≤ (22091129395417/50000000000000 : ℝ)^6353
        have hw : |(1347936909/2500000000 : ℝ)|=(1347936909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074136383/10000000000 : ℝ)|^8401 ≤ (12491308642409/100000000000000 : ℝ)^6353
        have hw : |(-2074136383/10000000000 : ℝ)|=(2074136383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s6_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355455311/10000000000 : ℝ)*x 0 + (896622293/2000000000 : ℝ)*x 1 + (2115691349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355455311/10000000000 : ℝ)^8401 ≤ (33317296609159/100000000000000 : ℝ)^6353 := by
    have hnat : (4355455311 : ℕ)^8401*100000000000000^6353 ≤ 33317296609159^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355455311 10000000000 33317296609159 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896622293/2000000000 : ℝ)^8401 ≤ (216341661439/625000000000 : ℝ)^6353 := by
    have hnat : (896622293 : ℕ)^8401*625000000000^6353 ≤ 216341661439^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896622293 2000000000 216341661439 625000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115691349/5000000000 : ℝ)^8401 ≤ (8017009386881/25000000000000 : ℝ)^6353 := by
    have hnat : (2115691349 : ℕ)^8401*25000000000000^6353 ≤ 8017009386881^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115691349 5000000000 8017009386881 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355455311/10000000000 : ℝ), (896622293/2000000000 : ℝ), (2115691349/5000000000 : ℝ)] ![(33317296609159/100000000000000 : ℝ), (216341661439/625000000000 : ℝ), (8017009386881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355455311/10000000000 : ℝ)|^8401 ≤ (33317296609159/100000000000000 : ℝ)^6353
        have hw : |(4355455311/10000000000 : ℝ)|=(4355455311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896622293/2000000000 : ℝ)|^8401 ≤ (216341661439/625000000000 : ℝ)^6353
        have hw : |(896622293/2000000000 : ℝ)|=(896622293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115691349/5000000000 : ℝ)|^8401 ≤ (8017009386881/25000000000000 : ℝ)^6353
        have hw : |(2115691349/5000000000 : ℝ)|=(2115691349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1429/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (713/6250 : ℝ) ^ (525/128 : ℝ) ≤ (13585821090727711/100000000000000000000 : ℝ) := by
    have hpowers : (713/6250 : ℝ)^525 ≤ (13585821090727711/100000000000000000000 : ℝ)^128 := by
      have hnat : (713 : ℕ)^525*100000000000000000000^128 ≤ 13585821090727711^128*6250^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        713 6250 13585821090727711 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (713/6250 : ℝ)) (X := (13585821090727711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (525/128 : ℝ) ≤ (32545368117855247/100000000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^525 ≤ (32545368117855247/100000000000000000000 : ℝ)^128 := by
      have hnat : (3529 : ℕ)^525*100000000000000000000^128 ≤ 32545368117855247^128*25000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 32545368117855247 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (32545368117855247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013585821090727711/50000000000000000000 : ℝ) ≤ (10000662402466263/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50013585821090727711/50000000000000000000 : ℝ)^128 ≤ (10000662402466263/10000000000000000 : ℝ)^525 := by
      have hnat : (50013585821090727711 : ℕ)^128*10000000000000000^525 ≤ 10000662402466263^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013585821090727711 50000000000000000000 10000662402466263 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000662402466263/10000000000000000 : ℝ)) (X := (50013585821090727711/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023065594604291479/50000000000000000000 : ℝ) ≤ (2000224905241291/2000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50023065594604291479/50000000000000000000 : ℝ)^128 ≤ (2000224905241291/2000000000000000 : ℝ)^525 := by
      have hnat : (50023065594604291479 : ℕ)^128*2000000000000000^525 ≤ 2000224905241291^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023065594604291479 50000000000000000000 2000224905241291 2000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224905241291/2000000000000000 : ℝ)) (X := (50023065594604291479/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032545368117855247/50000000000000000000 : ℝ) ≤ (10001586649946647/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50032545368117855247/50000000000000000000 : ℝ)^128 ≤ (10001586649946647/10000000000000000 : ℝ)^525 := by
      have hnat : (50032545368117855247 : ℕ)^128*10000000000000000^525 ≤ 10001586649946647^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032545368117855247 50000000000000000000 10001586649946647 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001586649946647/10000000000000000 : ℝ)) (X := (50032545368117855247/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13585821090727711/100000000000000000000 : ℝ) ≤ ((6767812492655604883/6770000000000000000 : ℝ)+2*(14441366881/8462500000000 : ℝ)*(713/6250 : ℝ))^(525/128 : ℝ) := by
    rw [show (6767812492655604883/6770000000000000000 : ℝ)+2*(14441366881/8462500000000 : ℝ)*(713/6250 : ℝ)=(10000662402466263/10000000000000000 : ℝ) by norm_num, show 1+2*(13585821090727711/100000000000000000000 : ℝ)=(50013585821090727711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32545368117855247/100000000000000000000 : ℝ)+(13585821090727711/100000000000000000000 : ℝ) ≤ ((6767812492655604883/6770000000000000000 : ℝ)+(14441366881/8462500000000 : ℝ)*((3529/25000 : ℝ)+(713/6250 : ℝ)))^(525/128 : ℝ) := by
    rw [show (6767812492655604883/6770000000000000000 : ℝ)+(14441366881/8462500000000 : ℝ)*((3529/25000 : ℝ)+(713/6250 : ℝ))=(2000224905241291/2000000000000000 : ℝ) by norm_num, show 1+(32545368117855247/100000000000000000000 : ℝ)+(13585821090727711/100000000000000000000 : ℝ)=(50023065594604291479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32545368117855247/100000000000000000000 : ℝ) ≤ ((6767812492655604883/6770000000000000000 : ℝ)+2*(14441366881/8462500000000 : ℝ)*(3529/25000 : ℝ))^(525/128 : ℝ) := by
    rw [show (6767812492655604883/6770000000000000000 : ℝ)+2*(14441366881/8462500000000 : ℝ)*(3529/25000 : ℝ)=(10001586649946647/10000000000000000 : ℝ) by norm_num, show 1+2*(32545368117855247/100000000000000000000 : ℝ)=(50032545368117855247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6767812492655604883/6770000000000000000 : ℝ)*(X 1 0+X 2 0)+(14441366881/8462500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (6767812492655604883/6770000000000000000 : ℝ)) (alpha := (14441366881/8462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6767812492655604883/6770000000000000000 : ℝ)*(X 0 1+X 2 1)+(14441366881/8462500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (6767812492655604883/6770000000000000000 : ℝ)) (alpha := (14441366881/8462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6767812492655604883/6770000000000000000 : ℝ)*(X 0 2+X 1 2)+(14441366881/8462500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (6767812492655604883/6770000000000000000 : ℝ)) (alpha := (14441366881/8462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2135698089/10000000000 : ℝ)*X 0 0+(2696033053/5000000000 : ℝ)*X 0 1+(2633259509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344539261/10000000000 : ℝ)*X 1 0+(-219936497/1000000000 : ℝ)*X 1 1+(2633259501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344539247/10000000000 : ℝ)*X 2 0+(2633259503/5000000000 : ℝ)*X 2 1+(-274920623/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871089123/2000000000 : ℝ)*X 0 0+(4230740833/10000000000 : ℝ)*X 0 1+(4483751059/10000000000 : ℝ)*X 0 2+(871089123/2000000000 : ℝ)*X 1 0+(4230740833/10000000000 : ℝ)*X 1 1+(4483751059/10000000000 : ℝ)*X 1 2+(871089123/2000000000 : ℝ)*X 2 0+(4230740833/10000000000 : ℝ)*X 2 1+(4483751059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-266962861/1250000000 : ℝ)*X 0 0+(5266836383/10000000000 : ℝ)*X 0 1+(215669903/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328145009/2500000000 : ℝ)*X 1 0+(-2074136381/10000000000 : ℝ)*X 1 1+(1078349523/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312580013/10000000000 : ℝ)*X 2 0+(1347936909/2500000000 : ℝ)*X 2 1+(-2074136383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355455311/10000000000 : ℝ)*X 0 0+(896622293/2000000000 : ℝ)*X 0 1+(2115691349/5000000000 : ℝ)*X 0 2+(4355455311/10000000000 : ℝ)*X 1 0+(896622293/2000000000 : ℝ)*X 1 1+(2115691349/5000000000 : ℝ)*X 1 2+(4355455311/10000000000 : ℝ)*X 2 0+(896622293/2000000000 : ℝ)*X 2 1+(2115691349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132646899966421188325180563/21156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (297174411/25000000000000 : ℝ)*(base19) + (1089215387/100000000000000 : ℝ)*(base23) + (42017399/100000000000000 : ℝ)*(lower2) + (78933289/50000000000000 : ℝ)*(upper3) + (36933979/50000000000000 : ℝ)*(upper5) + (744852963716487/12500000000000 : ℝ)*(major0) + (744852963716487/12500000000000 : ℝ)*(major1) + (744852963716487/12500000000000 : ℝ)*(major2) + (7965173286874317/100000000000000 : ℝ)*(sp0) + (398260170274091/5000000000000 : ℝ)*(sp1) + (7965203504964077/100000000000000 : ℝ)*(sp2) + (1976212482518719/50000000000000 : ℝ)*(sp3) + (7826826287/25000000000000 : ℝ)*(sp4) + (17651251269/100000000000000 : ℝ)*(sp7) + (1976221308144353/50000000000000 : ℝ)*(f.failure) + (995650574272433/12500000000000 : ℝ)*(f.sum) + (1031848993239/423125000000000000000000000 : ℝ)*base66 + (1130250979198218979/84625000000000000000000000000000 : ℝ)*base68 + (687676038728843979/84625000000000000000000000000000 : ℝ)*base70 + (861956287429218979/84625000000000000000000000000000 : ℝ)*base72 + (6092079851493/3385000000000000000000000000 : ℝ)*base73 + (1045239244556093979/84625000000000000000000000000000 : ℝ)*base76 + (48617598280406021/84625000000000000000000000000000 : ℝ)*base77 + (311127368592218979/84625000000000000000000000000000 : ℝ)*base80 + (3624254447213/846250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (62989349/5000000000000000000000 : ℝ)*base90 + (62989349/5000000000000000000000 : ℝ)*base92 + (62989349/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18902521608973926860967/1692500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1971213707/100000000000000 : ℝ)*(base19) + (2130804241/100000000000000 : ℝ)*(base23) + (121209679/50000000000000 : ℝ)*(upper3) + (1083889/1250000000000 : ℝ)*(lower4) + (111178111/50000000000000 : ℝ)*(upper5) + (5989106813113769/100000000000000 : ℝ)*(major0) + (5989106813113769/100000000000000 : ℝ)*(major1) + (5989106813113769/100000000000000 : ℝ)*(major2) + (6967141809/12500000000000 : ℝ)*(sp1) + (3044773519/5000000000000 : ℝ)*(sp2) + (8005684084642483/100000000000000 : ℝ)*(sp4) + (1601125275258861/20000000000000 : ℝ)*(sp5) + (8005621058367863/100000000000000 : ℝ)*(sp6) + (496566146163119/12500000000000 : ℝ)*(sp7) + (496566146163119/12500000000000 : ℝ)*(f.failure) + (8005684084642483/100000000000000 : ℝ)*(f.sum) + (2017396444721/423125000000000000000000000 : ℝ)*base66 + (1009102642930865973/677000000000000000000000000000000 : ℝ)*base68 + (12459801828365134027/677000000000000000000000000000000 : ℝ)*base69 + (7345461514205865973/677000000000000000000000000000000 : ℝ)*base72 + (9058059396437/3385000000000000000000000000 : ℝ)*base73 + (3738795610827134027/677000000000000000000000000000000 : ℝ)*base75 + (4750741153244865973/677000000000000000000000000000000 : ℝ)*base78 + (7171220264426134027/677000000000000000000000000000000 : ℝ)*base79 + (6287543821817/3385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9774027/1250000000000000000000 : ℝ)*base90 + (9774027/1250000000000000000000 : ℝ)*base92 + (9774027/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1208_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1208_s7_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-533928637/2500000000 : ℝ)*x 0 + (3369897/6250000 : ℝ)*x 1 + (2633369689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533928637/2500000000 : ℝ)^8401 ≤ (12984038728137/100000000000000 : ℝ)^6353 := by
    have hnat : (533928637 : ℕ)^8401*100000000000000^6353 ≤ 12984038728137^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533928637 2500000000 12984038728137 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3369897/6250000 : ℝ)^8401 ≤ (44183207640081/100000000000000 : ℝ)^6353 := by
    have hnat : (3369897 : ℕ)^8401*100000000000000^6353 ≤ 44183207640081^6353*6250000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3369897 6250000 44183207640081 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633369689/5000000000 : ℝ)^8401 ≤ (42832753628251/100000000000000 : ℝ)^6353 := by
    have hnat : (2633369689 : ℕ)^8401*100000000000000^6353 ≤ 42832753628251^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633369689 5000000000 42832753628251 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533928637/2500000000 : ℝ), (3369897/6250000 : ℝ), (2633369689/5000000000 : ℝ)] ![(12984038728137/100000000000000 : ℝ), (44183207640081/100000000000000 : ℝ), (42832753628251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533928637/2500000000 : ℝ)|^8401 ≤ (12984038728137/100000000000000 : ℝ)^6353
        have hw : |(-533928637/2500000000 : ℝ)|=(533928637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3369897/6250000 : ℝ)|^8401 ≤ (44183207640081/100000000000000 : ℝ)^6353
        have hw : |(3369897/6250000 : ℝ)|=(3369897/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633369689/5000000000 : ℝ)|^8401 ≤ (42832753628251/100000000000000 : ℝ)^6353
        have hw : |(2633369689/5000000000 : ℝ)|=(2633369689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s7_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344482131/10000000000 : ℝ)*x 0 + (-2199149811/10000000000 : ℝ)*x 1 + (5266738771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344482131/10000000000 : ℝ)^8401 ≤ (43670813144673/100000000000000 : ℝ)^6353 := by
    have hnat : (5344482131 : ℕ)^8401*100000000000000^6353 ≤ 43670813144673^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344482131 10000000000 43670813144673 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199149811/10000000000 : ℝ)^8401 ≤ (674821987103/5000000000000 : ℝ)^6353 := by
    have hnat : (2199149811 : ℕ)^8401*5000000000000^6353 ≤ 674821987103^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199149811 10000000000 674821987103 5000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266738771/10000000000 : ℝ)^8401 ≤ (42832747100329/100000000000000 : ℝ)^6353 := by
    have hnat : (5266738771 : ℕ)^8401*100000000000000^6353 ≤ 42832747100329^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266738771 10000000000 42832747100329 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344482131/10000000000 : ℝ), (-2199149811/10000000000 : ℝ), (5266738771/10000000000 : ℝ)] ![(43670813144673/100000000000000 : ℝ), (674821987103/5000000000000 : ℝ), (42832747100329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344482131/10000000000 : ℝ)|^8401 ≤ (43670813144673/100000000000000 : ℝ)^6353
        have hw : |(5344482131/10000000000 : ℝ)|=(5344482131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2199149811/10000000000 : ℝ)|^8401 ≤ (674821987103/5000000000000 : ℝ)^6353
        have hw : |(-2199149811/10000000000 : ℝ)|=(2199149811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266738771/10000000000 : ℝ)|^8401 ≤ (42832747100329/100000000000000 : ℝ)^6353
        have hw : |(5266738771/10000000000 : ℝ)|=(5266738771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s7_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068896383/2000000000 : ℝ)*x 0 + (5266738737/10000000000 : ℝ)*x 1 + (-2199150143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068896383/2000000000 : ℝ)^8401 ≤ (43670810810723/100000000000000 : ℝ)^6353 := by
    have hnat : (1068896383 : ℕ)^8401*100000000000000^6353 ≤ 43670810810723^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068896383 2000000000 43670810810723 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266738737/10000000000 : ℝ)^8401 ≤ (42832746734679/100000000000000 : ℝ)^6353 := by
    have hnat : (5266738737 : ℕ)^8401*100000000000000^6353 ≤ 42832746734679^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266738737 10000000000 42832746734679 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199150143/10000000000 : ℝ)^8401 ≤ (6748221218207/50000000000000 : ℝ)^6353 := by
    have hnat : (2199150143 : ℕ)^8401*50000000000000^6353 ≤ 6748221218207^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199150143 10000000000 6748221218207 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068896383/2000000000 : ℝ), (5266738737/10000000000 : ℝ), (-2199150143/10000000000 : ℝ)] ![(43670810810723/100000000000000 : ℝ), (42832746734679/100000000000000 : ℝ), (6748221218207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068896383/2000000000 : ℝ)|^8401 ≤ (43670810810723/100000000000000 : ℝ)^6353
        have hw : |(1068896383/2000000000 : ℝ)|=(1068896383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266738737/10000000000 : ℝ)|^8401 ≤ (42832746734679/100000000000000 : ℝ)^6353
        have hw : |(5266738737/10000000000 : ℝ)|=(5266738737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2199150143/10000000000 : ℝ)|^8401 ≤ (6748221218207/50000000000000 : ℝ)^6353
        have hw : |(-2199150143/10000000000 : ℝ)|=(2199150143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s7_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355456379/10000000000 : ℝ)*x 0 + (423119337/1000000000 : ℝ)*x 1 + (2241648119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355456379/10000000000 : ℝ)^8401 ≤ (16658653706269/50000000000000 : ℝ)^6353 := by
    have hnat : (4355456379 : ℕ)^8401*50000000000000^6353 ≤ 16658653706269^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355456379 10000000000 16658653706269 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423119337/1000000000 : ℝ)^8401 ≤ (4008267521157/12500000000000 : ℝ)^6353 := by
    have hnat : (423119337 : ℕ)^8401*12500000000000^6353 ≤ 4008267521157^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423119337 1000000000 4008267521157 12500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241648119/5000000000 : ℝ)^8401 ≤ (17308276202741/50000000000000 : ℝ)^6353 := by
    have hnat : (2241648119 : ℕ)^8401*50000000000000^6353 ≤ 17308276202741^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241648119 5000000000 17308276202741 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355456379/10000000000 : ℝ), (423119337/1000000000 : ℝ), (2241648119/5000000000 : ℝ)] ![(16658653706269/50000000000000 : ℝ), (4008267521157/12500000000000 : ℝ), (17308276202741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355456379/10000000000 : ℝ)|^8401 ≤ (16658653706269/50000000000000 : ℝ)^6353
        have hw : |(4355456379/10000000000 : ℝ)|=(4355456379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423119337/1000000000 : ℝ)|^8401 ≤ (4008267521157/12500000000000 : ℝ)^6353
        have hw : |(423119337/1000000000 : ℝ)|=(423119337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241648119/5000000000 : ℝ)|^8401 ≤ (17308276202741/50000000000000 : ℝ)^6353
        have hw : |(2241648119/5000000000 : ℝ)|=(2241648119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s7_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135719527/10000000000 : ℝ)*x 0 + (5267054103/10000000000 : ℝ)*x 1 + (2695759573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135719527/10000000000 : ℝ)^8401 ≤ (405752461121/3125000000000 : ℝ)^6353 := by
    have hnat : (2135719527 : ℕ)^8401*3125000000000^6353 ≤ 405752461121^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135719527 10000000000 405752461121 3125000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267054103/10000000000 : ℝ)^8401 ≤ (1338629323133/3125000000000 : ℝ)^6353 := by
    have hnat : (5267054103 : ℕ)^8401*3125000000000^6353 ≤ 1338629323133^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267054103 10000000000 1338629323133 3125000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695759573/5000000000 : ℝ)^8401 ≤ (44179782881603/100000000000000 : ℝ)^6353 := by
    have hnat : (2695759573 : ℕ)^8401*100000000000000^6353 ≤ 44179782881603^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695759573 5000000000 44179782881603 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135719527/10000000000 : ℝ), (5267054103/10000000000 : ℝ), (2695759573/5000000000 : ℝ)] ![(405752461121/3125000000000 : ℝ), (1338629323133/3125000000000 : ℝ), (44179782881603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135719527/10000000000 : ℝ)|^8401 ≤ (405752461121/3125000000000 : ℝ)^6353
        have hw : |(-2135719527/10000000000 : ℝ)|=(2135719527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267054103/10000000000 : ℝ)|^8401 ≤ (1338629323133/3125000000000 : ℝ)^6353
        have hw : |(5267054103/10000000000 : ℝ)|=(5267054103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695759573/5000000000 : ℝ)|^8401 ≤ (44179782881603/100000000000000 : ℝ)^6353
        have hw : |(2695759573/5000000000 : ℝ)|=(2695759573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s7_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312637397/10000000000 : ℝ)*x 0 + (-2074369243/10000000000 : ℝ)*x 1 + (2695759691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312637397/10000000000 : ℝ)^8401 ≤ (43327051401439/100000000000000 : ℝ)^6353 := by
    have hnat : (5312637397 : ℕ)^8401*100000000000000^6353 ≤ 43327051401439^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312637397 10000000000 43327051401439 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074369243/10000000000 : ℝ)^8401 ≤ (12493163136743/100000000000000 : ℝ)^6353 := by
    have hnat : (2074369243 : ℕ)^8401*100000000000000^6353 ≤ 12493163136743^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074369243 10000000000 12493163136743 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695759691/5000000000 : ℝ)^8401 ≤ (44179785438873/100000000000000 : ℝ)^6353 := by
    have hnat : (2695759691 : ℕ)^8401*100000000000000^6353 ≤ 44179785438873^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695759691 5000000000 44179785438873 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312637397/10000000000 : ℝ), (-2074369243/10000000000 : ℝ), (2695759691/5000000000 : ℝ)] ![(43327051401439/100000000000000 : ℝ), (12493163136743/100000000000000 : ℝ), (44179785438873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312637397/10000000000 : ℝ)|^8401 ≤ (43327051401439/100000000000000 : ℝ)^6353
        have hw : |(5312637397/10000000000 : ℝ)|=(5312637397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074369243/10000000000 : ℝ)|^8401 ≤ (12493163136743/100000000000000 : ℝ)^6353
        have hw : |(-2074369243/10000000000 : ℝ)|=(2074369243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695759691/5000000000 : ℝ)|^8401 ≤ (44179785438873/100000000000000 : ℝ)^6353
        have hw : |(2695759691/5000000000 : ℝ)|=(2695759691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s7_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212505481/400000000 : ℝ)*x 0 + (5391519683/10000000000 : ℝ)*x 1 + (-1037184669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212505481/400000000 : ℝ)^8401 ≤ (10831761847399/25000000000000 : ℝ)^6353 := by
    have hnat : (212505481 : ℕ)^8401*25000000000000^6353 ≤ 10831761847399^6353*400000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212505481 400000000 10831761847399 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391519683/10000000000 : ℝ)^8401 ≤ (1767191548019/4000000000000 : ℝ)^6353 := by
    have hnat : (5391519683 : ℕ)^8401*4000000000000^6353 ≤ 1767191548019^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391519683 10000000000 1767191548019 4000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037184669/5000000000 : ℝ)^8401 ≤ (2498632778667/20000000000000 : ℝ)^6353 := by
    have hnat : (1037184669 : ℕ)^8401*20000000000000^6353 ≤ 2498632778667^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037184669 5000000000 2498632778667 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212505481/400000000 : ℝ), (5391519683/10000000000 : ℝ), (-1037184669/5000000000 : ℝ)] ![(10831761847399/25000000000000 : ℝ), (1767191548019/4000000000000 : ℝ), (2498632778667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212505481/400000000 : ℝ)|^8401 ≤ (10831761847399/25000000000000 : ℝ)^6353
        have hw : |(212505481/400000000 : ℝ)|=(212505481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391519683/10000000000 : ℝ)|^8401 ≤ (1767191548019/4000000000000 : ℝ)^6353
        have hw : |(5391519683/10000000000 : ℝ)|=(5391519683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037184669/5000000000 : ℝ)|^8401 ≤ (2498632778667/20000000000000 : ℝ)^6353
        have hw : |(-1037184669/5000000000 : ℝ)|=(1037184669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s7_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177733393/5000000000 : ℝ)*x 0 + (4482660569/10000000000 : ℝ)*x 1 + (169273219/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177733393/5000000000 : ℝ)^8401 ≤ (3331741268483/10000000000000 : ℝ)^6353 := by
    have hnat : (2177733393 : ℕ)^8401*10000000000000^6353 ≤ 3331741268483^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177733393 5000000000 3331741268483 10000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482660569/10000000000 : ℝ)^8401 ≤ (34610062182579/100000000000000 : ℝ)^6353 := by
    have hnat : (4482660569 : ℕ)^8401*100000000000000^6353 ≤ 34610062182579^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482660569 10000000000 34610062182579 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169273219/400000000 : ℝ)^8401 ≤ (2004532819949/6250000000000 : ℝ)^6353 := by
    have hnat : (169273219 : ℕ)^8401*6250000000000^6353 ≤ 2004532819949^6353*400000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169273219 400000000 2004532819949 6250000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177733393/5000000000 : ℝ), (4482660569/10000000000 : ℝ), (169273219/400000000 : ℝ)] ![(3331741268483/10000000000000 : ℝ), (34610062182579/100000000000000 : ℝ), (2004532819949/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177733393/5000000000 : ℝ)|^8401 ≤ (3331741268483/10000000000000 : ℝ)^6353
        have hw : |(2177733393/5000000000 : ℝ)|=(2177733393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482660569/10000000000 : ℝ)|^8401 ≤ (34610062182579/100000000000000 : ℝ)^6353
        have hw : |(4482660569/10000000000 : ℝ)|=(4482660569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169273219/400000000 : ℝ)|^8401 ≤ (2004532819949/6250000000000 : ℝ)^6353
        have hw : |(169273219/400000000 : ℝ)|=(169273219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11437/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1429/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1429/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1429/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1429/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1429/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1429/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1429/12500 : ℝ) ^ (525/128 : ℝ) ≤ (6851716814357971/50000000000000000000 : ℝ) := by
    have hpowers : (1429/12500 : ℝ)^525 ≤ (6851716814357971/50000000000000000000 : ℝ)^128 := by
      have hnat : (1429 : ℕ)^525*50000000000000000000^128 ≤ 6851716814357971^128*12500^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1429 12500 6851716814357971 50000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1429/12500 : ℝ)) (X := (6851716814357971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3523/25000 : ℝ) ^ (525/128 : ℝ) ≤ (51710418653581/160000000000000000 : ℝ) := by
    have hpowers : (3523/25000 : ℝ)^525 ≤ (51710418653581/160000000000000000 : ℝ)^128 := by
      have hnat : (3523 : ℕ)^525*160000000000000000^128 ≤ 51710418653581^128*25000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523 25000 51710418653581 160000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3523/25000 : ℝ)) (X := (51710418653581/160000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006851716814357971/25000000000000000000 : ℝ) ≤ (10000668136294453/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (25006851716814357971/25000000000000000000 : ℝ)^128 ≤ (10000668136294453/10000000000000000 : ℝ)^525 := by
      have hnat : (25006851716814357971 : ℕ)^128*10000000000000000^525 ≤ 10000668136294453^525*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006851716814357971 25000000000000000000 10000668136294453 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668136294453/10000000000000000 : ℝ)) (X := (25006851716814357971/25000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046022445287204067/100000000000000000000 : ℝ) ≤ (5000560937924747/5000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (100046022445287204067/100000000000000000000 : ℝ)^128 ≤ (5000560937924747/5000000000000000 : ℝ)^525 := by
      have hnat : (100046022445287204067 : ℕ)^128*5000000000000000^525 ≤ 5000560937924747^525*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046022445287204067 100000000000000000000 5000560937924747 5000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000560937924747/5000000000000000 : ℝ)) (X := (100046022445287204067/100000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (80051710418653581/80000000000000000 : ℝ) ≤ (2000315123080907/2000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (80051710418653581/80000000000000000 : ℝ)^128 ≤ (2000315123080907/2000000000000000 : ℝ)^525 := by
      have hnat : (80051710418653581 : ℕ)^128*2000000000000000^525 ≤ 2000315123080907^525*80000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80051710418653581 80000000000000000 2000315123080907 2000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000315123080907/2000000000000000 : ℝ)) (X := (80051710418653581/80000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6851716814357971/50000000000000000000 : ℝ) ≤ ((6647850735339196889/6650000000000000000 : ℝ)+2*(453739555041/266000000000000 : ℝ)*(1429/12500 : ℝ))^(525/128 : ℝ) := by
    rw [show (6647850735339196889/6650000000000000000 : ℝ)+2*(453739555041/266000000000000 : ℝ)*(1429/12500 : ℝ)=(10000668136294453/10000000000000000 : ℝ) by norm_num, show 1+2*(6851716814357971/50000000000000000000 : ℝ)=(25006851716814357971/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51710418653581/160000000000000000 : ℝ)+(6851716814357971/50000000000000000000 : ℝ) ≤ ((6647850735339196889/6650000000000000000 : ℝ)+(453739555041/266000000000000 : ℝ)*((3523/25000 : ℝ)+(1429/12500 : ℝ)))^(525/128 : ℝ) := by
    rw [show (6647850735339196889/6650000000000000000 : ℝ)+(453739555041/266000000000000 : ℝ)*((3523/25000 : ℝ)+(1429/12500 : ℝ))=(5000560937924747/5000000000000000 : ℝ) by norm_num, show 1+(51710418653581/160000000000000000 : ℝ)+(6851716814357971/50000000000000000000 : ℝ)=(100046022445287204067/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51710418653581/160000000000000000 : ℝ) ≤ ((6647850735339196889/6650000000000000000 : ℝ)+2*(453739555041/266000000000000 : ℝ)*(3523/25000 : ℝ))^(525/128 : ℝ) := by
    rw [show (6647850735339196889/6650000000000000000 : ℝ)+2*(453739555041/266000000000000 : ℝ)*(3523/25000 : ℝ)=(2000315123080907/2000000000000000 : ℝ) by norm_num, show 1+2*(51710418653581/160000000000000000 : ℝ)=(80051710418653581/80000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6647850735339196889/6650000000000000000 : ℝ)*(X 1 0+X 2 0)+(453739555041/266000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (6647850735339196889/6650000000000000000 : ℝ)) (alpha := (453739555041/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6647850735339196889/6650000000000000000 : ℝ)*(X 0 1+X 2 1)+(453739555041/266000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (6647850735339196889/6650000000000000000 : ℝ)) (alpha := (453739555041/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6647850735339196889/6650000000000000000 : ℝ)*(X 0 2+X 1 2)+(453739555041/266000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (6647850735339196889/6650000000000000000 : ℝ)) (alpha := (453739555041/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-533928637/2500000000 : ℝ)*X 0 0+(3369897/6250000 : ℝ)*X 0 1+(2633369689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344482131/10000000000 : ℝ)*X 1 0+(-2199149811/10000000000 : ℝ)*X 1 1+(5266738771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068896383/2000000000 : ℝ)*X 2 0+(5266738737/10000000000 : ℝ)*X 2 1+(-2199150143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355456379/10000000000 : ℝ)*X 0 0+(423119337/1000000000 : ℝ)*X 0 1+(2241648119/5000000000 : ℝ)*X 0 2+(4355456379/10000000000 : ℝ)*X 1 0+(423119337/1000000000 : ℝ)*X 1 1+(2241648119/5000000000 : ℝ)*X 1 2+(4355456379/10000000000 : ℝ)*X 2 0+(423119337/1000000000 : ℝ)*X 2 1+(2241648119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2135719527/10000000000 : ℝ)*X 0 0+(5267054103/10000000000 : ℝ)*X 0 1+(2695759573/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312637397/10000000000 : ℝ)*X 1 0+(-2074369243/10000000000 : ℝ)*X 1 1+(2695759691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212505481/400000000 : ℝ)*X 2 0+(5391519683/10000000000 : ℝ)*X 2 1+(-1037184669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177733393/5000000000 : ℝ)*X 0 0+(4482660569/10000000000 : ℝ)*X 0 1+(169273219/400000000 : ℝ)*X 0 2+(2177733393/5000000000 : ℝ)*X 1 0+(4482660569/10000000000 : ℝ)*X 1 1+(169273219/400000000 : ℝ)*X 1 2+(2177733393/5000000000 : ℝ)*X 2 0+(4482660569/10000000000 : ℝ)*X 2 1+(169273219/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (663373335683161504935193341/166250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (339539551/50000000000000 : ℝ)*(base19) + (984721/50000000000000 : ℝ)*(base23) + (28035113/50000000000000 : ℝ)*(upper2) + (3276037/2000000000000 : ℝ)*(lower3) + (26177061/20000000000000 : ℝ)*(upper4) + (2990133109875977/50000000000000 : ℝ)*(major0) + (2990133109875977/50000000000000 : ℝ)*(major1) + (2990133109875977/50000000000000 : ℝ)*(major2) + (799386703578293/10000000000000 : ℝ)*(sp0) + (1998466589175957/25000000000000 : ℝ)*(sp1) + (1998457777621363/25000000000000 : ℝ)*(sp2) + (396665256000027/10000000000000 : ℝ)*(sp3) + (7184665607/20000000000000 : ℝ)*(sp6) + (6355356757/50000000000000 : ℝ)*(sp7) + (495833158839223/12500000000000 : ℝ)*(f.failure) + (799386703578293/10000000000000 : ℝ)*(f.sum) + (10873832234957/6650000000000000000000000000 : ℝ)*base65 + (798216508869339447/332500000000000000000000000000000 : ℝ)*base68 + (2082774434450660553/332500000000000000000000000000000 : ℝ)*base69 + (3108257078839339447/332500000000000000000000000000000 : ℝ)*base72 + (23337527144357/6650000000000000000000000000 : ℝ)*base73 + (4011108899990660553/332500000000000000000000000000000 : ℝ)*base75 + (5456677257983160553/332500000000000000000000000000000 : ℝ)*base77 + (878105173988160553/332500000000000000000000000000000 : ℝ)*base79 + (14903664072457/6650000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5623059/1250000000000000000000 : ℝ)*base90 + (5623059/1250000000000000000000 : ℝ)*base92 + (5623059/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112529261412941973583881/13300000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468810467/20000000000000 : ℝ)*(base19) + (1781693277/100000000000000 : ℝ)*(base23) + (470091/6250000000000 : ℝ)*(upper2) + (369870583/100000000000000 : ℝ)*(upper3) + (23922159/12500000000000 : ℝ)*(upper5) + (6010566216251851/100000000000000 : ℝ)*(major0) + (6010566216251851/100000000000000 : ℝ)*(major1) + (6010566216251851/100000000000000 : ℝ)*(major2) + (36062994741/50000000000000 : ℝ)*(sp1) + (69800626623/100000000000000 : ℝ)*(sp2) + (401718456083413/5000000000000 : ℝ)*(sp4) + (8034294651626443/100000000000000 : ℝ)*(sp5) + (200857438483709/2500000000000 : ℝ)*(sp6) + (797352605761443/20000000000000 : ℝ)*(sp7) + (797352605761443/20000000000000 : ℝ)*(f.failure) + (401718456083413/5000000000000 : ℝ)*(f.sum) + (2915944629891/13300000000000000000000000000 : ℝ)*base65 + (4638883686603033461/665000000000000000000000000000000 : ℝ)*base68 + (264983821653033461/665000000000000000000000000000000 : ℝ)*base70 + (559919912123033461/665000000000000000000000000000000 : ℝ)*base72 + (22351543003691/13300000000000000000000000000 : ℝ)*base73 + (4129117826966539/665000000000000000000000000000000 : ℝ)*base75 + (237270761596966539/665000000000000000000000000000000 : ℝ)*base77 + (3923992636481966539/665000000000000000000000000000000 : ℝ)*base79 + (69938815696091/13300000000000000000000000000 : ℝ)*base81 + (2974319/2000000000000000000000 : ℝ)*base90 + (2974319/2000000000000000000000 : ℝ)*base92 + (2974319/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1208_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11437/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1208_s8_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-533929539/2500000000 : ℝ)*x 0 + (5391788301/10000000000 : ℝ)*x 1 + (1053356787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533929539/2500000000 : ℝ)^8401 ≤ (3246016933493/25000000000000 : ℝ)^6353 := by
    have hnat : (533929539 : ℕ)^8401*25000000000000^6353 ≤ 3246016933493^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533929539 2500000000 3246016933493 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391788301/10000000000 : ℝ)^8401 ≤ (44182699438823/100000000000000 : ℝ)^6353 := by
    have hnat : (5391788301 : ℕ)^8401*100000000000000^6353 ≤ 44182699438823^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391788301 10000000000 44182699438823 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053356787/2000000000 : ℝ)^8401 ≤ (10708308203207/25000000000000 : ℝ)^6353 := by
    have hnat : (1053356787 : ℕ)^8401*25000000000000^6353 ≤ 10708308203207^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053356787 2000000000 10708308203207 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533929539/2500000000 : ℝ), (5391788301/10000000000 : ℝ), (1053356787/2000000000 : ℝ)] ![(3246016933493/25000000000000 : ℝ), (44182699438823/100000000000000 : ℝ), (10708308203207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533929539/2500000000 : ℝ)|^8401 ≤ (3246016933493/25000000000000 : ℝ)^6353
        have hw : |(-533929539/2500000000 : ℝ)|=(533929539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391788301/10000000000 : ℝ)|^8401 ≤ (44182699438823/100000000000000 : ℝ)^6353
        have hw : |(5391788301/10000000000 : ℝ)|=(5391788301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053356787/2000000000 : ℝ)|^8401 ≤ (10708308203207/25000000000000 : ℝ)^6353
        have hw : |(1053356787/2000000000 : ℝ)|=(1053356787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s8_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344469899/10000000000 : ℝ)*x 0 + (-219910531/1000000000 : ℝ)*x 1 + (2633392321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344469899/10000000000 : ℝ)^8401 ≤ (43670680974003/100000000000000 : ℝ)^6353 := by
    have hnat : (5344469899 : ℕ)^8401*100000000000000^6353 ≤ 43670680974003^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344469899 10000000000 43670680974003 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219910531/1000000000 : ℝ)^8401 ≤ (3374019648583/25000000000000 : ℝ)^6353 := by
    have hnat : (219910531 : ℕ)^8401*25000000000000^6353 ≤ 3374019648583^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219910531 1000000000 3374019648583 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633392321/5000000000 : ℝ)^8401 ≤ (42833240416211/100000000000000 : ℝ)^6353 := by
    have hnat : (2633392321 : ℕ)^8401*100000000000000^6353 ≤ 42833240416211^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633392321 5000000000 42833240416211 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344469899/10000000000 : ℝ), (-219910531/1000000000 : ℝ), (2633392321/5000000000 : ℝ)] ![(43670680974003/100000000000000 : ℝ), (3374019648583/25000000000000 : ℝ), (42833240416211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344469899/10000000000 : ℝ)|^8401 ≤ (43670680974003/100000000000000 : ℝ)^6353
        have hw : |(5344469899/10000000000 : ℝ)|=(5344469899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219910531/1000000000 : ℝ)|^8401 ≤ (3374019648583/25000000000000 : ℝ)^6353
        have hw : |(-219910531/1000000000 : ℝ)|=(219910531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633392321/5000000000 : ℝ)|^8401 ≤ (42833240416211/100000000000000 : ℝ)^6353
        have hw : |(2633392321/5000000000 : ℝ)|=(2633392321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s8_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344470477/10000000000 : ℝ)*x 0 + (2633391977/5000000000 : ℝ)*x 1 + (-549776363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344470477/10000000000 : ℝ)^8401 ≤ (10917671804869/25000000000000 : ℝ)^6353 := by
    have hnat : (5344470477 : ℕ)^8401*25000000000000^6353 ≤ 10917671804869^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344470477 10000000000 10917671804869 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633391977/5000000000 : ℝ)^8401 ≤ (21416616508581/50000000000000 : ℝ)^6353 := by
    have hnat : (2633391977 : ℕ)^8401*50000000000000^6353 ≤ 21416616508581^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633391977 5000000000 21416616508581 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549776363/2500000000 : ℝ)^8401 ≤ (13496079746729/100000000000000 : ℝ)^6353 := by
    have hnat : (549776363 : ℕ)^8401*100000000000000^6353 ≤ 13496079746729^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549776363 2500000000 13496079746729 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344470477/10000000000 : ℝ), (2633391977/5000000000 : ℝ), (-549776363/2500000000 : ℝ)] ![(10917671804869/25000000000000 : ℝ), (21416616508581/50000000000000 : ℝ), (13496079746729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344470477/10000000000 : ℝ)|^8401 ≤ (10917671804869/25000000000000 : ℝ)^6353
        have hw : |(5344470477/10000000000 : ℝ)|=(5344470477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633391977/5000000000 : ℝ)|^8401 ≤ (21416616508581/50000000000000 : ℝ)^6353
        have hw : |(2633391977/5000000000 : ℝ)|=(2633391977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-549776363/2500000000 : ℝ)|^8401 ≤ (13496079746729/100000000000000 : ℝ)^6353
        have hw : |(-549776363/2500000000 : ℝ)|=(549776363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s8_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177729967/5000000000 : ℝ)*x 0 + (846257283/2000000000 : ℝ)*x 1 + (448320139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177729967/5000000000 : ℝ)^8401 ≤ (8329335843307/25000000000000 : ℝ)^6353 := by
    have hnat : (2177729967 : ℕ)^8401*25000000000000^6353 ≤ 8329335843307^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177729967 5000000000 8329335843307 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846257283/2000000000 : ℝ)^8401 ≤ (1282682905197/4000000000000 : ℝ)^6353 := by
    have hnat : (846257283 : ℕ)^8401*4000000000000^6353 ≤ 1282682905197^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846257283 2000000000 1282682905197 4000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448320139/1000000000 : ℝ)^8401 ≤ (34615583982243/100000000000000 : ℝ)^6353 := by
    have hnat : (448320139 : ℕ)^8401*100000000000000^6353 ≤ 34615583982243^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448320139 1000000000 34615583982243 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177729967/5000000000 : ℝ), (846257283/2000000000 : ℝ), (448320139/1000000000 : ℝ)] ![(8329335843307/25000000000000 : ℝ), (1282682905197/4000000000000 : ℝ), (34615583982243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177729967/5000000000 : ℝ)|^8401 ≤ (8329335843307/25000000000000 : ℝ)^6353
        have hw : |(2177729967/5000000000 : ℝ)|=(2177729967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846257283/2000000000 : ℝ)|^8401 ≤ (1282682905197/4000000000000 : ℝ)^6353
        have hw : |(846257283/2000000000 : ℝ)|=(846257283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448320139/1000000000 : ℝ)|^8401 ≤ (34615583982243/100000000000000 : ℝ)^6353
        have hw : |(448320139/1000000000 : ℝ)|=(448320139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s8_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135722729/10000000000 : ℝ)*x 0 + (5267098931/10000000000 : ℝ)*x 1 + (134786807/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135722729/10000000000 : ℝ)^8401 ≤ (2596820899553/20000000000000 : ℝ)^6353 := by
    have hnat : (2135722729 : ℕ)^8401*20000000000000^6353 ≤ 2596820899553^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135722729 10000000000 2596820899553 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267098931/10000000000 : ℝ)^8401 ≤ (4283662044857/10000000000000 : ℝ)^6353 := by
    have hnat : (5267098931 : ℕ)^8401*10000000000000^6353 ≤ 4283662044857^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267098931 10000000000 4283662044857 10000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134786807/250000000 : ℝ)^8401 ≤ (11044818761883/25000000000000 : ℝ)^6353 := by
    have hnat : (134786807 : ℕ)^8401*25000000000000^6353 ≤ 11044818761883^6353*250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134786807 250000000 11044818761883 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135722729/10000000000 : ℝ), (5267098931/10000000000 : ℝ), (134786807/250000000 : ℝ)] ![(2596820899553/20000000000000 : ℝ), (4283662044857/10000000000000 : ℝ), (11044818761883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135722729/10000000000 : ℝ)|^8401 ≤ (2596820899553/20000000000000 : ℝ)^6353
        have hw : |(-2135722729/10000000000 : ℝ)|=(2135722729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267098931/10000000000 : ℝ)|^8401 ≤ (4283662044857/10000000000000 : ℝ)^6353
        have hw : |(5267098931/10000000000 : ℝ)|=(5267098931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134786807/250000000 : ℝ)|^8401 ≤ (11044818761883/25000000000000 : ℝ)^6353
        have hw : |(134786807/250000000 : ℝ)|=(134786807/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s8_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312649049/10000000000 : ℝ)*x 0 + (-2074417549/10000000000 : ℝ)*x 1 + (2695736141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312649049/10000000000 : ℝ)^8401 ≤ (43327177062789/100000000000000 : ℝ)^6353 := by
    have hnat : (5312649049 : ℕ)^8401*100000000000000^6353 ≤ 43327177062789^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312649049 10000000000 43327177062789 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074417549/10000000000 : ℝ)^8401 ≤ (12493547853571/100000000000000 : ℝ)^6353 := by
    have hnat : (2074417549 : ℕ)^8401*100000000000000^6353 ≤ 12493547853571^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074417549 10000000000 12493547853571 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695736141/5000000000 : ℝ)^8401 ≤ (11044818767301/25000000000000 : ℝ)^6353 := by
    have hnat : (2695736141 : ℕ)^8401*25000000000000^6353 ≤ 11044818767301^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695736141 5000000000 11044818767301 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312649049/10000000000 : ℝ), (-2074417549/10000000000 : ℝ), (2695736141/5000000000 : ℝ)] ![(43327177062789/100000000000000 : ℝ), (12493547853571/100000000000000 : ℝ), (11044818767301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312649049/10000000000 : ℝ)|^8401 ≤ (43327177062789/100000000000000 : ℝ)^6353
        have hw : |(5312649049/10000000000 : ℝ)|=(5312649049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074417549/10000000000 : ℝ)|^8401 ≤ (12493547853571/100000000000000 : ℝ)^6353
        have hw : |(-2074417549/10000000000 : ℝ)|=(2074417549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695736141/5000000000 : ℝ)|^8401 ≤ (11044818767301/25000000000000 : ℝ)^6353
        have hw : |(2695736141/5000000000 : ℝ)|=(2695736141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s8_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328162271/2500000000 : ℝ)*x 0 + (5391472259/10000000000 : ℝ)*x 1 + (-518604383/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328162271/2500000000 : ℝ)^8401 ≤ (43327177440247/100000000000000 : ℝ)^6353 := by
    have hnat : (1328162271 : ℕ)^8401*100000000000000^6353 ≤ 43327177440247^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328162271 2500000000 43327177440247 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391472259/10000000000 : ℝ)^8401 ≤ (44179274819979/100000000000000 : ℝ)^6353 := by
    have hnat : (5391472259 : ℕ)^8401*100000000000000^6353 ≤ 44179274819979^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391472259 10000000000 44179274819979 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518604383/2500000000 : ℝ)^8401 ≤ (12493547718179/100000000000000 : ℝ)^6353 := by
    have hnat : (518604383 : ℕ)^8401*100000000000000^6353 ≤ 12493547718179^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518604383 2500000000 12493547718179 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328162271/2500000000 : ℝ), (5391472259/10000000000 : ℝ), (-518604383/2500000000 : ℝ)] ![(43327177440247/100000000000000 : ℝ), (44179274819979/100000000000000 : ℝ), (12493547718179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328162271/2500000000 : ℝ)|^8401 ≤ (43327177440247/100000000000000 : ℝ)^6353
        have hw : |(1328162271/2500000000 : ℝ)|=(1328162271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391472259/10000000000 : ℝ)|^8401 ≤ (44179274819979/100000000000000 : ℝ)^6353
        have hw : |(5391472259/10000000000 : ℝ)|=(5391472259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-518604383/2500000000 : ℝ)|^8401 ≤ (12493547718179/100000000000000 : ℝ)^6353
        have hw : |(-518604383/2500000000 : ℝ)|=(518604383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s8_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355468897/10000000000 : ℝ)*x 0 + (896513543/2000000000 : ℝ)*x 1 + (4231922937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355468897/10000000000 : ℝ)^8401 ≤ (16658717019359/50000000000000 : ℝ)^6353 := by
    have hnat : (4355468897 : ℕ)^8401*50000000000000^6353 ≤ 16658717019359^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355468897 10000000000 16658717019359 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896513543/2000000000 : ℝ)^8401 ≤ (34609114161877/100000000000000 : ℝ)^6353 := by
    have hnat : (896513543 : ℕ)^8401*100000000000000^6353 ≤ 34609114161877^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896513543 2000000000 34609114161877 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231922937/10000000000 : ℝ)^8401 ≤ (32073451782209/100000000000000 : ℝ)^6353 := by
    have hnat : (4231922937 : ℕ)^8401*100000000000000^6353 ≤ 32073451782209^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231922937 10000000000 32073451782209 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355468897/10000000000 : ℝ), (896513543/2000000000 : ℝ), (4231922937/10000000000 : ℝ)] ![(16658717019359/50000000000000 : ℝ), (34609114161877/100000000000000 : ℝ), (32073451782209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355468897/10000000000 : ℝ)|^8401 ≤ (16658717019359/50000000000000 : ℝ)^6353
        have hw : |(4355468897/10000000000 : ℝ)|=(4355468897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896513543/2000000000 : ℝ)|^8401 ≤ (34609114161877/100000000000000 : ℝ)^6353
        have hw : |(896513543/2000000000 : ℝ)|=(896513543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231922937/10000000000 : ℝ)|^8401 ≤ (32073451782209/100000000000000 : ℝ)^6353
        have hw : |(4231922937/10000000000 : ℝ)|=(4231922937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5719/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7043/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11437/100000 : ℝ) ^ (525/128 : ℝ) ≤ (13728032834146337/100000000000000000000 : ℝ) := by
    have hpowers : (11437/100000 : ℝ)^525 ≤ (13728032834146337/100000000000000000000 : ℝ)^128 := by
      have hnat : (11437 : ℕ)^525*100000000000000000000^128 ≤ 13728032834146337^128*100000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11437 100000 13728032834146337 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11437/100000 : ℝ)) (X := (13728032834146337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14087/100000 : ℝ) ^ (525/128 : ℝ) ≤ (4034000538077737/12500000000000000000 : ℝ) := by
    have hpowers : (14087/100000 : ℝ)^525 ≤ (4034000538077737/12500000000000000000 : ℝ)^128 := by
      have hnat : (14087 : ℕ)^525*12500000000000000000^128 ≤ 4034000538077737^128*100000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14087 100000 4034000538077737 12500000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14087/100000 : ℝ)) (X := (4034000538077737/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013728032834146337/50000000000000000000 : ℝ) ≤ (10000669335549807/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50013728032834146337/50000000000000000000 : ℝ)^128 ≤ (10000669335549807/10000000000000000 : ℝ)^525 := by
      have hnat : (50013728032834146337 : ℕ)^128*10000000000000000^525 ≤ 10000669335549807^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013728032834146337 50000000000000000000 10000669335549807 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000669335549807/10000000000000000 : ℝ)) (X := (50013728032834146337/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046000037138768233/100000000000000000000 : ℝ) ≤ (625070083106719/625000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (100046000037138768233/100000000000000000000 : ℝ)^128 ≤ (625070083106719/625000000000000 : ℝ)^525 := by
      have hnat : (100046000037138768233 : ℕ)^128*625000000000000^525 ≤ 625070083106719^525*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046000037138768233 100000000000000000000 625070083106719 625000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625070083106719/625000000000000 : ℝ)) (X := (100046000037138768233/100000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254034000538077737/6250000000000000000 : ℝ) ≤ (10001573323865201/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (6254034000538077737/6250000000000000000 : ℝ)^128 ≤ (10001573323865201/10000000000000000 : ℝ)^525 := by
      have hnat : (6254034000538077737 : ℕ)^128*10000000000000000^525 ≤ 10001573323865201^525*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254034000538077737 6250000000000000000 10001573323865201 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001573323865201/10000000000000000 : ℝ)) (X := (6254034000538077737/6250000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13728032834146337/100000000000000000000 : ℝ) ≤ ((6622858706210956843/6625000000000000000 : ℝ)+2*(451994157697/265000000000000 : ℝ)*(11437/100000 : ℝ))^(525/128 : ℝ) := by
    rw [show (6622858706210956843/6625000000000000000 : ℝ)+2*(451994157697/265000000000000 : ℝ)*(11437/100000 : ℝ)=(10000669335549807/10000000000000000 : ℝ) by norm_num, show 1+2*(13728032834146337/100000000000000000000 : ℝ)=(50013728032834146337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4034000538077737/12500000000000000000 : ℝ)+(13728032834146337/100000000000000000000 : ℝ) ≤ ((6622858706210956843/6625000000000000000 : ℝ)+(451994157697/265000000000000 : ℝ)*((14087/100000 : ℝ)+(11437/100000 : ℝ)))^(525/128 : ℝ) := by
    rw [show (6622858706210956843/6625000000000000000 : ℝ)+(451994157697/265000000000000 : ℝ)*((14087/100000 : ℝ)+(11437/100000 : ℝ))=(625070083106719/625000000000000 : ℝ) by norm_num, show 1+(4034000538077737/12500000000000000000 : ℝ)+(13728032834146337/100000000000000000000 : ℝ)=(100046000037138768233/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4034000538077737/12500000000000000000 : ℝ) ≤ ((6622858706210956843/6625000000000000000 : ℝ)+2*(451994157697/265000000000000 : ℝ)*(14087/100000 : ℝ))^(525/128 : ℝ) := by
    rw [show (6622858706210956843/6625000000000000000 : ℝ)+2*(451994157697/265000000000000 : ℝ)*(14087/100000 : ℝ)=(10001573323865201/10000000000000000 : ℝ) by norm_num, show 1+2*(4034000538077737/12500000000000000000 : ℝ)=(6254034000538077737/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6622858706210956843/6625000000000000000 : ℝ)*(X 1 0+X 2 0)+(451994157697/265000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (11437/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (6622858706210956843/6625000000000000000 : ℝ)) (alpha := (451994157697/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6622858706210956843/6625000000000000000 : ℝ)*(X 0 1+X 2 1)+(451994157697/265000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (11437/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (6622858706210956843/6625000000000000000 : ℝ)) (alpha := (451994157697/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6622858706210956843/6625000000000000000 : ℝ)*(X 0 2+X 1 2)+(451994157697/265000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (11437/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (6622858706210956843/6625000000000000000 : ℝ)) (alpha := (451994157697/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-533929539/2500000000 : ℝ)*X 0 0+(5391788301/10000000000 : ℝ)*X 0 1+(1053356787/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344469899/10000000000 : ℝ)*X 1 0+(-219910531/1000000000 : ℝ)*X 1 1+(2633392321/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344470477/10000000000 : ℝ)*X 2 0+(2633391977/5000000000 : ℝ)*X 2 1+(-549776363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177729967/5000000000 : ℝ)*X 0 0+(846257283/2000000000 : ℝ)*X 0 1+(448320139/1000000000 : ℝ)*X 0 2+(2177729967/5000000000 : ℝ)*X 1 0+(846257283/2000000000 : ℝ)*X 1 1+(448320139/1000000000 : ℝ)*X 1 2+(2177729967/5000000000 : ℝ)*X 2 0+(846257283/2000000000 : ℝ)*X 2 1+(448320139/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2135722729/10000000000 : ℝ)*X 0 0+(5267098931/10000000000 : ℝ)*X 0 1+(134786807/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312649049/10000000000 : ℝ)*X 1 0+(-2074417549/10000000000 : ℝ)*X 1 1+(2695736141/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328162271/2500000000 : ℝ)*X 2 0+(5391472259/10000000000 : ℝ)*X 2 1+(-518604383/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355468897/10000000000 : ℝ)*X 0 0+(896513543/2000000000 : ℝ)*X 0 1+(4231922937/10000000000 : ℝ)*X 0 2+(4355468897/10000000000 : ℝ)*X 1 0+(896513543/2000000000 : ℝ)*X 1 1+(4231922937/10000000000 : ℝ)*X 1 2+(4355468897/10000000000 : ℝ)*X 2 0+(896513543/2000000000 : ℝ)*X 2 1+(4231922937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10640532698839073677136127/33125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104346983/12500000000000 : ℝ)*(base19) + (2418509/160000000000 : ℝ)*(base23) + (100680439/100000000000000 : ℝ)*(lower2) + (27523463/10000000000000 : ℝ)*(upper3) + (61883037/100000000000000 : ℝ)*(upper5) + (598472625578263/10000000000000 : ℝ)*(major0) + (598472625578263/10000000000000 : ℝ)*(major1) + (598472625578263/10000000000000 : ℝ)*(major2) + (399988697366011/5000000000000 : ℝ)*(sp0) + (999978510907871/12500000000000 : ℝ)*(sp1) + (3999913705235353/50000000000000 : ℝ)*(sp2) + (396960346082219/10000000000000 : ℝ)*(sp3) + (54974718611/100000000000000 : ℝ)*(sp4) + (20117996773/100000000000000 : ℝ)*(sp7) + (1984811789409481/50000000000000 : ℝ)*(f.failure) + (499989307627427/6250000000000 : ℝ)*(f.sum) + (4784045119839/1325000000000000000000000000 : ℝ)*base66 + (1046135765977821291/66250000000000000000000000000000 : ℝ)*base68 + (16685717178428709/66250000000000000000000000000000 : ℝ)*base69 + (518714313166571291/66250000000000000000000000000000 : ℝ)*base72 + (4649353087907/662500000000000000000000000 : ℝ)*base74 + (822997832606571291/66250000000000000000000000000000 : ℝ)*base76 + (732287979220928709/66250000000000000000000000000000 : ℝ)*base77 + (80687796651571291/66250000000000000000000000000000 : ℝ)*base80 + (1564928533807/662500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (25561773/5000000000000000000000 : ℝ)*base90 + (25561773/5000000000000000000000 : ℝ)*base92 + (25561773/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3202211154898299151627167369/331250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1645725261/100000000000000 : ℝ)*(base19) + (926166121/50000000000000 : ℝ)*(base23) + (582350293/100000000000000 : ℝ)*(lower1) + (44423703/25000000000000 : ℝ)*(upper3) + (33431609/50000000000000 : ℝ)*(lower4) + (5914559/3125000000000 : ℝ)*(upper5) + (6014973494508039/100000000000000 : ℝ)*(major0) + (6014973494508039/100000000000000 : ℝ)*(major1) + (6014973494508039/100000000000000 : ℝ)*(major2) + (579756293/12500000000000 : ℝ)*(sp2) + (8040260323700653/100000000000000 : ℝ)*(sp4) + (251258083686731/3125000000000 : ℝ)*(sp5) + (8040253833318067/100000000000000 : ℝ)*(sp6) + (997421585770081/25000000000000 : ℝ)*(sp7) + (997421585770081/25000000000000 : ℝ)*(f.failure) + (8040260323700653/100000000000000 : ℝ)*(f.sum) + (92099862395433/13250000000000000000000000000 : ℝ)*base65 + (1719695071412635877/662500000000000000000000000000000 : ℝ)*base67 + (191076474850135877/662500000000000000000000000000000 : ℝ)*base69 + (41282245179550135877/662500000000000000000000000000000 : ℝ)*base71 + (82708992987183/13250000000000000000000000000 : ℝ)*base73 + (31872697195950135877/662500000000000000000000000000000 : ℝ)*base75 + (3848376106999864123/662500000000000000000000000000000 : ℝ)*base78 + (7818371479312364123/662500000000000000000000000000000 : ℝ)*base80 + (66122907934183/13250000000000000000000000000 : ℝ)*base81 + (6601573/2500000000000000000000 : ℝ)*base90 + (6601573/2500000000000000000000 : ℝ)*base92 + (6601573/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1208_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1208_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1208_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1208_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1208_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1208_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
