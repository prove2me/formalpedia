-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:29:28.010456+00:00
-- url     : https://prove2.me/submissions/23365bac-8891-4f4f-93fe-cb4653ea34eb

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
theorem support_rectangle_w1256_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-928123983/5000000000 : ℝ)*x 0 + (3014177701/5000000000 : ℝ)*x 1 + (958943753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928123983/5000000000 : ℝ)^8449 ≤ (5415094932129/50000000000000 : ℝ)^6401 := by
    have hnat : (928123983 : ℕ)^8449*50000000000000^6401 ≤ 5415094932129^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928123983 5000000000 5415094932129 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3014177701/5000000000 : ℝ)^8449 ≤ (64088997909/125000000000 : ℝ)^6401 := by
    have hnat : (3014177701 : ℕ)^8449*125000000000^6401 ≤ 64088997909^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014177701 5000000000 64088997909 125000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958943753/2000000000 : ℝ)^8449 ≤ (378986118003/1000000000000 : ℝ)^6401 := by
    have hnat : (958943753 : ℕ)^8449*1000000000000^6401 ≤ 378986118003^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958943753 2000000000 378986118003 1000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928123983/5000000000 : ℝ), (3014177701/5000000000 : ℝ), (958943753/2000000000 : ℝ)] ![(5415094932129/50000000000000 : ℝ), (64088997909/125000000000 : ℝ), (378986118003/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928123983/5000000000 : ℝ)|^8449 ≤ (5415094932129/50000000000000 : ℝ)^6401
        have hw : |(-928123983/5000000000 : ℝ)|=(928123983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3014177701/5000000000 : ℝ)|^8449 ≤ (64088997909/125000000000 : ℝ)^6401
        have hw : |(3014177701/5000000000 : ℝ)|=(3014177701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958943753/2000000000 : ℝ)|^8449 ≤ (378986118003/1000000000000 : ℝ)^6401
        have hw : |(958943753/2000000000 : ℝ)|=(958943753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (688796349/1250000000 : ℝ)*x 0 + (-1280556683/5000000000 : ℝ)*x 1 + (4794718707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688796349/1250000000 : ℝ)^8449 ≤ (45537756015613/100000000000000 : ℝ)^6401 := by
    have hnat : (688796349 : ℕ)^8449*100000000000000^6401 ≤ 45537756015613^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688796349 1250000000 45537756015613 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280556683/5000000000 : ℝ)^8449 ≤ (16563632777147/100000000000000 : ℝ)^6401 := by
    have hnat : (1280556683 : ℕ)^8449*100000000000000^6401 ≤ 16563632777147^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280556683 5000000000 16563632777147 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794718707/10000000000 : ℝ)^8449 ≤ (18949305597587/50000000000000 : ℝ)^6401 := by
    have hnat : (4794718707 : ℕ)^8449*50000000000000^6401 ≤ 18949305597587^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794718707 10000000000 18949305597587 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(688796349/1250000000 : ℝ), (-1280556683/5000000000 : ℝ), (4794718707/10000000000 : ℝ)] ![(45537756015613/100000000000000 : ℝ), (16563632777147/100000000000000 : ℝ), (18949305597587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(688796349/1250000000 : ℝ)|^8449 ≤ (45537756015613/100000000000000 : ℝ)^6401
        have hw : |(688796349/1250000000 : ℝ)|=(688796349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1280556683/5000000000 : ℝ)|^8449 ≤ (16563632777147/100000000000000 : ℝ)^6401
        have hw : |(-1280556683/5000000000 : ℝ)|=(1280556683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794718707/10000000000 : ℝ)|^8449 ≤ (18949305597587/50000000000000 : ℝ)^6401
        have hw : |(4794718707/10000000000 : ℝ)|=(4794718707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755185393/5000000000 : ℝ)*x 0 + (153431/320000 : ℝ)*x 1 + (-64027833/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755185393/5000000000 : ℝ)^8449 ≤ (9107551190033/20000000000000 : ℝ)^6401 := by
    have hnat : (2755185393 : ℕ)^8449*20000000000000^6401 ≤ 9107551190033^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755185393 5000000000 9107551190033 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153431/320000 : ℝ)^8449 ≤ (18949305821901/50000000000000 : ℝ)^6401 := by
    have hnat : (153431 : ℕ)^8449*50000000000000^6401 ≤ 18949305821901^6401*320000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153431 320000 18949305821901 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64027833/250000000 : ℝ)^8449 ≤ (1035227024029/6250000000000 : ℝ)^6401 := by
    have hnat : (64027833 : ℕ)^8449*6250000000000^6401 ≤ 1035227024029^6401*250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64027833 250000000 1035227024029 6250000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755185393/5000000000 : ℝ), (153431/320000 : ℝ), (-64027833/250000000 : ℝ)] ![(9107551190033/20000000000000 : ℝ), (18949305821901/50000000000000 : ℝ), (1035227024029/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755185393/5000000000 : ℝ)|^8449 ≤ (9107551190033/20000000000000 : ℝ)^6401
        have hw : |(2755185393/5000000000 : ℝ)|=(2755185393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153431/320000 : ℝ)|^8449 ≤ (18949305821901/50000000000000 : ℝ)^6401
        have hw : |(153431/320000 : ℝ)|=(153431/320000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64027833/250000000 : ℝ)|^8449 ≤ (1035227024029/6250000000000 : ℝ)^6401
        have hw : |(-64027833/250000000 : ℝ)|=(64027833/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s0_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (838384843/2000000000 : ℝ)*x 0 + (779093509/2500000000 : ℝ)*x 1 + (351603731/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838384843/2000000000 : ℝ)^8449 ≤ (31739829837851/100000000000000 : ℝ)^6401 := by
    have hnat : (838384843 : ℕ)^8449*100000000000000^6401 ≤ 31739829837851^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838384843 2000000000 31739829837851 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779093509/2500000000 : ℝ)^8449 ≤ (2146064426623/10000000000000 : ℝ)^6401 := by
    have hnat : (779093509 : ℕ)^8449*10000000000000^6401 ≤ 2146064426623^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779093509 2500000000 2146064426623 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351603731/625000000 : ℝ)^8449 ≤ (5849940735273/12500000000000 : ℝ)^6401 := by
    have hnat : (351603731 : ℕ)^8449*12500000000000^6401 ≤ 5849940735273^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351603731 625000000 5849940735273 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838384843/2000000000 : ℝ), (779093509/2500000000 : ℝ), (351603731/625000000 : ℝ)] ![(31739829837851/100000000000000 : ℝ), (2146064426623/10000000000000 : ℝ), (5849940735273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838384843/2000000000 : ℝ)|^8449 ≤ (31739829837851/100000000000000 : ℝ)^6401
        have hw : |(838384843/2000000000 : ℝ)|=(838384843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779093509/2500000000 : ℝ)|^8449 ≤ (2146064426623/10000000000000 : ℝ)^6401
        have hw : |(779093509/2500000000 : ℝ)|=(779093509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(351603731/625000000 : ℝ)|^8449 ≤ (5849940735273/12500000000000 : ℝ)^6401
        have hw : |(351603731/625000000 : ℝ)|=(351603731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s0_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-372213153/2000000000 : ℝ)*x 0 + (4826478293/10000000000 : ℝ)*x 1 + (5995472909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372213153/2000000000 : ℝ)^8449 ≤ (10867308022457/100000000000000 : ℝ)^6401 := by
    have hnat : (372213153 : ℕ)^8449*100000000000000^6401 ≤ 10867308022457^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372213153 2000000000 10867308022457 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826478293/10000000000 : ℝ)^8449 ≤ (7646063197663/20000000000000 : ℝ)^6401 := by
    have hnat : (4826478293 : ℕ)^8449*20000000000000^6401 ≤ 7646063197663^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826478293 10000000000 7646063197663 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5995472909/10000000000 : ℝ)^8449 ≤ (50902375972933/100000000000000 : ℝ)^6401 := by
    have hnat : (5995472909 : ℕ)^8449*100000000000000^6401 ≤ 50902375972933^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995472909 10000000000 50902375972933 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372213153/2000000000 : ℝ), (4826478293/10000000000 : ℝ), (5995472909/10000000000 : ℝ)] ![(10867308022457/100000000000000 : ℝ), (7646063197663/20000000000000 : ℝ), (50902375972933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372213153/2000000000 : ℝ)|^8449 ≤ (10867308022457/100000000000000 : ℝ)^6401
        have hw : |(-372213153/2000000000 : ℝ)|=(372213153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826478293/10000000000 : ℝ)|^8449 ≤ (7646063197663/20000000000000 : ℝ)^6401
        have hw : |(4826478293/10000000000 : ℝ)|=(4826478293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5995472909/10000000000 : ℝ)|^8449 ≤ (50902375972933/100000000000000 : ℝ)^6401
        have hw : |(5995472909/10000000000 : ℝ)|=(5995472909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s0_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1293664323/2500000000 : ℝ)*x 0 + (-1360356897/10000000000 : ℝ)*x 1 + (5995475291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293664323/2500000000 : ℝ)^8449 ≤ (20955981684343/50000000000000 : ℝ)^6401 := by
    have hnat : (1293664323 : ℕ)^8449*50000000000000^6401 ≤ 20955981684343^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293664323 2500000000 20955981684343 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360356897/10000000000 : ℝ)^8449 ≤ (7185633948127/100000000000000 : ℝ)^6401 := by
    have hnat : (1360356897 : ℕ)^8449*100000000000000^6401 ≤ 7185633948127^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360356897 10000000000 7185633948127 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5995475291/10000000000 : ℝ)^8449 ≤ (25451201333473/50000000000000 : ℝ)^6401 := by
    have hnat : (5995475291 : ℕ)^8449*50000000000000^6401 ≤ 25451201333473^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995475291 10000000000 25451201333473 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293664323/2500000000 : ℝ), (-1360356897/10000000000 : ℝ), (5995475291/10000000000 : ℝ)] ![(20955981684343/50000000000000 : ℝ), (7185633948127/100000000000000 : ℝ), (25451201333473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293664323/2500000000 : ℝ)|^8449 ≤ (20955981684343/50000000000000 : ℝ)^6401
        have hw : |(1293664323/2500000000 : ℝ)|=(1293664323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1360356897/10000000000 : ℝ)|^8449 ≤ (7185633948127/100000000000000 : ℝ)^6401
        have hw : |(-1360356897/10000000000 : ℝ)|=(1360356897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5995475291/10000000000 : ℝ)|^8449 ≤ (25451201333473/50000000000000 : ℝ)^6401
        have hw : |(5995475291/10000000000 : ℝ)|=(5995475291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517465831/1000000000 : ℝ)*x 0 + (1498868333/2500000000 : ℝ)*x 1 + (-680179243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517465831/1000000000 : ℝ)^8449 ≤ (20955987126007/50000000000000 : ℝ)^6401 := by
    have hnat : (517465831 : ℕ)^8449*50000000000000^6401 ≤ 20955987126007^6401*1000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517465831 1000000000 20955987126007 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1498868333/2500000000 : ℝ)^8449 ≤ (10180476142661/20000000000000 : ℝ)^6401 := by
    have hnat : (1498868333 : ℕ)^8449*20000000000000^6401 ≤ 10180476142661^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498868333 2500000000 10180476142661 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680179243/5000000000 : ℝ)^8449 ≤ (898205628369/12500000000000 : ℝ)^6401 := by
    have hnat : (680179243 : ℕ)^8449*12500000000000^6401 ≤ 898205628369^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680179243 5000000000 898205628369 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517465831/1000000000 : ℝ), (1498868333/2500000000 : ℝ), (-680179243/5000000000 : ℝ)] ![(20955987126007/50000000000000 : ℝ), (10180476142661/20000000000000 : ℝ), (898205628369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517465831/1000000000 : ℝ)|^8449 ≤ (20955987126007/50000000000000 : ℝ)^6401
        have hw : |(517465831/1000000000 : ℝ)|=(517465831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1498868333/2500000000 : ℝ)|^8449 ≤ (10180476142661/20000000000000 : ℝ)^6401
        have hw : |(1498868333/2500000000 : ℝ)|=(1498868333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-680179243/5000000000 : ℝ)|^8449 ≤ (898205628369/12500000000000 : ℝ)^6401
        have hw : |(-680179243/5000000000 : ℝ)|=(680179243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (840345191/2000000000 : ℝ)*x 0 + (1112212927/2000000000 : ℝ)*x 1 + (3183252967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840345191/2000000000 : ℝ)^8449 ≤ (15918913575533/50000000000000 : ℝ)^6401 := by
    have hnat : (840345191 : ℕ)^8449*50000000000000^6401 ≤ 15918913575533^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840345191 2000000000 15918913575533 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112212927/2000000000 : ℝ)^8449 ≤ (46091540606057/100000000000000 : ℝ)^6401 := by
    have hnat : (1112212927 : ℕ)^8449*100000000000000^6401 ≤ 46091540606057^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112212927 2000000000 46091540606057 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183252967/10000000000 : ℝ)^8449 ≤ (1103531611191/5000000000000 : ℝ)^6401 := by
    have hnat : (3183252967 : ℕ)^8449*5000000000000^6401 ≤ 1103531611191^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183252967 10000000000 1103531611191 5000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840345191/2000000000 : ℝ), (1112212927/2000000000 : ℝ), (3183252967/10000000000 : ℝ)] ![(15918913575533/50000000000000 : ℝ), (46091540606057/100000000000000 : ℝ), (1103531611191/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840345191/2000000000 : ℝ)|^8449 ≤ (15918913575533/50000000000000 : ℝ)^6401
        have hw : |(840345191/2000000000 : ℝ)|=(840345191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1112212927/2000000000 : ℝ)|^8449 ≤ (46091540606057/100000000000000 : ℝ)^6401
        have hw : |(1112212927/2000000000 : ℝ)|=(1112212927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183252967/10000000000 : ℝ)|^8449 ≤ (1103531611191/5000000000000 : ℝ)^6401
        have hw : |(3183252967/10000000000 : ℝ)|=(3183252967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (437/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3423/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (33/8 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^33 ≤ (0 : ℝ)^8 := by
      have hnat : (0 : ℕ)^33*1^8 ≤ 0^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (33/8 : ℝ) ≤ (114147779742399537/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^33 ≤ (114147779742399537/5000000000000000000 : ℝ)^8 := by
      have hnat : (2 : ℕ)^33*5000000000000000000^8 ≤ 114147779742399537^8*5^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 114147779742399537 5000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (114147779742399537/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1 : ℝ)^8 ≤ (1 : ℝ)^33 := by
      have hnat : (1 : ℕ)^8*1^33 ≤ 1^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (5114147779742399537/5000000000000000000 : ℝ) ≤ (10054872086371233/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5114147779742399537/5000000000000000000 : ℝ)^8 ≤ (10054872086371233/10000000000000000 : ℝ)^33 := by
      have hnat : (5114147779742399537 : ℕ)^8*10000000000000000^33 ≤ 10054872086371233^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5114147779742399537 5000000000000000000 10054872086371233 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054872086371233/10000000000000000 : ℝ)) (X := (5114147779742399537/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (2614147779742399537/2500000000000000000 : ℝ) ≤ (5054872086371233/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2614147779742399537/2500000000000000000 : ℝ)^8 ≤ (5054872086371233/5000000000000000 : ℝ)^33 := by
      have hnat : (2614147779742399537 : ℕ)^8*5000000000000000^33 ≤ 5054872086371233^33*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2614147779742399537 2500000000000000000 5054872086371233 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054872086371233/5000000000000000 : ℝ)) (X := (2614147779742399537/2500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54872086371233/4000000000000000 : ℝ)*(0 : ℝ))^(33/8 : ℝ) := by
    rw [show (1 : ℝ)+2*(54872086371233/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(114147779742399537/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54872086371233/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(33/8 : ℝ) := by
    rw [show (1 : ℝ)+(54872086371233/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054872086371233/10000000000000000 : ℝ) by norm_num, show 1+(114147779742399537/5000000000000000000 : ℝ)+(0 : ℝ)=(5114147779742399537/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(114147779742399537/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54872086371233/4000000000000000 : ℝ)*(2/5 : ℝ))^(33/8 : ℝ) := by
    rw [show (1 : ℝ)+2*(54872086371233/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054872086371233/5000000000000000 : ℝ) by norm_num, show 1+2*(114147779742399537/5000000000000000000 : ℝ)=(2614147779742399537/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54872086371233/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54872086371233/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54872086371233/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54872086371233/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54872086371233/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54872086371233/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-928123983/5000000000 : ℝ)*X 0 0+(3014177701/5000000000 : ℝ)*X 0 1+(958943753/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((688796349/1250000000 : ℝ)*X 1 0+(-1280556683/5000000000 : ℝ)*X 1 1+(4794718707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2755185393/5000000000 : ℝ)*X 2 0+(153431/320000 : ℝ)*X 2 1+(-64027833/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838384843/2000000000 : ℝ)*X 0 0+(779093509/2500000000 : ℝ)*X 0 1+(351603731/625000000 : ℝ)*X 0 2+(838384843/2000000000 : ℝ)*X 1 0+(779093509/2500000000 : ℝ)*X 1 1+(351603731/625000000 : ℝ)*X 1 2+(838384843/2000000000 : ℝ)*X 2 0+(779093509/2500000000 : ℝ)*X 2 1+(351603731/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372213153/2000000000 : ℝ)*X 0 0+(4826478293/10000000000 : ℝ)*X 0 1+(5995472909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293664323/2500000000 : ℝ)*X 1 0+(-1360356897/10000000000 : ℝ)*X 1 1+(5995475291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517465831/1000000000 : ℝ)*X 2 0+(1498868333/2500000000 : ℝ)*X 2 1+(-680179243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((840345191/2000000000 : ℝ)*X 0 0+(1112212927/2000000000 : ℝ)*X 0 1+(3183252967/10000000000 : ℝ)*X 0 2+(840345191/2000000000 : ℝ)*X 1 0+(1112212927/2000000000 : ℝ)*X 1 1+(3183252967/10000000000 : ℝ)*X 1 2+(840345191/2000000000 : ℝ)*X 2 0+(1112212927/2000000000 : ℝ)*X 2 1+(3183252967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46246642434068196280959/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8086563/25000000000000 : ℝ)*(base1) + (147562491/25000000000000 : ℝ)*(base19) + (136897171/25000000000000 : ℝ)*(base23) + (20889319/50000000000000 : ℝ)*(base24) + (128380509/100000000000000 : ℝ)*(upper3) + (120913625690247/20000000000000 : ℝ)*(major0) + (120913625690247/20000000000000 : ℝ)*(major1) + (120913625690247/20000000000000 : ℝ)*(major2) + (20265336056637/2500000000000 : ℝ)*(sp0) + (810614140926561/100000000000000 : ℝ)*(sp1) + (202653535452301/25000000000000 : ℝ)*(sp2) + (398520398074677/100000000000000 : ℝ)*(sp3) + (1321257297/100000000000000 : ℝ)*(sp4) + (127278409/12500000000000 : ℝ)*(sp7) + (1992607243241/500000000000 : ℝ)*(f.failure) + (405307365588263/50000000000000 : ℝ)*(f.sum) + (103676787735449/40000000000000000000000000000 : ℝ)*base66 + (182696016375449/80000000000000000000000000000 : ℝ)*base68 + (398947561655449/80000000000000000000000000000 : ℝ)*base70 + (93029260695449/80000000000000000000000000000 : ℝ)*base72 + (129332801175449/40000000000000000000000000000 : ℝ)*base74 + (22153757975449/80000000000000000000000000000 : ℝ)*base76 + (521517903255449/80000000000000000000000000000 : ℝ)*base78 + (536847857895449/80000000000000000000000000000 : ℝ)*base80 + (221586367975449/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (139703/50000000000000000000 : ℝ)*base89 + (139703/50000000000000000000 : ℝ)*base91 + (139703/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1293271779134974177348917/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218181529/100000000000000 : ℝ)*(base1) + (58675841/4000000000000 : ℝ)*(base19) + (813269037/50000000000000 : ℝ)*(base23) + (161247153/50000000000000 : ℝ)*(upper3) + (6364009/50000000000000 : ℝ)*(upper5) + (637994945858183/100000000000000 : ℝ)*(major0) + (637994945858183/100000000000000 : ℝ)*(major1) + (637994945858183/100000000000000 : ℝ)*(major2) + (1406954693/50000000000000 : ℝ)*(sp1) + (2680657881/100000000000000 : ℝ)*(sp2) + (53464627057693/6250000000000 : ℝ)*(sp4) + (855429533936147/100000000000000 : ℝ)*(sp5) + (213857376886401/25000000000000 : ℝ)*(sp6) + (52569455405997/12500000000000 : ℝ)*(sp7) + (84111172285901/20000000000000 : ℝ)*(f.failure) + (427716907370779/50000000000000 : ℝ)*(f.sum) + (478008556849639/200000000000000000000000000000 : ℝ)*base65 + (1036667508750361/400000000000000000000000000000 : ℝ)*base68 + (3382231604750361/400000000000000000000000000000 : ℝ)*base70 + (1240953622449639/400000000000000000000000000000 : ℝ)*base71 + (369368416150361/200000000000000000000000000000 : ℝ)*base74 + (624686520449639/400000000000000000000000000000 : ℝ)*base75 + (1031304805550361/400000000000000000000000000000 : ℝ)*base78 + (1222823493649639/400000000000000000000000000000 : ℝ)*base79 + (519539356750361/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6637517/2000000000000000000000 : ℝ)*base90 + (6637517/2000000000000000000000 : ℝ)*base92 + (6637517/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1256_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (437/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3423/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1256_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026318907/5000000000 : ℝ)*x 0 + (5672109431/10000000000 : ℝ)*x 1 + (5025252709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026318907/5000000000 : ℝ)^8449 ≤ (12367634679353/100000000000000 : ℝ)^6401 := by
    have hnat : (1026318907 : ℕ)^8449*100000000000000^6401 ≤ 12367634679353^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026318907 5000000000 12367634679353 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5672109431/10000000000 : ℝ)^8449 ≤ (2365512179799/5000000000000 : ℝ)^6401 := by
    have hnat : (5672109431 : ℕ)^8449*5000000000000^6401 ≤ 2365512179799^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672109431 10000000000 2365512179799 5000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025252709/10000000000 : ℝ)^8449 ≤ (40322121708877/100000000000000 : ℝ)^6401 := by
    have hnat : (5025252709 : ℕ)^8449*100000000000000^6401 ≤ 40322121708877^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025252709 10000000000 40322121708877 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026318907/5000000000 : ℝ), (5672109431/10000000000 : ℝ), (5025252709/10000000000 : ℝ)] ![(12367634679353/100000000000000 : ℝ), (2365512179799/5000000000000 : ℝ), (40322121708877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026318907/5000000000 : ℝ)|^8449 ≤ (12367634679353/100000000000000 : ℝ)^6401
        have hw : |(-1026318907/5000000000 : ℝ)|=(1026318907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5672109431/10000000000 : ℝ)|^8449 ≤ (2365512179799/5000000000000 : ℝ)^6401
        have hw : |(5672109431/10000000000 : ℝ)|=(5672109431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025252709/10000000000 : ℝ)|^8449 ≤ (40322121708877/100000000000000 : ℝ)^6401
        have hw : |(5025252709/10000000000 : ℝ)|=(5025252709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706449877/5000000000 : ℝ)*x 0 + (-2399761109/10000000000 : ℝ)*x 1 + (2512626459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706449877/5000000000 : ℝ)^8449 ≤ (11119388751163/25000000000000 : ℝ)^6401 := by
    have hnat : (2706449877 : ℕ)^8449*25000000000000^6401 ≤ 11119388751163^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706449877 5000000000 11119388751163 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2399761109/10000000000 : ℝ)^8449 ≤ (7600160526979/50000000000000 : ℝ)^6401 := by
    have hnat : (2399761109 : ℕ)^8449*50000000000000^6401 ≤ 7600160526979^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399761109 10000000000 7600160526979 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512626459/5000000000 : ℝ)^8449 ≤ (20161061961213/50000000000000 : ℝ)^6401 := by
    have hnat : (2512626459 : ℕ)^8449*50000000000000^6401 ≤ 20161061961213^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512626459 5000000000 20161061961213 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706449877/5000000000 : ℝ), (-2399761109/10000000000 : ℝ), (2512626459/5000000000 : ℝ)] ![(11119388751163/25000000000000 : ℝ), (7600160526979/50000000000000 : ℝ), (20161061961213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706449877/5000000000 : ℝ)|^8449 ≤ (11119388751163/25000000000000 : ℝ)^6401
        have hw : |(2706449877/5000000000 : ℝ)|=(2706449877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2399761109/10000000000 : ℝ)|^8449 ≤ (7600160526979/50000000000000 : ℝ)^6401
        have hw : |(-2399761109/10000000000 : ℝ)|=(2399761109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512626459/5000000000 : ℝ)|^8449 ≤ (20161061961213/50000000000000 : ℝ)^6401
        have hw : |(2512626459/5000000000 : ℝ)|=(2512626459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (676612493/1250000000 : ℝ)*x 0 + (5025252791/10000000000 : ℝ)*x 1 + (-2399761023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676612493/1250000000 : ℝ)^8449 ≤ (22238778532693/50000000000000 : ℝ)^6401 := by
    have hnat : (676612493 : ℕ)^8449*50000000000000^6401 ≤ 22238778532693^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676612493 1250000000 22238778532693 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5025252791/10000000000 : ℝ)^8449 ≤ (40322122577351/100000000000000 : ℝ)^6401 := by
    have hnat : (5025252791 : ℕ)^8449*100000000000000^6401 ≤ 40322122577351^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025252791 10000000000 40322122577351 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2399761023/10000000000 : ℝ)^8449 ≤ (15200320334939/100000000000000 : ℝ)^6401 := by
    have hnat : (2399761023 : ℕ)^8449*100000000000000^6401 ≤ 15200320334939^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399761023 10000000000 15200320334939 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676612493/1250000000 : ℝ), (5025252791/10000000000 : ℝ), (-2399761023/10000000000 : ℝ)] ![(22238778532693/50000000000000 : ℝ), (40322122577351/100000000000000 : ℝ), (15200320334939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676612493/1250000000 : ℝ)|^8449 ≤ (22238778532693/50000000000000 : ℝ)^6401
        have hw : |(676612493/1250000000 : ℝ)|=(676612493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5025252791/10000000000 : ℝ)|^8449 ≤ (40322122577351/100000000000000 : ℝ)^6401
        have hw : |(5025252791/10000000000 : ℝ)|=(5025252791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2399761023/10000000000 : ℝ)|^8449 ≤ (15200320334939/100000000000000 : ℝ)^6401
        have hw : |(-2399761023/10000000000 : ℝ)|=(2399761023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s1_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43076377/100000000 : ℝ)*x 0 + (3697963003/10000000000 : ℝ)*x 1 + (5013706061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43076377/100000000 : ℝ)^8449 ≤ (16450685240927/50000000000000 : ℝ)^6401 := by
    have hnat : (43076377 : ℕ)^8449*50000000000000^6401 ≤ 16450685240927^6401*100000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43076377 100000000 16450685240927 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3697963003/10000000000 : ℝ)^8449 ≤ (6724688763343/25000000000000 : ℝ)^6401 := by
    have hnat : (3697963003 : ℕ)^8449*25000000000000^6401 ≤ 6724688763343^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3697963003 10000000000 6724688763343 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5013706061/10000000000 : ℝ)^8449 ≤ (2009993722507/5000000000000 : ℝ)^6401 := by
    have hnat : (5013706061 : ℕ)^8449*5000000000000^6401 ≤ 2009993722507^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013706061 10000000000 2009993722507 5000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43076377/100000000 : ℝ), (3697963003/10000000000 : ℝ), (5013706061/10000000000 : ℝ)] ![(16450685240927/50000000000000 : ℝ), (6724688763343/25000000000000 : ℝ), (2009993722507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43076377/100000000 : ℝ)|^8449 ≤ (16450685240927/50000000000000 : ℝ)^6401
        have hw : |(43076377/100000000 : ℝ)|=(43076377/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3697963003/10000000000 : ℝ)|^8449 ≤ (6724688763343/25000000000000 : ℝ)^6401
        have hw : |(3697963003/10000000000 : ℝ)|=(3697963003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5013706061/10000000000 : ℝ)|^8449 ≤ (2009993722507/5000000000000 : ℝ)^6401
        have hw : |(5013706061/10000000000 : ℝ)|=(5013706061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s1_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2053297633/10000000000 : ℝ)*x 0 + (157303227/312500000 : ℝ)*x 1 + (5663499061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053297633/10000000000 : ℝ)^8449 ≤ (12372882499641/100000000000000 : ℝ)^6401 := by
    have hnat : (2053297633 : ℕ)^8449*100000000000000^6401 ≤ 12372882499641^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053297633 10000000000 12372882499641 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157303227/312500000 : ℝ)^8449 ≤ (2020582341917/5000000000000 : ℝ)^6401 := by
    have hnat : (157303227 : ℕ)^8449*5000000000000^6401 ≤ 2020582341917^6401*312500000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157303227 312500000 2020582341917 5000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663499061/10000000000 : ℝ)^8449 ≤ (1888618826139/4000000000000 : ℝ)^6401 := by
    have hnat : (5663499061 : ℕ)^8449*4000000000000^6401 ≤ 1888618826139^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663499061 10000000000 1888618826139 4000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2053297633/10000000000 : ℝ), (157303227/312500000 : ℝ), (5663499061/10000000000 : ℝ)] ![(12372882499641/100000000000000 : ℝ), (2020582341917/5000000000000 : ℝ), (1888618826139/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2053297633/10000000000 : ℝ)|^8449 ≤ (12372882499641/100000000000000 : ℝ)^6401
        have hw : |(-2053297633/10000000000 : ℝ)|=(2053297633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157303227/312500000 : ℝ)|^8449 ≤ (2020582341917/5000000000000 : ℝ)^6401
        have hw : |(157303227/312500000 : ℝ)|=(157303227/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663499061/10000000000 : ℝ)|^8449 ≤ (1888618826139/4000000000000 : ℝ)^6401
        have hw : |(5663499061/10000000000 : ℝ)|=(5663499061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s1_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246140637/10000000000 : ℝ)*x 0 + (-55047333/312500000 : ℝ)*x 1 + (5663499411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246140637/10000000000 : ℝ)^8449 ≤ (42677867612707/100000000000000 : ℝ)^6401 := by
    have hnat : (5246140637 : ℕ)^8449*100000000000000^6401 ≤ 42677867612707^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246140637 10000000000 42677867612707 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55047333/312500000 : ℝ)^8449 ≤ (10106657869101/100000000000000 : ℝ)^6401 := by
    have hnat : (55047333 : ℕ)^8449*100000000000000^6401 ≤ 10106657869101^6401*312500000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55047333 312500000 10106657869101 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663499411/10000000000 : ℝ)^8449 ≤ (47215474504931/100000000000000 : ℝ)^6401 := by
    have hnat : (5663499411 : ℕ)^8449*100000000000000^6401 ≤ 47215474504931^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663499411 10000000000 47215474504931 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246140637/10000000000 : ℝ), (-55047333/312500000 : ℝ), (5663499411/10000000000 : ℝ)] ![(42677867612707/100000000000000 : ℝ), (10106657869101/100000000000000 : ℝ), (47215474504931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246140637/10000000000 : ℝ)|^8449 ≤ (42677867612707/100000000000000 : ℝ)^6401
        have hw : |(5246140637/10000000000 : ℝ)|=(5246140637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55047333/312500000 : ℝ)|^8449 ≤ (10106657869101/100000000000000 : ℝ)^6401
        have hw : |(-55047333/312500000 : ℝ)|=(55047333/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663499411/10000000000 : ℝ)|^8449 ≤ (47215474504931/100000000000000 : ℝ)^6401
        have hw : |(5663499411/10000000000 : ℝ)|=(5663499411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2623070279/5000000000 : ℝ)*x 0 + (5663499169/10000000000 : ℝ)*x 1 + (-1761515119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623070279/5000000000 : ℝ)^8449 ≤ (42677866764411/100000000000000 : ℝ)^6401 := by
    have hnat : (2623070279 : ℕ)^8449*100000000000000^6401 ≤ 42677866764411^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623070279 5000000000 42677866764411 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5663499169/10000000000 : ℝ)^8449 ≤ (11803867960481/25000000000000 : ℝ)^6401 := by
    have hnat : (5663499169 : ℕ)^8449*25000000000000^6401 ≤ 11803867960481^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663499169 10000000000 11803867960481 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761515119/10000000000 : ℝ)^8449 ≤ (10106661375487/100000000000000 : ℝ)^6401 := by
    have hnat : (1761515119 : ℕ)^8449*100000000000000^6401 ≤ 10106661375487^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761515119 10000000000 10106661375487 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623070279/5000000000 : ℝ), (5663499169/10000000000 : ℝ), (-1761515119/10000000000 : ℝ)] ![(42677866764411/100000000000000 : ℝ), (11803867960481/25000000000000 : ℝ), (10106661375487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623070279/5000000000 : ℝ)|^8449 ≤ (42677866764411/100000000000000 : ℝ)^6401
        have hw : |(2623070279/5000000000 : ℝ)|=(2623070279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5663499169/10000000000 : ℝ)|^8449 ≤ (11803867960481/25000000000000 : ℝ)^6401
        have hw : |(5663499169/10000000000 : ℝ)|=(5663499169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761515119/10000000000 : ℝ)|^8449 ≤ (10106661375487/100000000000000 : ℝ)^6401
        have hw : |(-1761515119/10000000000 : ℝ)|=(1761515119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s1_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4308979591/10000000000 : ℝ)*x 0 + (312282333/625000000 : ℝ)*x 1 + (3715477223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308979591/10000000000 : ℝ)^8449 ≤ (8228724913191/25000000000000 : ℝ)^6401 := by
    have hnat : (4308979591 : ℕ)^8449*25000000000000^6401 ≤ 8228724913191^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308979591 10000000000 8228724913191 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312282333/625000000 : ℝ)^8449 ≤ (40018059857779/100000000000000 : ℝ)^6401 := by
    have hnat : (312282333 : ℕ)^8449*100000000000000^6401 ≤ 40018059857779^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312282333 625000000 40018059857779 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3715477223/10000000000 : ℝ)^8449 ≤ (27067040467993/100000000000000 : ℝ)^6401 := by
    have hnat : (3715477223 : ℕ)^8449*100000000000000^6401 ≤ 27067040467993^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3715477223 10000000000 27067040467993 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308979591/10000000000 : ℝ), (312282333/625000000 : ℝ), (3715477223/10000000000 : ℝ)] ![(8228724913191/25000000000000 : ℝ), (40018059857779/100000000000000 : ℝ), (27067040467993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308979591/10000000000 : ℝ)|^8449 ≤ (8228724913191/25000000000000 : ℝ)^6401
        have hw : |(4308979591/10000000000 : ℝ)|=(4308979591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312282333/625000000 : ℝ)|^8449 ≤ (40018059857779/100000000000000 : ℝ)^6401
        have hw : |(312282333/625000000 : ℝ)|=(312282333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3715477223/10000000000 : ℝ)|^8449 ≤ (27067040467993/100000000000000 : ℝ)^6401
        have hw : |(3715477223/10000000000 : ℝ)|=(3715477223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3423/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (437/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (783/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (997/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3423/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (437/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3423/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (437/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3423/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (437/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3423/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (437/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3423/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (437/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3423/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (437/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (437/50000 : ℝ) ^ (33/8 : ℝ) ≤ (64530444299/20000000000000000000 : ℝ) := by
    have hpowers : (437/50000 : ℝ)^33 ≤ (64530444299/20000000000000000000 : ℝ)^8 := by
      have hnat : (437 : ℕ)^33*20000000000000000000^8 ≤ 64530444299^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        437 50000 64530444299 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (437/50000 : ℝ)) (X := (64530444299/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (3423/12500 : ℝ) ^ (33/8 : ℝ) ≤ (239135834285158231/50000000000000000000 : ℝ) := by
    have hpowers : (3423/12500 : ℝ)^33 ≤ (239135834285158231/50000000000000000000 : ℝ)^8 := by
      have hnat : (3423 : ℕ)^33*50000000000000000000^8 ≤ 239135834285158231^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3423 12500 239135834285158231 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3423/12500 : ℝ)) (X := (239135834285158231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000064530444299/10000000000000000000 : ℝ) ≤ (2000000003128749/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (10000000064530444299/10000000000000000000 : ℝ)^8 ≤ (2000000003128749/2000000000000000 : ℝ)^33 := by
      have hnat : (10000000064530444299 : ℕ)^8*2000000000000000^33 ≤ 2000000003128749^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000064530444299 10000000000000000000 2000000003128749 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000003128749/2000000000000000 : ℝ)) (X := (10000000064530444299/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (100478271991222537957/100000000000000000000 : ℝ) ≤ (10011573526209351/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100478271991222537957/100000000000000000000 : ℝ)^8 ≤ (10011573526209351/10000000000000000 : ℝ)^33 := by
      have hnat : (100478271991222537957 : ℕ)^8*10000000000000000^33 ≤ 10011573526209351^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100478271991222537957 100000000000000000000 10011573526209351 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011573526209351/10000000000000000 : ℝ)) (X := (100478271991222537957/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (25239135834285158231/25000000000000000000 : ℝ) ≤ (10023147036774957/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25239135834285158231/25000000000000000000 : ℝ)^8 ≤ (10023147036774957/10000000000000000 : ℝ)^33 := by
      have hnat : (25239135834285158231 : ℕ)^8*10000000000000000^33 ≤ 10023147036774957^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25239135834285158231 25000000000000000000 10023147036774957 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023147036774957/10000000000000000 : ℝ)) (X := (25239135834285158231/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(64530444299/20000000000000000000 : ℝ) ≤ ((12049080450829409121/12050000000000000000 : ℝ)+2*(526068662073/120500000000000 : ℝ)*(437/50000 : ℝ))^(33/8 : ℝ) := by
    rw [show (12049080450829409121/12050000000000000000 : ℝ)+2*(526068662073/120500000000000 : ℝ)*(437/50000 : ℝ)=(2000000003128749/2000000000000000 : ℝ) by norm_num, show 1+2*(64530444299/20000000000000000000 : ℝ)=(10000000064530444299/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(239135834285158231/50000000000000000000 : ℝ)+(64530444299/20000000000000000000 : ℝ) ≤ ((12049080450829409121/12050000000000000000 : ℝ)+(526068662073/120500000000000 : ℝ)*((3423/12500 : ℝ)+(437/50000 : ℝ)))^(33/8 : ℝ) := by
    rw [show (12049080450829409121/12050000000000000000 : ℝ)+(526068662073/120500000000000 : ℝ)*((3423/12500 : ℝ)+(437/50000 : ℝ))=(10011573526209351/10000000000000000 : ℝ) by norm_num, show 1+(239135834285158231/50000000000000000000 : ℝ)+(64530444299/20000000000000000000 : ℝ)=(100478271991222537957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(239135834285158231/50000000000000000000 : ℝ) ≤ ((12049080450829409121/12050000000000000000 : ℝ)+2*(526068662073/120500000000000 : ℝ)*(3423/12500 : ℝ))^(33/8 : ℝ) := by
    rw [show (12049080450829409121/12050000000000000000 : ℝ)+2*(526068662073/120500000000000 : ℝ)*(3423/12500 : ℝ)=(10023147036774957/10000000000000000 : ℝ) by norm_num, show 1+2*(239135834285158231/50000000000000000000 : ℝ)=(25239135834285158231/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12049080450829409121/12050000000000000000 : ℝ)*(X 1 0+X 2 0)+(526068662073/120500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (437/50000 : ℝ)) (hi := (3423/12500 : ℝ)) (c := (12049080450829409121/12050000000000000000 : ℝ)) (alpha := (526068662073/120500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12049080450829409121/12050000000000000000 : ℝ)*(X 0 1+X 2 1)+(526068662073/120500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (437/50000 : ℝ)) (hi := (3423/12500 : ℝ)) (c := (12049080450829409121/12050000000000000000 : ℝ)) (alpha := (526068662073/120500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12049080450829409121/12050000000000000000 : ℝ)*(X 0 2+X 1 2)+(526068662073/120500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (437/50000 : ℝ)) (hi := (3423/12500 : ℝ)) (c := (12049080450829409121/12050000000000000000 : ℝ)) (alpha := (526068662073/120500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1026318907/5000000000 : ℝ)*X 0 0+(5672109431/10000000000 : ℝ)*X 0 1+(5025252709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706449877/5000000000 : ℝ)*X 1 0+(-2399761109/10000000000 : ℝ)*X 1 1+(2512626459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676612493/1250000000 : ℝ)*X 2 0+(5025252791/10000000000 : ℝ)*X 2 1+(-2399761023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43076377/100000000 : ℝ)*X 0 0+(3697963003/10000000000 : ℝ)*X 0 1+(5013706061/10000000000 : ℝ)*X 0 2+(43076377/100000000 : ℝ)*X 1 0+(3697963003/10000000000 : ℝ)*X 1 1+(5013706061/10000000000 : ℝ)*X 1 2+(43076377/100000000 : ℝ)*X 2 0+(3697963003/10000000000 : ℝ)*X 2 1+(5013706061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2053297633/10000000000 : ℝ)*X 0 0+(157303227/312500000 : ℝ)*X 0 1+(5663499061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246140637/10000000000 : ℝ)*X 1 0+(-55047333/312500000 : ℝ)*X 1 1+(5663499411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2623070279/5000000000 : ℝ)*X 2 0+(5663499169/10000000000 : ℝ)*X 2 1+(-1761515119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308979591/10000000000 : ℝ)*X 0 0+(312282333/625000000 : ℝ)*X 0 1+(3715477223/10000000000 : ℝ)*X 0 2+(4308979591/10000000000 : ℝ)*X 1 0+(312282333/625000000 : ℝ)*X 1 1+(3715477223/10000000000 : ℝ)*X 1 2+(4308979591/10000000000 : ℝ)*X 2 0+(312282333/625000000 : ℝ)*X 2 1+(3715477223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31954991172226909627923/6025000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4655837/10000000000000 : ℝ)*(base1) + (593916511/50000000000000 : ℝ)*(base19) + (1242097937/100000000000000 : ℝ)*(base23) + (492667/400000000000 : ℝ)*(upper3) + (169546763/100000000000000 : ℝ)*(upper5) + (1152992885480439/100000000000000 : ℝ)*(major0) + (1152992885480439/100000000000000 : ℝ)*(major1) + (1152992885480439/100000000000000 : ℝ)*(major2) + (1545944069735563/100000000000000 : ℝ)*(sp0) + (24155473494989/1562500000000 : ℝ)*(sp1) + (77297512470719/5000000000000 : ℝ)*(sp2) + (380015231108907/50000000000000 : ℝ)*(sp3) + (1867083781/25000000000000 : ℝ)*(sp4) + (449235159/12500000000000 : ℝ)*(sp7) + (760034102657457/100000000000000 : ℝ)*(f.failure) + (1545951491512317/100000000000000 : ℝ)*(f.sum) + (8974277147403/6025000000000000000000000000 : ℝ)*base66 + (3552353866943384119/1205000000000000000000000000000000 : ℝ)*base67 + (4169877780826615881/1205000000000000000000000000000000 : ℝ)*base70 + (2257125483301615881/1205000000000000000000000000000000 : ℝ)*base72 + (3576784608803/6025000000000000000000000000 : ℝ)*base74 + (8355417562211615881/1205000000000000000000000000000000 : ℝ)*base76 + (1452465165818384119/1205000000000000000000000000000000 : ℝ)*base77 + (3169772161788384119/1205000000000000000000000000000000 : ℝ)*base79 + (30470035919203/6025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (22602831/10000000000000000000000 : ℝ)*base89 + (22602831/10000000000000000000000 : ℝ)*base91 + (22602831/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124255249660137784244175969/15062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25643801/50000000000000 : ℝ)*(base1) + (1613776773/100000000000000 : ℝ)*(base19) + (311839457/20000000000000 : ℝ)*(base23) + (211554497/100000000000000 : ℝ)*(upper3) + (181173273/100000000000000 : ℝ)*(upper5) + (1184215902170521/100000000000000 : ℝ)*(major0) + (1184215902170521/100000000000000 : ℝ)*(major1) + (592107951085261/50000000000000 : ℝ)*(major2) + (8065641141/100000000000000 : ℝ)*(sp1) + (3550399371/50000000000000 : ℝ)*(sp2) + (793907887348659/50000000000000 : ℝ)*(sp4) + (793903021995901/50000000000000 : ℝ)*(sp5) + (158780706341369/10000000000000 : ℝ)*(sp6) + (390307877333339/50000000000000 : ℝ)*(sp7) + (780615805954279/100000000000000 : ℝ)*(f.failure) + (396953930852429/25000000000000 : ℝ)*(f.sum) + (21931079506061/12050000000000000000000000000 : ℝ)*base66 + (5863294089854677959/1205000000000000000000000000000000 : ℝ)*base68 + (4151058865643715581/602500000000000000000000000000000 : ℝ)*base69 + (7686415167604677959/1205000000000000000000000000000000 : ℝ)*base72 + (22331627519011/12050000000000000000000000000 : ℝ)*base74 + (2937196294288715581/602500000000000000000000000000000 : ℝ)*base75 + (7534500131211977959/1205000000000000000000000000000000 : ℝ)*base78 + (8270912684961977959/1205000000000000000000000000000000 : ℝ)*base80 + (24972381666583/6025000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4941543/10000000000000000000000 : ℝ)*base90 + (4941543/10000000000000000000000 : ℝ)*base92 + (104941543/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1256_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3423/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (437/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (783/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (997/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1256_s2_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-419997131/2000000000 : ℝ)*x 0 + (5490428307/10000000000 : ℝ)*x 1 + (323545351/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419997131/2000000000 : ℝ)^8449 ≤ (12745575119643/100000000000000 : ℝ)^6401 := by
    have hnat : (419997131 : ℕ)^8449*100000000000000^6401 ≤ 12745575119643^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419997131 2000000000 12745575119643 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490428307/10000000000 : ℝ)^8449 ≤ (9064069571211/20000000000000 : ℝ)^6401 := by
    have hnat : (5490428307 : ℕ)^8449*20000000000000^6401 ≤ 9064069571211^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490428307 10000000000 9064069571211 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323545351/625000000 : ℝ)^8449 ≤ (20967038504313/50000000000000 : ℝ)^6401 := by
    have hnat : (323545351 : ℕ)^8449*50000000000000^6401 ≤ 20967038504313^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323545351 625000000 20967038504313 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419997131/2000000000 : ℝ), (5490428307/10000000000 : ℝ), (323545351/625000000 : ℝ)] ![(12745575119643/100000000000000 : ℝ), (9064069571211/20000000000000 : ℝ), (20967038504313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419997131/2000000000 : ℝ)|^8449 ≤ (12745575119643/100000000000000 : ℝ)^6401
        have hw : |(-419997131/2000000000 : ℝ)|=(419997131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490428307/10000000000 : ℝ)|^8449 ≤ (9064069571211/20000000000000 : ℝ)^6401
        have hw : |(5490428307/10000000000 : ℝ)|=(5490428307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323545351/625000000 : ℝ)|^8449 ≤ (20967038504313/50000000000000 : ℝ)^6401
        have hw : |(323545351/625000000 : ℝ)|=(323545351/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s2_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684560783/5000000000 : ℝ)*x 0 + (-452480609/2000000000 : ℝ)*x 1 + (5176725749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684560783/5000000000 : ℝ)^8449 ≤ (11000838387847/25000000000000 : ℝ)^6401 := by
    have hnat : (2684560783 : ℕ)^8449*25000000000000^6401 ≤ 11000838387847^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684560783 5000000000 11000838387847 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452480609/2000000000 : ℝ)^8449 ≤ (703128400193/5000000000000 : ℝ)^6401 := by
    have hnat : (452480609 : ℕ)^8449*5000000000000^6401 ≤ 703128400193^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452480609 2000000000 703128400193 5000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176725749/10000000000 : ℝ)^8449 ≤ (41934078430697/100000000000000 : ℝ)^6401 := by
    have hnat : (5176725749 : ℕ)^8449*100000000000000^6401 ≤ 41934078430697^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176725749 10000000000 41934078430697 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684560783/5000000000 : ℝ), (-452480609/2000000000 : ℝ), (5176725749/10000000000 : ℝ)] ![(11000838387847/25000000000000 : ℝ), (703128400193/5000000000000 : ℝ), (41934078430697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684560783/5000000000 : ℝ)|^8449 ≤ (11000838387847/25000000000000 : ℝ)^6401
        have hw : |(2684560783/5000000000 : ℝ)|=(2684560783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452480609/2000000000 : ℝ)|^8449 ≤ (703128400193/5000000000000 : ℝ)^6401
        have hw : |(-452480609/2000000000 : ℝ)|=(452480609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176725749/10000000000 : ℝ)|^8449 ≤ (41934078430697/100000000000000 : ℝ)^6401
        have hw : |(5176725749/10000000000 : ℝ)|=(5176725749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s2_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369121471/10000000000 : ℝ)*x 0 + (5176725799/10000000000 : ℝ)*x 1 + (-452480621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369121471/10000000000 : ℝ)^8449 ≤ (8800670504739/20000000000000 : ℝ)^6401 := by
    have hnat : (5369121471 : ℕ)^8449*20000000000000^6401 ≤ 8800670504739^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369121471 10000000000 8800670504739 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176725799/10000000000 : ℝ)^8449 ≤ (4193407896531/10000000000000 : ℝ)^6401 := by
    have hnat : (5176725799 : ℕ)^8449*10000000000000^6401 ≤ 4193407896531^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176725799 10000000000 4193407896531 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452480621/2000000000 : ℝ)^8449 ≤ (1406256849613/10000000000000 : ℝ)^6401 := by
    have hnat : (452480621 : ℕ)^8449*10000000000000^6401 ≤ 1406256849613^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452480621 2000000000 1406256849613 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369121471/10000000000 : ℝ), (5176725799/10000000000 : ℝ), (-452480621/2000000000 : ℝ)] ![(8800670504739/20000000000000 : ℝ), (4193407896531/10000000000000 : ℝ), (1406256849613/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369121471/10000000000 : ℝ)|^8449 ≤ (8800670504739/20000000000000 : ℝ)^6401
        have hw : |(5369121471/10000000000 : ℝ)|=(5369121471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176725799/10000000000 : ℝ)|^8449 ≤ (4193407896531/10000000000000 : ℝ)^6401
        have hw : |(5176725799/10000000000 : ℝ)|=(5176725799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452480621/2000000000 : ℝ)|^8449 ≤ (1406256849613/10000000000000 : ℝ)^6401
        have hw : |(-452480621/2000000000 : ℝ)|=(452480621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s2_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4340370919/10000000000 : ℝ)*x 0 + (4032648667/10000000000 : ℝ)*x 1 + (4670736983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340370919/10000000000 : ℝ)^8449 ≤ (4153972042047/12500000000000 : ℝ)^6401 := by
    have hnat : (4340370919 : ℕ)^8449*12500000000000^6401 ≤ 4153972042047^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340370919 10000000000 4153972042047 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032648667/10000000000 : ℝ)^8449 ≤ (30157756355653/100000000000000 : ℝ)^6401 := by
    have hnat : (4032648667 : ℕ)^8449*100000000000000^6401 ≤ 30157756355653^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032648667 10000000000 30157756355653 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4670736983/10000000000 : ℝ)^8449 ≤ (36610467288009/100000000000000 : ℝ)^6401 := by
    have hnat : (4670736983 : ℕ)^8449*100000000000000^6401 ≤ 36610467288009^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4670736983 10000000000 36610467288009 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340370919/10000000000 : ℝ), (4032648667/10000000000 : ℝ), (4670736983/10000000000 : ℝ)] ![(4153972042047/12500000000000 : ℝ), (30157756355653/100000000000000 : ℝ), (36610467288009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340370919/10000000000 : ℝ)|^8449 ≤ (4153972042047/12500000000000 : ℝ)^6401
        have hw : |(4340370919/10000000000 : ℝ)|=(4340370919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032648667/10000000000 : ℝ)|^8449 ≤ (30157756355653/100000000000000 : ℝ)^6401
        have hw : |(4032648667/10000000000 : ℝ)|=(4032648667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4670736983/10000000000 : ℝ)|^8449 ≤ (36610467288009/100000000000000 : ℝ)^6401
        have hw : |(4670736983/10000000000 : ℝ)|=(4670736983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s2_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100061219/10000000000 : ℝ)*x 0 + (5178722941/10000000000 : ℝ)*x 1 + (1372103107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100061219/10000000000 : ℝ)^8449 ≤ (12746180485651/100000000000000 : ℝ)^6401 := by
    have hnat : (2100061219 : ℕ)^8449*100000000000000^6401 ≤ 12746180485651^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100061219 10000000000 12746180485651 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178722941/10000000000 : ℝ)^8449 ≤ (20977717120317/50000000000000 : ℝ)^6401 := by
    have hnat : (5178722941 : ℕ)^8449*50000000000000^6401 ≤ 20977717120317^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178722941 10000000000 20977717120317 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372103107/2500000000 : ℝ)^8449 ≤ (45298385271763/100000000000000 : ℝ)^6401 := by
    have hnat : (1372103107 : ℕ)^8449*100000000000000^6401 ≤ 45298385271763^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372103107 2500000000 45298385271763 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100061219/10000000000 : ℝ), (5178722941/10000000000 : ℝ), (1372103107/2500000000 : ℝ)] ![(12746180485651/100000000000000 : ℝ), (20977717120317/50000000000000 : ℝ), (45298385271763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100061219/10000000000 : ℝ)|^8449 ≤ (12746180485651/100000000000000 : ℝ)^6401
        have hw : |(-2100061219/10000000000 : ℝ)|=(2100061219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178722941/10000000000 : ℝ)|^8449 ≤ (20977717120317/50000000000000 : ℝ)^6401
        have hw : |(5178722941/10000000000 : ℝ)|=(5178722941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372103107/2500000000 : ℝ)|^8449 ≤ (45298385271763/100000000000000 : ℝ)^6401
        have hw : |(1372103107/2500000000 : ℝ)|=(1372103107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s2_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644470419/5000000000 : ℝ)*x 0 + (-1950716109/10000000000 : ℝ)*x 1 + (5488412473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644470419/5000000000 : ℝ)^8449 ≤ (5392256446713/12500000000000 : ℝ)^6401 := by
    have hnat : (2644470419 : ℕ)^8449*12500000000000^6401 ≤ 5392256446713^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644470419 5000000000 5392256446713 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950716109/10000000000 : ℝ)^8449 ≤ (1445445331159/12500000000000 : ℝ)^6401 := by
    have hnat : (1950716109 : ℕ)^8449*12500000000000^6401 ≤ 1445445331159^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950716109 10000000000 1445445331159 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488412473/10000000000 : ℝ)^8449 ≤ (45298385761999/100000000000000 : ℝ)^6401 := by
    have hnat : (5488412473 : ℕ)^8449*100000000000000^6401 ≤ 45298385761999^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488412473 10000000000 45298385761999 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644470419/5000000000 : ℝ), (-1950716109/10000000000 : ℝ), (5488412473/10000000000 : ℝ)] ![(5392256446713/12500000000000 : ℝ), (1445445331159/12500000000000 : ℝ), (45298385761999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644470419/5000000000 : ℝ)|^8449 ≤ (5392256446713/12500000000000 : ℝ)^6401
        have hw : |(2644470419/5000000000 : ℝ)|=(2644470419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950716109/10000000000 : ℝ)|^8449 ≤ (1445445331159/12500000000000 : ℝ)^6401
        have hw : |(-1950716109/10000000000 : ℝ)|=(1950716109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488412473/10000000000 : ℝ)|^8449 ≤ (45298385761999/100000000000000 : ℝ)^6401
        have hw : |(5488412473/10000000000 : ℝ)|=(5488412473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s2_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644470489/5000000000 : ℝ)*x 0 + (171512893/312500000 : ℝ)*x 1 + (-1950715773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644470489/5000000000 : ℝ)^8449 ≤ (21569026540463/50000000000000 : ℝ)^6401 := by
    have hnat : (2644470489 : ℕ)^8449*50000000000000^6401 ≤ 21569026540463^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644470489 5000000000 21569026540463 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171512893/312500000 : ℝ)^8449 ≤ (45298386884097/100000000000000 : ℝ)^6401 := by
    have hnat : (171512893 : ℕ)^8449*100000000000000^6401 ≤ 45298386884097^6401*312500000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171512893 312500000 45298386884097 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950715773/10000000000 : ℝ)^8449 ≤ (46254240081/400000000000 : ℝ)^6401 := by
    have hnat : (1950715773 : ℕ)^8449*400000000000^6401 ≤ 46254240081^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950715773 10000000000 46254240081 400000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644470489/5000000000 : ℝ), (171512893/312500000 : ℝ), (-1950715773/10000000000 : ℝ)] ![(21569026540463/50000000000000 : ℝ), (45298386884097/100000000000000 : ℝ), (46254240081/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644470489/5000000000 : ℝ)|^8449 ≤ (21569026540463/50000000000000 : ℝ)^6401
        have hw : |(2644470489/5000000000 : ℝ)|=(2644470489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171512893/312500000 : ℝ)|^8449 ≤ (45298386884097/100000000000000 : ℝ)^6401
        have hw : |(171512893/312500000 : ℝ)|=(171512893/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950715773/10000000000 : ℝ)|^8449 ≤ (46254240081/400000000000 : ℝ)^6401
        have hw : |(-1950715773/10000000000 : ℝ)|=(1950715773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (868104829/2000000000 : ℝ)*x 0 + (233333737/500000000 : ℝ)*x 1 + (2018374127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868104829/2000000000 : ℝ)^8449 ≤ (33233324864549/100000000000000 : ℝ)^6401 := by
    have hnat : (868104829 : ℕ)^8449*100000000000000^6401 ≤ 33233324864549^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868104829 2000000000 33233324864549 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233333737/500000000 : ℝ)^8449 ≤ (18284222349741/50000000000000 : ℝ)^6401 := by
    have hnat : (233333737 : ℕ)^8449*50000000000000^6401 ≤ 18284222349741^6401*500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233333737 500000000 18284222349741 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018374127/5000000000 : ℝ)^8449 ≤ (3019823042197/10000000000000 : ℝ)^6401 := by
    have hnat : (2018374127 : ℕ)^8449*10000000000000^6401 ≤ 3019823042197^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018374127 5000000000 3019823042197 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868104829/2000000000 : ℝ), (233333737/500000000 : ℝ), (2018374127/5000000000 : ℝ)] ![(33233324864549/100000000000000 : ℝ), (18284222349741/50000000000000 : ℝ), (3019823042197/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868104829/2000000000 : ℝ)|^8449 ≤ (33233324864549/100000000000000 : ℝ)^6401
        have hw : |(868104829/2000000000 : ℝ)|=(868104829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(233333737/500000000 : ℝ)|^8449 ≤ (18284222349741/50000000000000 : ℝ)^6401
        have hw : |(233333737/500000000 : ℝ)|=(233333737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2018374127/5000000000 : ℝ)|^8449 ≤ (3019823042197/10000000000000 : ℝ)^6401
        have hw : |(2018374127/5000000000 : ℝ)|=(2018374127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (997/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (783/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2389/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16187/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (997/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (783/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (997/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (783/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (997/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (783/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (997/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (783/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (997/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (783/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (997/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (783/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (783/12500 : ℝ) ^ (33/8 : ℝ) ≤ (136120481869603/12500000000000000000 : ℝ) := by
    have hpowers : (783/12500 : ℝ)^33 ≤ (136120481869603/12500000000000000000 : ℝ)^8 := by
      have hnat : (783 : ℕ)^33*12500000000000000000^8 ≤ 136120481869603^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        783 12500 136120481869603 12500000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (783/12500 : ℝ)) (X := (136120481869603/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (997/5000 : ℝ) ^ (33/8 : ℝ) ≤ (16153858455571107/12500000000000000000 : ℝ) := by
    have hpowers : (997/5000 : ℝ)^33 ≤ (16153858455571107/12500000000000000000 : ℝ)^8 := by
      have hnat : (997 : ℕ)^33*12500000000000000000^8 ≤ 16153858455571107^8*5000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        997 5000 16153858455571107 12500000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (997/5000 : ℝ)) (X := (16153858455571107/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250136120481869603/6250000000000000000 : ℝ) ≤ (2500013199452987/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (6250136120481869603/6250000000000000000 : ℝ)^8 ≤ (2500013199452987/2500000000000000 : ℝ)^33 := by
      have hnat : (6250136120481869603 : ℕ)^8*2500000000000000^33 ≤ 2500013199452987^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250136120481869603 6250000000000000000 2500013199452987 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500013199452987/2500000000000000 : ℝ)) (X := (6250136120481869603/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (1251628997893744071/1250000000000000000 : ℝ) ≤ (62519735689401/62500000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1251628997893744071/1250000000000000000 : ℝ)^8 ≤ (62519735689401/62500000000000 : ℝ)^33 := by
      have hnat : (1251628997893744071 : ℕ)^8*62500000000000^33 ≤ 62519735689401^33*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251628997893744071 1250000000000000000 62519735689401 62500000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62519735689401/62500000000000 : ℝ)) (X := (1251628997893744071/1250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (6266153858455571107/6250000000000000000 : ℝ) ≤ (2501565655699093/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (6266153858455571107/6250000000000000000 : ℝ)^8 ≤ (2501565655699093/2500000000000000 : ℝ)^33 := by
      have hnat : (6266153858455571107 : ℕ)^8*2500000000000000^33 ≤ 2501565655699093^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6266153858455571107 6250000000000000000 2501565655699093 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501565655699093/2500000000000000 : ℝ)) (X := (6266153858455571107/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(136120481869603/12500000000000000000 : ℝ) ≤ ((8545113982448360557/8547500000000000000 : ℝ)+2*(776228123053/341900000000000 : ℝ)*(783/12500 : ℝ))^(33/8 : ℝ) := by
    rw [show (8545113982448360557/8547500000000000000 : ℝ)+2*(776228123053/341900000000000 : ℝ)*(783/12500 : ℝ)=(2500013199452987/2500000000000000 : ℝ) by norm_num, show 1+2*(136120481869603/12500000000000000000 : ℝ)=(6250136120481869603/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16153858455571107/12500000000000000000 : ℝ)+(136120481869603/12500000000000000000 : ℝ) ≤ ((8545113982448360557/8547500000000000000 : ℝ)+(776228123053/341900000000000 : ℝ)*((997/5000 : ℝ)+(783/12500 : ℝ)))^(33/8 : ℝ) := by
    rw [show (8545113982448360557/8547500000000000000 : ℝ)+(776228123053/341900000000000 : ℝ)*((997/5000 : ℝ)+(783/12500 : ℝ))=(62519735689401/62500000000000 : ℝ) by norm_num, show 1+(16153858455571107/12500000000000000000 : ℝ)+(136120481869603/12500000000000000000 : ℝ)=(1251628997893744071/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16153858455571107/12500000000000000000 : ℝ) ≤ ((8545113982448360557/8547500000000000000 : ℝ)+2*(776228123053/341900000000000 : ℝ)*(997/5000 : ℝ))^(33/8 : ℝ) := by
    rw [show (8545113982448360557/8547500000000000000 : ℝ)+2*(776228123053/341900000000000 : ℝ)*(997/5000 : ℝ)=(2501565655699093/2500000000000000 : ℝ) by norm_num, show 1+2*(16153858455571107/12500000000000000000 : ℝ)=(6266153858455571107/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8545113982448360557/8547500000000000000 : ℝ)*(X 1 0+X 2 0)+(776228123053/341900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (783/12500 : ℝ)) (hi := (997/5000 : ℝ)) (c := (8545113982448360557/8547500000000000000 : ℝ)) (alpha := (776228123053/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8545113982448360557/8547500000000000000 : ℝ)*(X 0 1+X 2 1)+(776228123053/341900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (783/12500 : ℝ)) (hi := (997/5000 : ℝ)) (c := (8545113982448360557/8547500000000000000 : ℝ)) (alpha := (776228123053/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8545113982448360557/8547500000000000000 : ℝ)*(X 0 2+X 1 2)+(776228123053/341900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (783/12500 : ℝ)) (hi := (997/5000 : ℝ)) (c := (8545113982448360557/8547500000000000000 : ℝ)) (alpha := (776228123053/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419997131/2000000000 : ℝ)*X 0 0+(5490428307/10000000000 : ℝ)*X 0 1+(323545351/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684560783/5000000000 : ℝ)*X 1 0+(-452480609/2000000000 : ℝ)*X 1 1+(5176725749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369121471/10000000000 : ℝ)*X 2 0+(5176725799/10000000000 : ℝ)*X 2 1+(-452480621/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340370919/10000000000 : ℝ)*X 0 0+(4032648667/10000000000 : ℝ)*X 0 1+(4670736983/10000000000 : ℝ)*X 0 2+(4340370919/10000000000 : ℝ)*X 1 0+(4032648667/10000000000 : ℝ)*X 1 1+(4670736983/10000000000 : ℝ)*X 1 2+(4340370919/10000000000 : ℝ)*X 2 0+(4032648667/10000000000 : ℝ)*X 2 1+(4670736983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2100061219/10000000000 : ℝ)*X 0 0+(5178722941/10000000000 : ℝ)*X 0 1+(1372103107/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644470419/5000000000 : ℝ)*X 1 0+(-1950716109/10000000000 : ℝ)*X 1 1+(5488412473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644470489/5000000000 : ℝ)*X 2 0+(171512893/312500000 : ℝ)*X 2 1+(-1950715773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868104829/2000000000 : ℝ)*X 0 0+(233333737/500000000 : ℝ)*X 0 1+(2018374127/5000000000 : ℝ)*X 0 2+(868104829/2000000000 : ℝ)*X 1 0+(233333737/500000000 : ℝ)*X 1 1+(2018374127/5000000000 : ℝ)*X 1 2+(868104829/2000000000 : ℝ)*X 2 0+(233333737/500000000 : ℝ)*X 2 1+(2018374127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (383100485885871893558481561/106843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (573527763/100000000000000 : ℝ)*(base19) + (24512309/5000000000000 : ℝ)*(base23) + (1803913/12500000000000 : ℝ)*(lower2) + (108597243/100000000000000 : ℝ)*(upper3) + (32036649/100000000000000 : ℝ)*(upper5) + (1188733622896659/50000000000000 : ℝ)*(major0) + (1188733622896659/50000000000000 : ℝ)*(major1) + (1188733622896659/50000000000000 : ℝ)*(major2) + (1593869996637113/50000000000000 : ℝ)*(sp0) + (1593873085504643/50000000000000 : ℝ)*(sp1) + (796936563572717/25000000000000 : ℝ)*(sp2) + (783592039325197/50000000000000 : ℝ)*(sp3) + (3375631411/50000000000000 : ℝ)*(sp4) + (709775741/20000000000000 : ℝ)*(sp7) + (1567187627529099/100000000000000 : ℝ)*(f.failure) + (398468343067131/12500000000000 : ℝ)*(f.sum) + (50087194956131/17095000000000000000000000000 : ℝ)*base66 + (7425051342098604063/427375000000000000000000000000000 : ℝ)*base67 + (498449541553645937/427375000000000000000000000000000 : ℝ)*base70 + (2615657379811729063/427375000000000000000000000000000 : ℝ)*base71 + (57640948362097/8547500000000000000000000000 : ℝ)*base73 + (463836478164104063/427375000000000000000000000000000 : ℝ)*base75 + (987715508450729063/427375000000000000000000000000000 : ℝ)*base77 + (5813852443659604063/427375000000000000000000000000000 : ℝ)*base79 + (24523148485593/8547500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (68217483/10000000000000000000000 : ℝ)*base90 + (68217483/10000000000000000000000 : ℝ)*base92 + (68217483/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25470375214599190380401763/4273750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63565077/4000000000000 : ℝ)*(base19) + (23171807/1250000000000 : ℝ)*(base23) + (44556429/100000000000000 : ℝ)*(upper2) + (27776951/12500000000000 : ℝ)*(upper3) + (28589059/25000000000000 : ℝ)*(upper5) + (48165269091997/2000000000000 : ℝ)*(major0) + (48165269091997/2000000000000 : ℝ)*(major1) + (48165269091997/2000000000000 : ℝ)*(major2) + (16338956639/100000000000000 : ℝ)*(sp1) + (706214089/3125000000000 : ℝ)*(sp2) + (1614519362255539/50000000000000 : ℝ)*(sp4) + (1614510398213757/50000000000000 : ℝ)*(sp5) + (322901427191567/10000000000000 : ℝ)*(sp6) + (1587487986031113/100000000000000 : ℝ)*(sp7) + (1587487986031113/100000000000000 : ℝ)*(f.failure) + (1614519362255539/50000000000000 : ℝ)*(f.sum) + (11296825308547/3419000000000000000000000000 : ℝ)*base66 + (127523051552477329/17095000000000000000000000000000 : ℝ)*base67 + (107575270980017329/17095000000000000000000000000000 : ℝ)*base69 + (65425621788042329/17095000000000000000000000000000 : ℝ)*base71 + (4328149875869/3419000000000000000000000000 : ℝ)*base73 + (26875234676137671/17095000000000000000000000000000 : ℝ)*base76 + (67964412854152329/17095000000000000000000000000000 : ℝ)*base77 + (114071798252447329/17095000000000000000000000000000 : ℝ)*base79 + (511870688661/1709500000000000000000000000 : ℝ)*base81 + (33312521/10000000000000000000000 : ℝ)*base90 + (33312521/10000000000000000000000 : ℝ)*base92 + (33312521/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1256_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (997/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (783/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16187/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1256_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16187/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1256_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1256_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1256_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16187/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
