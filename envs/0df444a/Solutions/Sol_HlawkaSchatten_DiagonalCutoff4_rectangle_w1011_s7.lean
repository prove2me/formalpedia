-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1011_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:01:19.812558+00:00
-- url     : https://prove2.me/submissions/8c0baa71-a559-4f3b-b683-6b7873a0af83

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
theorem support_rectangle_w1011_s7_0 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-446225929/2000000000 : ℝ)*x 0 + (337215439/625000000 : ℝ)*x 1 + (5263259917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446225929/2000000000 : ℝ)^2051 ≤ (13545334042399/100000000000000 : ℝ)^1539 := by
    have hnat : (446225929 : ℕ)^2051*100000000000000^1539 ≤ 13545334042399^1539*2000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446225929 2000000000 13545334042399 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337215439/625000000 : ℝ)^2051 ≤ (5492718951567/12500000000000 : ℝ)^1539 := by
    have hnat : (337215439 : ℕ)^2051*12500000000000^1539 ≤ 5492718951567^1539*625000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337215439 625000000 5492718951567 12500000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263259917/10000000000 : ℝ)^2051 ≤ (8502582865269/20000000000000 : ℝ)^1539 := by
    have hnat : (5263259917 : ℕ)^2051*20000000000000^1539 ≤ 8502582865269^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263259917 10000000000 8502582865269 20000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446225929/2000000000 : ℝ), (337215439/625000000 : ℝ), (5263259917/10000000000 : ℝ)] ![(13545334042399/100000000000000 : ℝ), (5492718951567/12500000000000 : ℝ), (8502582865269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446225929/2000000000 : ℝ)|^2051 ≤ (13545334042399/100000000000000 : ℝ)^1539
        have hw : |(-446225929/2000000000 : ℝ)|=(446225929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337215439/625000000 : ℝ)|^2051 ≤ (5492718951567/12500000000000 : ℝ)^1539
        have hw : |(337215439/625000000 : ℝ)|=(337215439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263259917/10000000000 : ℝ)|^2051 ≤ (8502582865269/20000000000000 : ℝ)^1539
        have hw : |(5263259917/10000000000 : ℝ)|=(5263259917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1011_s7_1 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672556071/5000000000 : ℝ)*x 0 + (-2298214671/10000000000 : ℝ)*x 1 + (164476873/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672556071/5000000000 : ℝ)^2051 ≤ (43396282518879/100000000000000 : ℝ)^1539 := by
    have hnat : (2672556071 : ℕ)^2051*100000000000000^1539 ≤ 43396282518879^1539*5000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672556071 5000000000 43396282518879 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2298214671/10000000000 : ℝ)^2051 ≤ (14090802934257/100000000000000 : ℝ)^1539 := by
    have hnat : (2298214671 : ℕ)^2051*100000000000000^1539 ≤ 14090802934257^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298214671 10000000000 14090802934257 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164476873/312500000 : ℝ)^2051 ≤ (4251291453087/10000000000000 : ℝ)^1539 := by
    have hnat : (164476873 : ℕ)^2051*10000000000000^1539 ≤ 4251291453087^1539*312500000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164476873 312500000 4251291453087 10000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672556071/5000000000 : ℝ), (-2298214671/10000000000 : ℝ), (164476873/312500000 : ℝ)] ![(43396282518879/100000000000000 : ℝ), (14090802934257/100000000000000 : ℝ), (4251291453087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672556071/5000000000 : ℝ)|^2051 ≤ (43396282518879/100000000000000 : ℝ)^1539
        have hw : |(2672556071/5000000000 : ℝ)|=(2672556071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2298214671/10000000000 : ℝ)|^2051 ≤ (14090802934257/100000000000000 : ℝ)^1539
        have hw : |(-2298214671/10000000000 : ℝ)|=(2298214671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164476873/312500000 : ℝ)|^2051 ≤ (4251291453087/10000000000000 : ℝ)^1539
        have hw : |(164476873/312500000 : ℝ)|=(164476873/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1011_s7_2 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069022429/2000000000 : ℝ)*x 0 + (2631629961/5000000000 : ℝ)*x 1 + (-1149107343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069022429/2000000000 : ℝ)^2051 ≤ (21698141275669/50000000000000 : ℝ)^1539 := by
    have hnat : (1069022429 : ℕ)^2051*50000000000000^1539 ≤ 21698141275669^1539*2000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069022429 2000000000 21698141275669 50000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631629961/5000000000 : ℝ)^2051 ≤ (5314114297521/12500000000000 : ℝ)^1539 := by
    have hnat : (2631629961 : ℕ)^2051*12500000000000^1539 ≤ 5314114297521^1539*5000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631629961 5000000000 5314114297521 12500000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149107343/5000000000 : ℝ)^2051 ≤ (14090803056821/100000000000000 : ℝ)^1539 := by
    have hnat : (1149107343 : ℕ)^2051*100000000000000^1539 ≤ 14090803056821^1539*5000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149107343 5000000000 14090803056821 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069022429/2000000000 : ℝ), (2631629961/5000000000 : ℝ), (-1149107343/5000000000 : ℝ)] ![(21698141275669/50000000000000 : ℝ), (5314114297521/12500000000000 : ℝ), (14090803056821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069022429/2000000000 : ℝ)|^2051 ≤ (21698141275669/50000000000000 : ℝ)^1539
        have hw : |(1069022429/2000000000 : ℝ)|=(1069022429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631629961/5000000000 : ℝ)|^2051 ≤ (5314114297521/12500000000000 : ℝ)^1539
        have hw : |(2631629961/5000000000 : ℝ)|=(2631629961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1149107343/5000000000 : ℝ)|^2051 ≤ (14090803056821/100000000000000 : ℝ)^1539
        have hw : |(-1149107343/5000000000 : ℝ)|=(1149107343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1011_s7_3 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4383454873/10000000000 : ℝ)*x 0 + (4257255439/10000000000 : ℝ)*x 1 + (4513498229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4383454873/10000000000 : ℝ)^2051 ≤ (16658074319719/50000000000000 : ℝ)^1539 := by
    have hnat : (4383454873 : ℕ)^2051*50000000000000^1539 ≤ 16658074319719^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383454873 10000000000 16658074319719 50000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4257255439/10000000000 : ℝ)^2051 ≤ (16022019809231/50000000000000 : ℝ)^1539 := by
    have hnat : (4257255439 : ℕ)^2051*50000000000000^1539 ≤ 16022019809231^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257255439 10000000000 16022019809231 50000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513498229/10000000000 : ℝ)^2051 ≤ (6927962346881/20000000000000 : ℝ)^1539 := by
    have hnat : (4513498229 : ℕ)^2051*20000000000000^1539 ≤ 6927962346881^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513498229 10000000000 6927962346881 20000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4383454873/10000000000 : ℝ), (4257255439/10000000000 : ℝ), (4513498229/10000000000 : ℝ)] ![(16658074319719/50000000000000 : ℝ), (16022019809231/50000000000000 : ℝ), (6927962346881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4383454873/10000000000 : ℝ)|^2051 ≤ (16658074319719/50000000000000 : ℝ)^1539
        have hw : |(4383454873/10000000000 : ℝ)|=(4383454873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4257255439/10000000000 : ℝ)|^2051 ≤ (16022019809231/50000000000000 : ℝ)^1539
        have hw : |(4257255439/10000000000 : ℝ)|=(4257255439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513498229/10000000000 : ℝ)|^2051 ≤ (6927962346881/20000000000000 : ℝ)^1539
        have hw : |(4513498229/10000000000 : ℝ)|=(4513498229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1011_s7_4 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2231134733/10000000000 : ℝ)*x 0 + (1315897771/2500000000 : ℝ)*x 1 + (269755739/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2231134733/10000000000 : ℝ)^2051 ≤ (13545375208451/100000000000000 : ℝ)^1539 := by
    have hnat : (2231134733 : ℕ)^2051*100000000000000^1539 ≤ 13545375208451^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231134733 10000000000 13545375208451 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315897771/2500000000 : ℝ)^2051 ≤ (42516479204577/100000000000000 : ℝ)^1539 := by
    have hnat : (1315897771 : ℕ)^2051*100000000000000^1539 ≤ 42516479204577^1539*2500000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315897771 2500000000 42516479204577 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269755739/500000000 : ℝ)^2051 ≤ (5492268197469/12500000000000 : ℝ)^1539 := by
    have hnat : (269755739 : ℕ)^2051*12500000000000^1539 ≤ 5492268197469^1539*500000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269755739 500000000 5492268197469 12500000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2231134733/10000000000 : ℝ), (1315897771/2500000000 : ℝ), (269755739/500000000 : ℝ)] ![(13545375208451/100000000000000 : ℝ), (42516479204577/100000000000000 : ℝ), (5492268197469/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2231134733/10000000000 : ℝ)|^2051 ≤ (13545375208451/100000000000000 : ℝ)^1539
        have hw : |(-2231134733/10000000000 : ℝ)|=(2231134733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315897771/2500000000 : ℝ)|^2051 ≤ (42516479204577/100000000000000 : ℝ)^1539
        have hw : |(1315897771/2500000000 : ℝ)|=(1315897771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269755739/500000000 : ℝ)|^2051 ≤ (5492268197469/12500000000000 : ℝ)^1539
        have hw : |(269755739/500000000 : ℝ)|=(269755739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1011_s7_5 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311965743/10000000000 : ℝ)*x 0 + (-1083180007/5000000000 : ℝ)*x 1 + (33719467/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311965743/10000000000 : ℝ)^2051 ≤ (5379751583511/12500000000000 : ℝ)^1539 := by
    have hnat : (5311965743 : ℕ)^2051*12500000000000^1539 ≤ 5379751583511^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311965743 10000000000 5379751583511 12500000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083180007/5000000000 : ℝ)^2051 ≤ (3255960598501/25000000000000 : ℝ)^1539 := by
    have hnat : (1083180007 : ℕ)^2051*25000000000000^1539 ≤ 3255960598501^1539*5000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083180007 5000000000 3255960598501 25000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33719467/62500000 : ℝ)^2051 ≤ (1373067029017/3125000000000 : ℝ)^1539 := by
    have hnat : (33719467 : ℕ)^2051*3125000000000^1539 ≤ 1373067029017^1539*62500000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33719467 62500000 1373067029017 3125000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311965743/10000000000 : ℝ), (-1083180007/5000000000 : ℝ), (33719467/62500000 : ℝ)] ![(5379751583511/12500000000000 : ℝ), (3255960598501/25000000000000 : ℝ), (1373067029017/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311965743/10000000000 : ℝ)|^2051 ≤ (5379751583511/12500000000000 : ℝ)^1539
        have hw : |(5311965743/10000000000 : ℝ)|=(5311965743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1083180007/5000000000 : ℝ)|^2051 ≤ (3255960598501/25000000000000 : ℝ)^1539
        have hw : |(-1083180007/5000000000 : ℝ)|=(1083180007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33719467/62500000 : ℝ)|^2051 ≤ (1373067029017/3125000000000 : ℝ)^1539
        have hw : |(33719467/62500000 : ℝ)|=(33719467/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1011_s7_6 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311965851/10000000000 : ℝ)*x 0 + (5395114641/10000000000 : ℝ)*x 1 + (-86654399/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311965851/10000000000 : ℝ)^2051 ≤ (2151900691711/5000000000000 : ℝ)^1539 := by
    have hnat : (5311965851 : ℕ)^2051*5000000000000^1539 ≤ 2151900691711^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311965851 10000000000 2151900691711 5000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395114641/10000000000 : ℝ)^2051 ≤ (43938144071121/100000000000000 : ℝ)^1539 := by
    have hnat : (5395114641 : ℕ)^2051*100000000000000^1539 ≤ 43938144071121^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395114641 10000000000 43938144071121 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86654399/400000000 : ℝ)^2051 ≤ (651192104077/5000000000000 : ℝ)^1539 := by
    have hnat : (86654399 : ℕ)^2051*5000000000000^1539 ≤ 651192104077^1539*400000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86654399 400000000 651192104077 5000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311965851/10000000000 : ℝ), (5395114641/10000000000 : ℝ), (-86654399/400000000 : ℝ)] ![(2151900691711/5000000000000 : ℝ), (43938144071121/100000000000000 : ℝ), (651192104077/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311965851/10000000000 : ℝ)|^2051 ≤ (2151900691711/5000000000000 : ℝ)^1539
        have hw : |(5311965851/10000000000 : ℝ)|=(5311965851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395114641/10000000000 : ℝ)|^2051 ≤ (43938144071121/100000000000000 : ℝ)^1539
        have hw : |(5395114641/10000000000 : ℝ)|=(5395114641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86654399/400000000 : ℝ)|^2051 ≤ (651192104077/5000000000000 : ℝ)^1539
        have hw : |(-86654399/400000000 : ℝ)|=(86654399/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1011_s7_7 (p : ℝ) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1095866227/2500000000 : ℝ)*x 0 + (564107047/1250000000 : ℝ)*x 1 + (4257899729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095866227/2500000000 : ℝ)^2051 ≤ (8329062570923/25000000000000 : ℝ)^1539 := by
    have hnat : (1095866227 : ℕ)^2051*25000000000000^1539 ≤ 8329062570923^1539*2500000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095866227 2500000000 8329062570923 25000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564107047/1250000000 : ℝ)^2051 ≤ (34633247038867/100000000000000 : ℝ)^1539 := by
    have hnat : (564107047 : ℕ)^2051*100000000000000^1539 ≤ 34633247038867^1539*1250000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564107047 1250000000 34633247038867 100000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4257899729/10000000000 : ℝ)^2051 ≤ (16025251329759/50000000000000 : ℝ)^1539 := by
    have hnat : (4257899729 : ℕ)^2051*50000000000000^1539 ≤ 16025251329759^1539*10000000000^2051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257899729 10000000000 16025251329759 50000000000000 2051 1539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2051/512 : ℝ)) 2051 1539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1095866227/2500000000 : ℝ), (564107047/1250000000 : ℝ), (4257899729/10000000000 : ℝ)] ![(8329062570923/25000000000000 : ℝ), (34633247038867/100000000000000 : ℝ), (16025251329759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1095866227/2500000000 : ℝ)|^2051 ≤ (8329062570923/25000000000000 : ℝ)^1539
        have hw : |(1095866227/2500000000 : ℝ)|=(1095866227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564107047/1250000000 : ℝ)|^2051 ≤ (34633247038867/100000000000000 : ℝ)^1539
        have hw : |(564107047/1250000000 : ℝ)|=(564107047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4257899729/10000000000 : ℝ)|^2051 ≤ (16025251329759/50000000000000 : ℝ)^1539
        have hw : |(4257899729/10000000000 : ℝ)|=(4257899729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1011_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73462137/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11171/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13971/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11159/100000 : ℝ) ^ (8203/2048 : ℝ) ≤ (15324482460273609/100000000000000000000 : ℝ) := by
    have hpowers : (11159/100000 : ℝ)^8203 ≤ (15324482460273609/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11159 : ℕ)^8203*100000000000000000000^2048 ≤ 15324482460273609^2048*100000^8203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11159 100000 15324482460273609 100000000000000000000 8203 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11159/100000 : ℝ)) (X := (15324482460273609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8203 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13983/100000 : ℝ) ^ (8203/2048 : ℝ) ≤ (18913955998887797/50000000000000000000 : ℝ) := by
    have hpowers : (13983/100000 : ℝ)^8203 ≤ (18913955998887797/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13983 : ℕ)^8203*50000000000000000000^2048 ≤ 18913955998887797^2048*100000^8203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13983 100000 18913955998887797 50000000000000000000 8203 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13983/100000 : ℝ)) (X := (18913955998887797/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8203 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015324482460273609/50000000000000000000 : ℝ) ≤ (625047819291681/625000000000000 : ℝ) ^ (8203/2048 : ℝ) := by
    have hpowers : (50015324482460273609/50000000000000000000 : ℝ)^2048 ≤ (625047819291681/625000000000000 : ℝ)^8203 := by
      have hnat : (50015324482460273609 : ℕ)^2048*625000000000000^8203 ≤ 625047819291681^8203*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015324482460273609 50000000000000000000 625047819291681 625000000000000 2048 8203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625047819291681/625000000000000 : ℝ)) (X := (50015324482460273609/50000000000000000000 : ℝ)) (by norm_num) 8203 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053152394458049203/100000000000000000000 : ℝ) ≤ (10001326763422177/10000000000000000 : ℝ) ^ (8203/2048 : ℝ) := by
    have hpowers : (100053152394458049203/100000000000000000000 : ℝ)^2048 ≤ (10001326763422177/10000000000000000 : ℝ)^8203 := by
      have hnat : (100053152394458049203 : ℕ)^2048*10000000000000000^8203 ≤ 10001326763422177^8203*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053152394458049203 100000000000000000000 10001326763422177 10000000000000000 2048 8203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001326763422177/10000000000000000 : ℝ)) (X := (100053152394458049203/100000000000000000000 : ℝ)) (by norm_num) 8203 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018913955998887797/25000000000000000000 : ℝ) ≤ (5000944209088729/5000000000000000 : ℝ) ^ (8203/2048 : ℝ) := by
    have hpowers : (25018913955998887797/25000000000000000000 : ℝ)^2048 ≤ (5000944209088729/5000000000000000 : ℝ)^8203 := by
      have hnat : (25018913955998887797 : ℕ)^2048*5000000000000000^8203 ≤ 5000944209088729^8203*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018913955998887797 25000000000000000000 5000944209088729 5000000000000000 2048 8203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000944209088729/5000000000000000 : ℝ)) (X := (25018913955998887797/25000000000000000000 : ℝ)) (by norm_num) 8203 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15324482460273609/100000000000000000000 : ℝ) ≤ ((14114812828023476473/14120000000000000000 : ℝ)+2*(561654755281/282400000000000 : ℝ)*(11159/100000 : ℝ))^(8203/2048 : ℝ) := by
    rw [show (14114812828023476473/14120000000000000000 : ℝ)+2*(561654755281/282400000000000 : ℝ)*(11159/100000 : ℝ)=(625047819291681/625000000000000 : ℝ) by norm_num, show 1+2*(15324482460273609/100000000000000000000 : ℝ)=(50015324482460273609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18913955998887797/50000000000000000000 : ℝ)+(15324482460273609/100000000000000000000 : ℝ) ≤ ((14114812828023476473/14120000000000000000 : ℝ)+(561654755281/282400000000000 : ℝ)*((13983/100000 : ℝ)+(11159/100000 : ℝ)))^(8203/2048 : ℝ) := by
    rw [show (14114812828023476473/14120000000000000000 : ℝ)+(561654755281/282400000000000 : ℝ)*((13983/100000 : ℝ)+(11159/100000 : ℝ))=(10001326763422177/10000000000000000 : ℝ) by norm_num, show 1+(18913955998887797/50000000000000000000 : ℝ)+(15324482460273609/100000000000000000000 : ℝ)=(100053152394458049203/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18913955998887797/50000000000000000000 : ℝ) ≤ ((14114812828023476473/14120000000000000000 : ℝ)+2*(561654755281/282400000000000 : ℝ)*(13983/100000 : ℝ))^(8203/2048 : ℝ) := by
    rw [show (14114812828023476473/14120000000000000000 : ℝ)+2*(561654755281/282400000000000 : ℝ)*(13983/100000 : ℝ)=(5000944209088729/5000000000000000 : ℝ) by norm_num, show 1+2*(18913955998887797/50000000000000000000 : ℝ)=(25018913955998887797/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14114812828023476473/14120000000000000000 : ℝ)*(X 1 0+X 2 0)+(561654755281/282400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8203/2048 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (14114812828023476473/14120000000000000000 : ℝ)) (alpha := (561654755281/282400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14114812828023476473/14120000000000000000 : ℝ)*(X 0 1+X 2 1)+(561654755281/282400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8203/2048 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (14114812828023476473/14120000000000000000 : ℝ)) (alpha := (561654755281/282400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14114812828023476473/14120000000000000000 : ℝ)*(X 0 2+X 1 2)+(561654755281/282400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8203/2048 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (14114812828023476473/14120000000000000000 : ℝ)) (alpha := (561654755281/282400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-446225929/2000000000 : ℝ)*X 0 0+(337215439/625000000 : ℝ)*X 0 1+(5263259917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672556071/5000000000 : ℝ)*X 1 0+(-2298214671/10000000000 : ℝ)*X 1 1+(164476873/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069022429/2000000000 : ℝ)*X 2 0+(2631629961/5000000000 : ℝ)*X 2 1+(-1149107343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4383454873/10000000000 : ℝ)*X 0 0+(4257255439/10000000000 : ℝ)*X 0 1+(4513498229/10000000000 : ℝ)*X 0 2+(4383454873/10000000000 : ℝ)*X 1 0+(4257255439/10000000000 : ℝ)*X 1 1+(4513498229/10000000000 : ℝ)*X 1 2+(4383454873/10000000000 : ℝ)*X 2 0+(4257255439/10000000000 : ℝ)*X 2 1+(4513498229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2231134733/10000000000 : ℝ)*X 0 0+(1315897771/2500000000 : ℝ)*X 0 1+(269755739/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311965743/10000000000 : ℝ)*X 1 0+(-1083180007/5000000000 : ℝ)*X 1 1+(33719467/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311965851/10000000000 : ℝ)*X 2 0+(5395114641/10000000000 : ℝ)*X 2 1+(-86654399/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1095866227/2500000000 : ℝ)*X 0 0+(564107047/1250000000 : ℝ)*X 0 1+(4257899729/10000000000 : ℝ)*X 0 2+(1095866227/2500000000 : ℝ)*X 1 0+(564107047/1250000000 : ℝ)*X 1 1+(4257899729/10000000000 : ℝ)*X 1 2+(1095866227/2500000000 : ℝ)*X 2 0+(564107047/1250000000 : ℝ)*X 2 1+(4257899729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1011_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177071118740927350195559037/44125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199912973/25000000000000 : ℝ)*(base19) + (734973969/100000000000000 : ℝ)*(base23) + (7368119/20000000000000 : ℝ)*(lower2) + (118154863/100000000000000 : ℝ)*(upper3) + (44531853/100000000000000 : ℝ)*(upper5) + (358364067675377/6250000000000 : ℝ)*(major0) + (358364067675377/6250000000000 : ℝ)*(major1) + (358364067675377/6250000000000 : ℝ)*(major2) + (3782528756684251/50000000000000 : ℝ)*(sp0) + (7565077569458403/100000000000000 : ℝ)*(sp1) + (302603105365453/4000000000000 : ℝ)*(sp2) + (3902559289591799/100000000000000 : ℝ)*(sp3) + (651741931/3125000000000 : ℝ)*(sp4) + (6186572589/50000000000000 : ℝ)*(sp7) + (243910728921061/6250000000000 : ℝ)*(f.failure) + (3782539184555147/50000000000000 : ℝ)*(f.sum) + (9449563064251/1765000000000000000000000000 : ℝ)*base66 + (711146514571505321/88250000000000000000000000000000 : ℝ)*base67 + (1131791854975005321/88250000000000000000000000000000 : ℝ)*base69 + (1499279985437505321/88250000000000000000000000000000 : ℝ)*base71 + (3070188779867/882500000000000000000000000 : ℝ)*base73 + (2541051546585494679/88250000000000000000000000000000 : ℝ)*base76 + (1069142534149244679/88250000000000000000000000000000 : ℝ)*base78 + (1810013798541005321/88250000000000000000000000000000 : ℝ)*base79 + (7256665034879/1765000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4632643/312500000000000000000 : ℝ)*base90 + (4632643/312500000000000000000 : ℝ)*base92 + (4632643/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7478990923251378645991409211/706000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1187582593/100000000000000 : ℝ)*(base19) + (1688538569/100000000000000 : ℝ)*(base23) + (102589249/100000000000000 : ℝ)*(upper3) + (153271131/100000000000000 : ℝ)*(lower4) + (78778023/50000000000000 : ℝ)*(upper5) + (5762713717594769/100000000000000 : ℝ)*(major0) + (5762713717594769/100000000000000 : ℝ)*(major1) + (5762713717594769/100000000000000 : ℝ)*(major2) + (30234758153/100000000000000 : ℝ)*(sp1) + (39503009607/100000000000000 : ℝ)*(sp2) + (380159657897699/5000000000000 : ℝ)*(sp4) + (3801580867806617/50000000000000 : ℝ)*(sp5) + (1900787991601451/25000000000000 : ℝ)*(sp6) + (980558481029957/25000000000000 : ℝ)*(sp7) + (980558481029957/25000000000000 : ℝ)*(f.failure) + (380159657897699/5000000000000 : ℝ)*(f.sum) + (78787132931009/14120000000000000000000000000 : ℝ)*base65 + (9532724347502180263/1412000000000000000000000000000000 : ℝ)*base68 + (6970430382529819737/1412000000000000000000000000000000 : ℝ)*base69 + (25692729445729819737/1412000000000000000000000000000000 : ℝ)*base71 + (24027981032409/14120000000000000000000000000 : ℝ)*base73 + (15983942880126180263/1412000000000000000000000000000000 : ℝ)*base76 + (209478113242180263/1412000000000000000000000000000000 : ℝ)*base78 + (28455688517078180263/1412000000000000000000000000000000 : ℝ)*base80 + (36800821187889/14120000000000000000000000000 : ℝ)*base81 + (10261891/1250000000000000000000 : ℝ)*base90 + (10261891/1250000000000000000000 : ℝ)*base92 + (10261891/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1011_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73462137/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13971/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1011_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73462137/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13971/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1011_s7 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
