-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1017_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:06:48.258892+00:00
-- url     : https://prove2.me/submissions/5234992a-aebc-4c74-b37a-8ac024601ee0

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
theorem support_rectangle_w1017_box_0 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096948141/10000000000 : ℝ)*x 0 + (2689009759/5000000000 : ℝ)*x 1 + (67225239/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096948141/10000000000 : ℝ)^4105 ≤ (12477018824661/100000000000000 : ℝ)^3081 := by
    have hnat : (2096948141 : ℕ)^4105*100000000000000^3081 ≤ 12477018824661^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096948141 10000000000 12477018824661 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689009759/5000000000 : ℝ)^4105 ≤ (21880746369029/50000000000000 : ℝ)^3081 := by
    have hnat : (2689009759 : ℕ)^4105*50000000000000^3081 ≤ 21880746369029^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689009759 5000000000 21880746369029 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67225239/125000000 : ℝ)^4105 ≤ (43761488423123/100000000000000 : ℝ)^3081 := by
    have hnat : (67225239 : ℕ)^4105*100000000000000^3081 ≤ 43761488423123^3081*125000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67225239 125000000 43761488423123 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096948141/10000000000 : ℝ), (2689009759/5000000000 : ℝ), (67225239/125000000 : ℝ)] ![(12477018824661/100000000000000 : ℝ), (21880746369029/50000000000000 : ℝ), (43761488423123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096948141/10000000000 : ℝ)|^4105 ≤ (12477018824661/100000000000000 : ℝ)^3081
        have hw : |(-2096948141/10000000000 : ℝ)|=(2096948141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689009759/5000000000 : ℝ)|^4105 ≤ (21880746369029/50000000000000 : ℝ)^3081
        have hw : |(2689009759/5000000000 : ℝ)|=(2689009759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67225239/125000000 : ℝ)|^4105 ≤ (43761488423123/100000000000000 : ℝ)^3081
        have hw : |(67225239/125000000 : ℝ)|=(67225239/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_1 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529461793/1000000000 : ℝ)*x 0 + (-17677709/80000000 : ℝ)*x 1 + (5378019387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529461793/1000000000 : ℝ)^4105 ≤ (857192577871/2000000000000 : ℝ)^3081 := by
    have hnat : (529461793 : ℕ)^4105*2000000000000^3081 ≤ 857192577871^3081*1000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529461793 1000000000 857192577871 2000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17677709/80000000 : ℝ)^4105 ≤ (6689439888913/50000000000000 : ℝ)^3081 := by
    have hnat : (17677709 : ℕ)^4105*50000000000000^3081 ≤ 6689439888913^3081*80000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17677709 80000000 6689439888913 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378019387/10000000000 : ℝ)^4105 ≤ (5470186414727/12500000000000 : ℝ)^3081 := by
    have hnat : (5378019387 : ℕ)^4105*12500000000000^3081 ≤ 5470186414727^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378019387 10000000000 5470186414727 12500000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529461793/1000000000 : ℝ), (-17677709/80000000 : ℝ), (5378019387/10000000000 : ℝ)] ![(857192577871/2000000000000 : ℝ), (6689439888913/50000000000000 : ℝ), (5470186414727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529461793/1000000000 : ℝ)|^4105 ≤ (857192577871/2000000000000 : ℝ)^3081
        have hw : |(529461793/1000000000 : ℝ)|=(529461793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17677709/80000000 : ℝ)|^4105 ≤ (6689439888913/50000000000000 : ℝ)^3081
        have hw : |(-17677709/80000000 : ℝ)|=(17677709/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378019387/10000000000 : ℝ)|^4105 ≤ (5470186414727/12500000000000 : ℝ)^3081
        have hw : |(5378019387/10000000000 : ℝ)|=(5378019387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_2 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647309013/5000000000 : ℝ)*x 0 + (2689009627/5000000000 : ℝ)*x 1 + (-88388547/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647309013/5000000000 : ℝ)^4105 ≤ (21429814964473/50000000000000 : ℝ)^3081 := by
    have hnat : (2647309013 : ℕ)^4105*50000000000000^3081 ≤ 21429814964473^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647309013 5000000000 21429814964473 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689009627/5000000000 : ℝ)^4105 ≤ (4376148987589/10000000000000 : ℝ)^3081 := by
    have hnat : (2689009627 : ℕ)^4105*10000000000000^3081 ≤ 4376148987589^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689009627 5000000000 4376148987589 10000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88388547/400000000 : ℝ)^4105 ≤ (1337888018117/10000000000000 : ℝ)^3081 := by
    have hnat : (88388547 : ℕ)^4105*10000000000000^3081 ≤ 1337888018117^3081*400000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88388547 400000000 1337888018117 10000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647309013/5000000000 : ℝ), (2689009627/5000000000 : ℝ), (-88388547/400000000 : ℝ)] ![(21429814964473/50000000000000 : ℝ), (4376148987589/10000000000000 : ℝ), (1337888018117/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647309013/5000000000 : ℝ)|^4105 ≤ (21429814964473/50000000000000 : ℝ)^3081
        have hw : |(2647309013/5000000000 : ℝ)|=(2647309013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689009627/5000000000 : ℝ)|^4105 ≤ (4376148987589/10000000000000 : ℝ)^3081
        have hw : |(2689009627/5000000000 : ℝ)|=(2689009627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88388547/400000000 : ℝ)|^4105 ≤ (1337888018117/10000000000000 : ℝ)^3081
        have hw : |(-88388547/400000000 : ℝ)|=(88388547/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_3 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4491548967/10000000000 : ℝ)*x 0 + (4330306841/10000000000 : ℝ)*x 1 + (866061313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4491548967/10000000000 : ℝ)^4105 ≤ (6884884293267/20000000000000 : ℝ)^3081 := by
    have hnat : (4491548967 : ℕ)^4105*20000000000000^3081 ≤ 6884884293267^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491548967 10000000000 6884884293267 20000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4330306841/10000000000 : ℝ)^4105 ≤ (32787790651333/100000000000000 : ℝ)^3081 := by
    have hnat : (4330306841 : ℕ)^4105*100000000000000^3081 ≤ 32787790651333^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330306841 10000000000 32787790651333 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866061313/2000000000 : ℝ)^4105 ≤ (16393893933491/50000000000000 : ℝ)^3081 := by
    have hnat : (866061313 : ℕ)^4105*50000000000000^3081 ≤ 16393893933491^3081*2000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866061313 2000000000 16393893933491 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4491548967/10000000000 : ℝ), (4330306841/10000000000 : ℝ), (866061313/2000000000 : ℝ)] ![(6884884293267/20000000000000 : ℝ), (32787790651333/100000000000000 : ℝ), (16393893933491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4491548967/10000000000 : ℝ)|^4105 ≤ (6884884293267/20000000000000 : ℝ)^3081
        have hw : |(4491548967/10000000000 : ℝ)|=(4491548967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4330306841/10000000000 : ℝ)|^4105 ≤ (32787790651333/100000000000000 : ℝ)^3081
        have hw : |(4330306841/10000000000 : ℝ)|=(4330306841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(866061313/2000000000 : ℝ)|^4105 ≤ (16393893933491/50000000000000 : ℝ)^3081
        have hw : |(866061313/2000000000 : ℝ)|=(866061313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_4 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2360698047/10000000000 : ℝ)*x 0 + (2639662179/5000000000 : ℝ)*x 1 + (5279324401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2360698047/10000000000 : ℝ)^4105 ≤ (14610477092409/100000000000000 : ℝ)^3081 := by
    have hnat : (2360698047 : ℕ)^4105*100000000000000^3081 ≤ 14610477092409^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360698047 10000000000 14610477092409 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639662179/5000000000 : ℝ)^4105 ≤ (42694761214409/100000000000000 : ℝ)^3081 := by
    have hnat : (2639662179 : ℕ)^4105*100000000000000^3081 ≤ 42694761214409^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639662179 5000000000 42694761214409 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279324401/10000000000 : ℝ)^4105 ≤ (8538952335547/20000000000000 : ℝ)^3081 := by
    have hnat : (5279324401 : ℕ)^4105*20000000000000^3081 ≤ 8538952335547^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279324401 10000000000 8538952335547 20000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2360698047/10000000000 : ℝ), (2639662179/5000000000 : ℝ), (5279324401/10000000000 : ℝ)] ![(14610477092409/100000000000000 : ℝ), (42694761214409/100000000000000 : ℝ), (8538952335547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2360698047/10000000000 : ℝ)|^4105 ≤ (14610477092409/100000000000000 : ℝ)^3081
        have hw : |(-2360698047/10000000000 : ℝ)|=(2360698047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639662179/5000000000 : ℝ)|^4105 ≤ (42694761214409/100000000000000 : ℝ)^3081
        have hw : |(2639662179/5000000000 : ℝ)|=(2639662179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279324401/10000000000 : ℝ)|^4105 ≤ (8538952335547/20000000000000 : ℝ)^3081
        have hw : |(5279324401/10000000000 : ℝ)|=(5279324401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_5 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682272761/5000000000 : ℝ)*x 0 + (-281017721/1250000000 : ℝ)*x 1 + (5279324077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682272761/5000000000 : ℝ)^4105 ≤ (43615474643671/100000000000000 : ℝ)^3081 := by
    have hnat : (2682272761 : ℕ)^4105*100000000000000^3081 ≤ 43615474643671^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682272761 5000000000 43615474643671 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281017721/1250000000 : ℝ)^4105 ≤ (6844883579081/50000000000000 : ℝ)^3081 := by
    have hnat : (281017721 : ℕ)^4105*50000000000000^3081 ≤ 6844883579081^3081*1250000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281017721 1250000000 6844883579081 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279324077/10000000000 : ℝ)^4105 ≤ (42694758186631/100000000000000 : ℝ)^3081 := by
    have hnat : (5279324077 : ℕ)^4105*100000000000000^3081 ≤ 42694758186631^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279324077 10000000000 42694758186631 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682272761/5000000000 : ℝ), (-281017721/1250000000 : ℝ), (5279324077/10000000000 : ℝ)] ![(43615474643671/100000000000000 : ℝ), (6844883579081/50000000000000 : ℝ), (42694758186631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682272761/5000000000 : ℝ)|^4105 ≤ (43615474643671/100000000000000 : ℝ)^3081
        have hw : |(2682272761/5000000000 : ℝ)|=(2682272761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-281017721/1250000000 : ℝ)|^4105 ≤ (6844883579081/50000000000000 : ℝ)^3081
        have hw : |(-281017721/1250000000 : ℝ)|=(281017721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279324077/10000000000 : ℝ)|^4105 ≤ (42694758186631/100000000000000 : ℝ)^3081
        have hw : |(5279324077/10000000000 : ℝ)|=(5279324077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_6 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072908903/2000000000 : ℝ)*x 0 + (329957803/625000000 : ℝ)*x 1 + (-281017761/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072908903/2000000000 : ℝ)^4105 ≤ (43615463735333/100000000000000 : ℝ)^3081 := by
    have hnat : (1072908903 : ℕ)^4105*100000000000000^3081 ≤ 43615463735333^3081*2000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072908903 2000000000 43615463735333 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329957803/625000000 : ℝ)^4105 ≤ (10673691623541/25000000000000 : ℝ)^3081 := by
    have hnat : (329957803 : ℕ)^4105*25000000000000^3081 ≤ 10673691623541^3081*625000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329957803 625000000 10673691623541 25000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281017761/1250000000 : ℝ)^4105 ≤ (3422442438599/25000000000000 : ℝ)^3081 := by
    have hnat : (281017761 : ℕ)^4105*25000000000000^3081 ≤ 3422442438599^3081*1250000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281017761 1250000000 3422442438599 25000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072908903/2000000000 : ℝ), (329957803/625000000 : ℝ), (-281017761/1250000000 : ℝ)] ![(43615463735333/100000000000000 : ℝ), (10673691623541/25000000000000 : ℝ), (3422442438599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072908903/2000000000 : ℝ)|^4105 ≤ (43615463735333/100000000000000 : ℝ)^3081
        have hw : |(1072908903/2000000000 : ℝ)|=(1072908903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329957803/625000000 : ℝ)|^4105 ≤ (10673691623541/25000000000000 : ℝ)^3081
        have hw : |(329957803/625000000 : ℝ)|=(329957803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281017761/1250000000 : ℝ)|^4105 ≤ (3422442438599/25000000000000 : ℝ)^3081
        have hw : |(-281017761/1250000000 : ℝ)|=(281017761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_7 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273319689/10000000000 : ℝ)*x 0 + (177575969/400000000 : ℝ)*x 1 + (4439399689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273319689/10000000000 : ℝ)^4105 ≤ (16107076083149/50000000000000 : ℝ)^3081 := by
    have hnat : (4273319689 : ℕ)^4105*50000000000000^3081 ≤ 16107076083149^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273319689 10000000000 16107076083149 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177575969/400000000 : ℝ)^4105 ≤ (8473230388101/25000000000000 : ℝ)^3081 := by
    have hnat : (177575969 : ℕ)^4105*25000000000000^3081 ≤ 8473230388101^3081*400000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177575969 400000000 8473230388101 25000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4439399689/10000000000 : ℝ)^4105 ≤ (33892926272211/100000000000000 : ℝ)^3081 := by
    have hnat : (4439399689 : ℕ)^4105*100000000000000^3081 ≤ 33892926272211^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439399689 10000000000 33892926272211 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273319689/10000000000 : ℝ), (177575969/400000000 : ℝ), (4439399689/10000000000 : ℝ)] ![(16107076083149/50000000000000 : ℝ), (8473230388101/25000000000000 : ℝ), (33892926272211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273319689/10000000000 : ℝ)|^4105 ≤ (16107076083149/50000000000000 : ℝ)^3081
        have hw : |(4273319689/10000000000 : ℝ)|=(4273319689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177575969/400000000 : ℝ)|^4105 ≤ (8473230388101/25000000000000 : ℝ)^3081
        have hw : |(177575969/400000000 : ℝ)|=(177575969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4439399689/10000000000 : ℝ)|^4105 ≤ (33892926272211/100000000000000 : ℝ)^3081
        have hw : |(4439399689/10000000000 : ℝ)|=(4439399689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_8 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-576425467/2500000000 : ℝ)*x 0 + (162889141/312500000 : ℝ)*x 1 + (5387612039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (576425467/2500000000 : ℝ)^4105 ≤ (2831748260437/20000000000000 : ℝ)^3081 := by
    have hnat : (576425467 : ℕ)^4105*20000000000000^3081 ≤ 2831748260437^3081*2500000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576425467 2500000000 2831748260437 20000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162889141/312500000 : ℝ)^4105 ≤ (41975737378371/100000000000000 : ℝ)^3081 := by
    have hnat : (162889141 : ℕ)^4105*100000000000000^3081 ≤ 41975737378371^3081*312500000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162889141 312500000 41975737378371 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387612039/10000000000 : ℝ)^4105 ≤ (43865521309177/100000000000000 : ℝ)^3081 := by
    have hnat : (5387612039 : ℕ)^4105*100000000000000^3081 ≤ 43865521309177^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387612039 10000000000 43865521309177 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-576425467/2500000000 : ℝ), (162889141/312500000 : ℝ), (5387612039/10000000000 : ℝ)] ![(2831748260437/20000000000000 : ℝ), (41975737378371/100000000000000 : ℝ), (43865521309177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-576425467/2500000000 : ℝ)|^4105 ≤ (2831748260437/20000000000000 : ℝ)^3081
        have hw : |(-576425467/2500000000 : ℝ)|=(576425467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162889141/312500000 : ℝ)|^4105 ≤ (41975737378371/100000000000000 : ℝ)^3081
        have hw : |(162889141/312500000 : ℝ)|=(162889141/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387612039/10000000000 : ℝ)|^4105 ≤ (43865521309177/100000000000000 : ℝ)^3081
        have hw : |(5387612039/10000000000 : ℝ)|=(5387612039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_9 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643908609/5000000000 : ℝ)*x 0 + (-441181437/2000000000 : ℝ)*x 1 + (215504481/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643908609/5000000000 : ℝ)^4105 ≤ (5348287040771/12500000000000 : ℝ)^3081 := by
    have hnat : (2643908609 : ℕ)^4105*12500000000000^3081 ≤ 5348287040771^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643908609 5000000000 5348287040771 12500000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441181437/2000000000 : ℝ)^4105 ≤ (13348182502991/100000000000000 : ℝ)^3081 := by
    have hnat : (441181437 : ℕ)^4105*100000000000000^3081 ≤ 13348182502991^3081*2000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441181437 2000000000 13348182502991 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215504481/400000000 : ℝ)^4105 ≤ (8773104231461/20000000000000 : ℝ)^3081 := by
    have hnat : (215504481 : ℕ)^4105*20000000000000^3081 ≤ 8773104231461^3081*400000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215504481 400000000 8773104231461 20000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643908609/5000000000 : ℝ), (-441181437/2000000000 : ℝ), (215504481/400000000 : ℝ)] ![(5348287040771/12500000000000 : ℝ), (13348182502991/100000000000000 : ℝ), (8773104231461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643908609/5000000000 : ℝ)|^4105 ≤ (5348287040771/12500000000000 : ℝ)^3081
        have hw : |(2643908609/5000000000 : ℝ)|=(2643908609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441181437/2000000000 : ℝ)|^4105 ≤ (13348182502991/100000000000000 : ℝ)^3081
        have hw : |(-441181437/2000000000 : ℝ)|=(441181437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215504481/400000000 : ℝ)|^4105 ≤ (8773104231461/20000000000000 : ℝ)^3081
        have hw : |(215504481/400000000 : ℝ)|=(215504481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_10 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660977173/1250000000 : ℝ)*x 0 + (1077522429/2000000000 : ℝ)*x 1 + (-1102953401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660977173/1250000000 : ℝ)^4105 ≤ (1711451924631/4000000000000 : ℝ)^3081 := by
    have hnat : (660977173 : ℕ)^4105*4000000000000^3081 ≤ 1711451924631^3081*1250000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660977173 1250000000 1711451924631 4000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077522429/2000000000 : ℝ)^4105 ≤ (43865522459061/100000000000000 : ℝ)^3081 := by
    have hnat : (1077522429 : ℕ)^4105*100000000000000^3081 ≤ 43865522459061^3081*2000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077522429 2000000000 43865522459061 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102953401/5000000000 : ℝ)^4105 ≤ (13348179415149/100000000000000 : ℝ)^3081 := by
    have hnat : (1102953401 : ℕ)^4105*100000000000000^3081 ≤ 13348179415149^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102953401 5000000000 13348179415149 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660977173/1250000000 : ℝ), (1077522429/2000000000 : ℝ), (-1102953401/5000000000 : ℝ)] ![(1711451924631/4000000000000 : ℝ), (43865522459061/100000000000000 : ℝ), (13348179415149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660977173/1250000000 : ℝ)|^4105 ≤ (1711451924631/4000000000000 : ℝ)^3081
        have hw : |(660977173/1250000000 : ℝ)|=(660977173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077522429/2000000000 : ℝ)|^4105 ≤ (43865522459061/100000000000000 : ℝ)^3081
        have hw : |(1077522429/2000000000 : ℝ)|=(1077522429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102953401/5000000000 : ℝ)|^4105 ≤ (13348179415149/100000000000000 : ℝ)^3081
        have hw : |(-1102953401/5000000000 : ℝ)|=(1102953401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_11 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4512487149/10000000000 : ℝ)*x 0 + (53996217/125000000 : ℝ)*x 1 + (86393937/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4512487149/10000000000 : ℝ)^4105 ≤ (6927679674621/20000000000000 : ℝ)^3081 := by
    have hnat : (4512487149 : ℕ)^4105*20000000000000^3081 ≤ 6927679674621^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512487149 10000000000 6927679674621 20000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53996217/125000000 : ℝ)^4105 ≤ (32680803375449/100000000000000 : ℝ)^3081 := by
    have hnat : (53996217 : ℕ)^4105*100000000000000^3081 ≤ 32680803375449^3081*125000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53996217 125000000 32680803375449 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86393937/200000000 : ℝ)^4105 ≤ (16340399117323/50000000000000 : ℝ)^3081 := by
    have hnat : (86393937 : ℕ)^4105*50000000000000^3081 ≤ 16340399117323^3081*200000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86393937 200000000 16340399117323 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4512487149/10000000000 : ℝ), (53996217/125000000 : ℝ), (86393937/200000000 : ℝ)] ![(6927679674621/20000000000000 : ℝ), (32680803375449/100000000000000 : ℝ), (16340399117323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4512487149/10000000000 : ℝ)|^4105 ≤ (6927679674621/20000000000000 : ℝ)^3081
        have hw : |(4512487149/10000000000 : ℝ)|=(4512487149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53996217/125000000 : ℝ)|^4105 ≤ (32680803375449/100000000000000 : ℝ)^3081
        have hw : |(53996217/125000000 : ℝ)|=(53996217/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86393937/200000000 : ℝ)|^4105 ≤ (16340399117323/50000000000000 : ℝ)^3081
        have hw : |(86393937/200000000 : ℝ)|=(86393937/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_12 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430469259/2000000000 : ℝ)*x 0 + (5443516593/10000000000 : ℝ)*x 1 + (5271351157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430469259/2000000000 : ℝ)^4105 ≤ (12918113007317/100000000000000 : ℝ)^3081 := by
    have hnat : (430469259 : ℕ)^4105*100000000000000^3081 ≤ 12918113007317^3081*2000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430469259 2000000000 12918113007317 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443516593/10000000000 : ℝ)^4105 ≤ (1111825388177/2500000000000 : ℝ)^3081 := by
    have hnat : (5443516593 : ℕ)^4105*2500000000000^3081 ≤ 1111825388177^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443516593 10000000000 1111825388177 2500000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271351157/10000000000 : ℝ)^4105 ≤ (665763616531/1562500000000 : ℝ)^3081 := by
    have hnat : (5271351157 : ℕ)^4105*1562500000000^3081 ≤ 665763616531^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271351157 10000000000 665763616531 1562500000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430469259/2000000000 : ℝ), (5443516593/10000000000 : ℝ), (5271351157/10000000000 : ℝ)] ![(12918113007317/100000000000000 : ℝ), (1111825388177/2500000000000 : ℝ), (665763616531/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430469259/2000000000 : ℝ)|^4105 ≤ (12918113007317/100000000000000 : ℝ)^3081
        have hw : |(-430469259/2000000000 : ℝ)|=(430469259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443516593/10000000000 : ℝ)|^4105 ≤ (1111825388177/2500000000000 : ℝ)^3081
        have hw : |(5443516593/10000000000 : ℝ)|=(5443516593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271351157/10000000000 : ℝ)|^4105 ≤ (665763616531/1562500000000 : ℝ)^3081
        have hw : |(5271351157/10000000000 : ℝ)|=(5271351157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_13 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685095963/5000000000 : ℝ)*x 0 + (-1125593369/5000000000 : ℝ)*x 1 + (1317837817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685095963/5000000000 : ℝ)^4105 ≤ (43676650071941/100000000000000 : ℝ)^3081 := by
    have hnat : (2685095963 : ℕ)^4105*100000000000000^3081 ≤ 43676650071941^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685095963 5000000000 43676650071941 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125593369/5000000000 : ℝ)^4105 ≤ (13714477261359/100000000000000 : ℝ)^3081 := by
    have hnat : (1125593369 : ℕ)^4105*100000000000000^3081 ≤ 13714477261359^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125593369 5000000000 13714477261359 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317837817/2500000000 : ℝ)^4105 ≤ (42608872653409/100000000000000 : ℝ)^3081 := by
    have hnat : (1317837817 : ℕ)^4105*100000000000000^3081 ≤ 42608872653409^3081*2500000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317837817 2500000000 42608872653409 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685095963/5000000000 : ℝ), (-1125593369/5000000000 : ℝ), (1317837817/2500000000 : ℝ)] ![(43676650071941/100000000000000 : ℝ), (13714477261359/100000000000000 : ℝ), (42608872653409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685095963/5000000000 : ℝ)|^4105 ≤ (43676650071941/100000000000000 : ℝ)^3081
        have hw : |(2685095963/5000000000 : ℝ)|=(2685095963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1125593369/5000000000 : ℝ)|^4105 ≤ (13714477261359/100000000000000 : ℝ)^3081
        have hw : |(-1125593369/5000000000 : ℝ)|=(1125593369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317837817/2500000000 : ℝ)|^4105 ≤ (42608872653409/100000000000000 : ℝ)^3081
        have hw : |(1317837817/2500000000 : ℝ)|=(1317837817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_14 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370191241/10000000000 : ℝ)*x 0 + (2635675823/5000000000 : ℝ)*x 1 + (-45023743/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370191241/10000000000 : ℝ)^4105 ≤ (10919160662269/25000000000000 : ℝ)^3081 := by
    have hnat : (5370191241 : ℕ)^4105*25000000000000^3081 ≤ 10919160662269^3081*10000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370191241 10000000000 10919160662269 25000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635675823/5000000000 : ℝ)^4105 ≤ (21304438362159/50000000000000 : ℝ)^3081 := by
    have hnat : (2635675823 : ℕ)^4105*50000000000000^3081 ≤ 21304438362159^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635675823 5000000000 21304438362159 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45023743/200000000 : ℝ)^4105 ≤ (6857240302757/50000000000000 : ℝ)^3081 := by
    have hnat : (45023743 : ℕ)^4105*50000000000000^3081 ≤ 6857240302757^3081*200000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45023743 200000000 6857240302757 50000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370191241/10000000000 : ℝ), (2635675823/5000000000 : ℝ), (-45023743/200000000 : ℝ)] ![(10919160662269/25000000000000 : ℝ), (21304438362159/50000000000000 : ℝ), (6857240302757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370191241/10000000000 : ℝ)|^4105 ≤ (10919160662269/25000000000000 : ℝ)^3081
        have hw : |(5370191241/10000000000 : ℝ)|=(5370191241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635675823/5000000000 : ℝ)|^4105 ≤ (21304438362159/50000000000000 : ℝ)^3081
        have hw : |(2635675823/5000000000 : ℝ)|=(2635675823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45023743/200000000 : ℝ)|^4105 ≤ (6857240302757/50000000000000 : ℝ)^3081
        have hw : |(-45023743/200000000 : ℝ)|=(45023743/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1017_box_15 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127730123/5000000000 : ℝ)*x 0 + (556025969/1250000000 : ℝ)*x 1 + (139006489/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127730123/5000000000 : ℝ)^4105 ≤ (8008724559111/25000000000000 : ℝ)^3081 := by
    have hnat : (2127730123 : ℕ)^4105*25000000000000^3081 ≤ 8008724559111^3081*5000000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127730123 5000000000 8008724559111 25000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556025969/1250000000 : ℝ)^4105 ≤ (33982551402553/100000000000000 : ℝ)^3081 := by
    have hnat : (556025969 : ℕ)^4105*100000000000000^3081 ≤ 33982551402553^3081*1250000000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556025969 1250000000 33982551402553 100000000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139006489/312500000 : ℝ)^4105 ≤ (1061954698249/3125000000000 : ℝ)^3081 := by
    have hnat : (139006489 : ℕ)^4105*3125000000000^3081 ≤ 1061954698249^3081*312500000^4105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139006489 312500000 1061954698249 3125000000000 4105 3081 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4105/1024 : ℝ)) 4105 3081 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127730123/5000000000 : ℝ), (556025969/1250000000 : ℝ), (139006489/312500000 : ℝ)] ![(8008724559111/25000000000000 : ℝ), (33982551402553/100000000000000 : ℝ), (1061954698249/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127730123/5000000000 : ℝ)|^4105 ≤ (8008724559111/25000000000000 : ℝ)^3081
        have hw : |(2127730123/5000000000 : ℝ)|=(2127730123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(556025969/1250000000 : ℝ)|^4105 ≤ (33982551402553/100000000000000 : ℝ)^3081
        have hw : |(556025969/1250000000 : ℝ)|=(556025969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139006489/312500000 : ℝ)|^4105 ≤ (1061954698249/3125000000000 : ℝ)^3081
        have hw : |(139006489/312500000 : ℝ)|=(139006489/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1017_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147040751/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11841/20000 : ℝ) ∧ (79417/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2071/2500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11183/100000 : ℝ) ^ (8209/2048 : ℝ) ≤ (1919754098251163/12500000000000000000 : ℝ) := by
    have hpowers : (11183/100000 : ℝ)^8209 ≤ (1919754098251163/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11183 : ℕ)^8209*12500000000000000000^2048 ≤ 1919754098251163^2048*100000^8209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11183 100000 1919754098251163 12500000000000000000 8209 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11183/100000 : ℝ)) (X := (1919754098251163/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8209 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13971/100000 : ℝ) ^ (8209/2048 : ℝ) ≤ (18740651962425973/50000000000000000000 : ℝ) := by
    have hpowers : (13971/100000 : ℝ)^8209 ≤ (18740651962425973/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13971 : ℕ)^8209*50000000000000000000^2048 ≤ 18740651962425973^2048*100000^8209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13971 100000 18740651962425973 50000000000000000000 8209 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13971/100000 : ℝ)) (X := (18740651962425973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8209 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251919754098251163/6250000000000000000 : ℝ) ≤ (500038311154031/500000000000000 : ℝ) ^ (8209/2048 : ℝ) := by
    have hpowers : (6251919754098251163/6250000000000000000 : ℝ)^2048 ≤ (500038311154031/500000000000000 : ℝ)^8209 := by
      have hnat : (6251919754098251163 : ℕ)^2048*500000000000000^8209 ≤ 500038311154031^8209*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251919754098251163 6250000000000000000 500038311154031 500000000000000 2048 8209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500038311154031/500000000000000 : ℝ)) (X := (6251919754098251163/6250000000000000000 : ℝ)) (by norm_num) 8209 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (80042271469368689/80000000000000000 : ℝ) ≤ (5000658993244427/5000000000000000 : ℝ) ^ (8209/2048 : ℝ) := by
    have hpowers : (80042271469368689/80000000000000000 : ℝ)^2048 ≤ (5000658993244427/5000000000000000 : ℝ)^8209 := by
      have hnat : (80042271469368689 : ℕ)^2048*5000000000000000^8209 ≤ 5000658993244427^8209*80000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80042271469368689 80000000000000000 5000658993244427 5000000000000000 2048 8209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000658993244427/5000000000000000 : ℝ)) (X := (80042271469368689/80000000000000000 : ℝ)) (by norm_num) 8209 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018740651962425973/25000000000000000000 : ℝ) ≤ (78139607421071/78125000000000 : ℝ) ^ (8209/2048 : ℝ) := by
    have hpowers : (25018740651962425973/25000000000000000000 : ℝ)^2048 ≤ (78139607421071/78125000000000 : ℝ)^8209 := by
      have hnat : (25018740651962425973 : ℕ)^2048*78125000000000^8209 ≤ 78139607421071^8209*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018740651962425973 25000000000000000000 78139607421071 78125000000000 2048 8209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78139607421071/78125000000000 : ℝ)) (X := (25018740651962425973/25000000000000000000 : ℝ)) (by norm_num) 8209 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1919754098251163/12500000000000000000 : ℝ) ≤ ((6967448872390051729/6970000000000000000 : ℝ)+2*(275881704117/139400000000000 : ℝ)*(11183/100000 : ℝ))^(8209/2048 : ℝ) := by
    rw [show (6967448872390051729/6970000000000000000 : ℝ)+2*(275881704117/139400000000000 : ℝ)*(11183/100000 : ℝ)=(500038311154031/500000000000000 : ℝ) by norm_num, show 1+2*(1919754098251163/12500000000000000000 : ℝ)=(6251919754098251163/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18740651962425973/50000000000000000000 : ℝ)+(1919754098251163/12500000000000000000 : ℝ) ≤ ((6967448872390051729/6970000000000000000 : ℝ)+(275881704117/139400000000000 : ℝ)*((13971/100000 : ℝ)+(11183/100000 : ℝ)))^(8209/2048 : ℝ) := by
    rw [show (6967448872390051729/6970000000000000000 : ℝ)+(275881704117/139400000000000 : ℝ)*((13971/100000 : ℝ)+(11183/100000 : ℝ))=(5000658993244427/5000000000000000 : ℝ) by norm_num, show 1+(18740651962425973/50000000000000000000 : ℝ)+(1919754098251163/12500000000000000000 : ℝ)=(80042271469368689/80000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18740651962425973/50000000000000000000 : ℝ) ≤ ((6967448872390051729/6970000000000000000 : ℝ)+2*(275881704117/139400000000000 : ℝ)*(13971/100000 : ℝ))^(8209/2048 : ℝ) := by
    rw [show (6967448872390051729/6970000000000000000 : ℝ)+2*(275881704117/139400000000000 : ℝ)*(13971/100000 : ℝ)=(78139607421071/78125000000000 : ℝ) by norm_num, show 1+2*(18740651962425973/50000000000000000000 : ℝ)=(25018740651962425973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6967448872390051729/6970000000000000000 : ℝ)*(X 1 0+X 2 0)+(275881704117/139400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8209/2048 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (13971/100000 : ℝ)) (c := (6967448872390051729/6970000000000000000 : ℝ)) (alpha := (275881704117/139400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6967448872390051729/6970000000000000000 : ℝ)*(X 0 1+X 2 1)+(275881704117/139400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8209/2048 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (13971/100000 : ℝ)) (c := (6967448872390051729/6970000000000000000 : ℝ)) (alpha := (275881704117/139400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6967448872390051729/6970000000000000000 : ℝ)*(X 0 2+X 1 2)+(275881704117/139400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8209/2048 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (13971/100000 : ℝ)) (c := (6967448872390051729/6970000000000000000 : ℝ)) (alpha := (275881704117/139400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2096948141/10000000000 : ℝ)*X 0 0+(2689009759/5000000000 : ℝ)*X 0 1+(67225239/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((529461793/1000000000 : ℝ)*X 1 0+(-17677709/80000000 : ℝ)*X 1 1+(5378019387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647309013/5000000000 : ℝ)*X 2 0+(2689009627/5000000000 : ℝ)*X 2 1+(-88388547/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4491548967/10000000000 : ℝ)*X 0 0+(4330306841/10000000000 : ℝ)*X 0 1+(866061313/2000000000 : ℝ)*X 0 2+(4491548967/10000000000 : ℝ)*X 1 0+(4330306841/10000000000 : ℝ)*X 1 1+(866061313/2000000000 : ℝ)*X 1 2+(4491548967/10000000000 : ℝ)*X 2 0+(4330306841/10000000000 : ℝ)*X 2 1+(866061313/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2360698047/10000000000 : ℝ)*X 0 0+(2639662179/5000000000 : ℝ)*X 0 1+(5279324401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682272761/5000000000 : ℝ)*X 1 0+(-281017721/1250000000 : ℝ)*X 1 1+(5279324077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072908903/2000000000 : ℝ)*X 2 0+(329957803/625000000 : ℝ)*X 2 1+(-281017761/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4273319689/10000000000 : ℝ)*X 0 0+(177575969/400000000 : ℝ)*X 0 1+(4439399689/10000000000 : ℝ)*X 0 2+(4273319689/10000000000 : ℝ)*X 1 0+(177575969/400000000 : ℝ)*X 1 1+(4439399689/10000000000 : ℝ)*X 1 2+(4273319689/10000000000 : ℝ)*X 2 0+(177575969/400000000 : ℝ)*X 2 1+(4439399689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-576425467/2500000000 : ℝ)*X 0 0+(162889141/312500000 : ℝ)*X 0 1+(5387612039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2643908609/5000000000 : ℝ)*X 1 0+(-441181437/2000000000 : ℝ)*X 1 1+(215504481/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((660977173/1250000000 : ℝ)*X 2 0+(1077522429/2000000000 : ℝ)*X 2 1+(-1102953401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4512487149/10000000000 : ℝ)*X 0 0+(53996217/125000000 : ℝ)*X 0 1+(86393937/200000000 : ℝ)*X 0 2+(4512487149/10000000000 : ℝ)*X 1 0+(53996217/125000000 : ℝ)*X 1 1+(86393937/200000000 : ℝ)*X 1 2+(4512487149/10000000000 : ℝ)*X 2 0+(53996217/125000000 : ℝ)*X 2 1+(86393937/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-430469259/2000000000 : ℝ)*X 0 0+(5443516593/10000000000 : ℝ)*X 0 1+(5271351157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2685095963/5000000000 : ℝ)*X 1 0+(-1125593369/5000000000 : ℝ)*X 1 1+(1317837817/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370191241/10000000000 : ℝ)*X 2 0+(2635675823/5000000000 : ℝ)*X 2 1+(-45023743/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2127730123/5000000000 : ℝ)*X 0 0+(556025969/1250000000 : ℝ)*X 0 1+(139006489/312500000 : ℝ)*X 0 2+(2127730123/5000000000 : ℝ)*X 1 0+(556025969/1250000000 : ℝ)*X 1 1+(139006489/312500000 : ℝ)*X 1 2+(2127730123/5000000000 : ℝ)*X 2 0+(556025969/1250000000 : ℝ)*X 2 1+(139006489/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1017_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-54209517790516347193207193493339/87125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223487003/100000000000000 : ℝ)*(upper1) + (178663119/100000000000000 : ℝ)*(upper2) + (323604529/100000000000000 : ℝ)*(lower4) + (4458931/2500000000000 : ℝ)*(upper5) + (953745343885101/25000000000000 : ℝ)*(major0) + (953745343885101/25000000000000 : ℝ)*(major1) + (953745343885101/25000000000000 : ℝ)*(major2) + (311197237/2500000000000 : ℝ)*(sp3) + (632024587461883/12500000000000 : ℝ)*(sp4) + (2528060931272669/50000000000000 : ℝ)*(sp5) + (2528054831322469/50000000000000 : ℝ)*(sp6) + (1297246867322593/50000000000000 : ℝ)*(sp7) + (37418574863/50000000000000 : ℝ)*(sp13) + (43518525063/50000000000000 : ℝ)*(sp14) + (1297253091267333/50000000000000 : ℝ)*(f.failure) + (632024587461883/12500000000000 : ℝ)*(f.sum) + (1191102958153/435625000000000000000000000 : ℝ)*base65 + (1673321202255260371/174250000000000000000000000000000 : ℝ)*base68 + (2313926509873260371/174250000000000000000000000000000 : ℝ)*base70 + (1564753099017260371/174250000000000000000000000000000 : ℝ)*base72 + (5270741325251/871250000000000000000000000 : ℝ)*base73 + (2040179573425760371/174250000000000000000000000000000 : ℝ)*base76 + (825126796174260371/174250000000000000000000000000000 : ℝ)*base78 + (1797362442724260371/174250000000000000000000000000000 : ℝ)*base80 + (717719728821/871250000000000000000000000 : ℝ)*base81 + (13912917/5000000000000000000000 : ℝ)*base90 + (13912917/5000000000000000000000 : ℝ)*base92 + (13912917/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11841/20000 : ℝ) ≤ (412674137431955551392191553/697000000000000000000000000 : ℝ) := by norm_num
    linear_combination (337727/1250000000000 : ℝ)*(upper3) + (12247419/25000000000000 : ℝ)*(upper4) + (7127367/10000000000000 : ℝ)*(lower5) + (387710293308783/10000000000000 : ℝ)*(major0) + (387710293308783/10000000000000 : ℝ)*(major1) + (387710293308783/10000000000000 : ℝ)*(major2) + (5097706254976627/100000000000000 : ℝ)*(sp0) + (5097706005180303/100000000000000 : ℝ)*(sp1) + (5097705997641793/100000000000000 : ℝ)*(sp2) + (26367485811281/1000000000000 : ℝ)*(sp3) + (1262031069/12500000000000 : ℝ)*(sp5) + (10103787061/100000000000000 : ℝ)*(sp6) + (340782027/6250000000000 : ℝ)*(sp7) + (9846452227/100000000000000 : ℝ)*(sp8) + (2636754033640531/100000000000000 : ℝ)*(f.failure) + (1019543220285771/20000000000000 : ℝ)*(f.sum) + (3408943708087/348500000000000000000000000 : ℝ)*base66 + (272280495586414193/69700000000000000000000000000000 : ℝ)*base68 + (636570428822885807/69700000000000000000000000000000 : ℝ)*base69 + (909395368834814193/69700000000000000000000000000000 : ℝ)*base72 + (1105276142861/348500000000000000000000000 : ℝ)*base74 + (278880367284485807/69700000000000000000000000000000 : ℝ)*base75 + (84034263464885807/69700000000000000000000000000000 : ℝ)*base77 + (400063188144414193/69700000000000000000000000000000 : ℝ)*base80 + (1031505145687/348500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (57721219/10000000000000000000000 : ℝ)*base90 + (57721219/10000000000000000000000 : ℝ)*base92 + (57721219/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79417/100000 : ℝ) ≤ (691938576982384005938931789399/871250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1053491/20000000000000 : ℝ)*(lower3) + (274796983/100000000000000 : ℝ)*(upper4) + (1523879/4000000000000 : ℝ)*(lower5) + (10863503815391/250000000000 : ℝ)*(major0) + (10863503815391/250000000000 : ℝ)*(major1) + (10863503815391/250000000000 : ℝ)*(major2) + (3689640199/100000000000000 : ℝ)*(sp0) + (848738851/100000000000000 : ℝ)*(sp1) + (265567911029/100000000000000 : ℝ)*(sp2) + (38427168229/20000000000000 : ℝ)*(sp3) + (2854545062905349/50000000000000 : ℝ)*(sp8) + (2854546483356023/50000000000000 : ℝ)*(sp9) + (5708828247539869/100000000000000 : ℝ)*(sp10) + (2955044080380573/100000000000000 : ℝ)*(sp11) + (2955236216221719/100000000000000 : ℝ)*(f.failure) + (2854546907725449/50000000000000 : ℝ)*(f.sum) + (143359920587/697000000000000000000000000 : ℝ)*base65 + (8081450431083539/1742500000000000000000000000000 : ℝ)*base67 + (41786850284538539/1742500000000000000000000000000 : ℝ)*base69 + (35206996081586039/1742500000000000000000000000000 : ℝ)*base71 + (16542918259/1742500000000000000000000 : ℝ)*base74 + (21577928806176039/1742500000000000000000000000000 : ℝ)*base75 + (18200396483026039/1742500000000000000000000000000 : ℝ)*base77 + (8654586712681039/1742500000000000000000000000000 : ℝ)*base79 + (2973185785433/348500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (55729031/10000000000000000000000 : ℝ)*base90 + (55729031/10000000000000000000000 : ℝ)*base92 + (55729031/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-2071/2500 : ℝ) ≤ (-7217199002448579253812858683421/8712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1864701/25000000000000 : ℝ)*(lower0) + (68541083/100000000000000 : ℝ)*(upper1) + (234608197/100000000000000 : ℝ)*(upper3) + (323076429/100000000000000 : ℝ)*(lower4) + (109491311947739/2500000000000 : ℝ)*(major0) + (109491311947739/2500000000000 : ℝ)*(major1) + (109491311947739/2500000000000 : ℝ)*(major2) + (504448159/10000000000000 : ℝ)*(sp4) + (66235187143/50000000000000 : ℝ)*(sp5) + (38828289591/20000000000000 : ℝ)*(sp7) + (726047826966891/12500000000000 : ℝ)*(sp12) + (5808255189842433/100000000000000 : ℝ)*(sp13) + (5808387660216719/100000000000000 : ℝ)*(sp14) + (93072987018121/3125000000000 : ℝ)*(sp15) + (744632431506957/25000000000000 : ℝ)*(f.failure) + (5808387660216719/100000000000000 : ℝ)*(f.sum) + (1712902601003/697000000000000000000000000 : ℝ)*base65 + (206445010169034269/17425000000000000000000000000000 : ℝ)*base68 + (59291181289484269/17425000000000000000000000000000 : ℝ)*base70 + (191908151887984269/17425000000000000000000000000000 : ℝ)*base72 + (924491311797/697000000000000000000000000 : ℝ)*base74 + (152090081560984269/17425000000000000000000000000000 : ℝ)*base76 + (87384551268309269/17425000000000000000000000000000 : ℝ)*base78 + (322962872192784269/17425000000000000000000000000000 : ℝ)*base80 + (1315517636751/139400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (19004707/2500000000000000000000 : ℝ)*base89 + (19004707/2500000000000000000000 : ℝ)*base91 + (19004707/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1017_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147040751/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11841/20000 : ℝ) else (79417/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2071/2500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1017_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147040751/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11841/20000 : ℝ) else (79417/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2071/2500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1017_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
