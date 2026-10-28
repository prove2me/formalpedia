-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1003_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:50:25.084526+00:00
-- url     : https://prove2.me/submissions/72dca02d-0dac-4b74-b3bd-8b24bc276ae9

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
theorem support_rectangle_w1003_box_0 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103491277/10000000000 : ℝ)*x 0 + (5378201573/10000000000 : ℝ)*x 1 + (1344550403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103491277/10000000000 : ℝ)^2049 ≤ (500565730897/4000000000000 : ℝ)^1537 := by
    have hnat : (2103491277 : ℕ)^2049*4000000000000^1537 ≤ 500565730897^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103491277 10000000000 500565730897 4000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5378201573/10000000000 : ℝ)^2049 ≤ (43742928148337/100000000000000 : ℝ)^1537 := by
    have hnat : (5378201573 : ℕ)^2049*100000000000000^1537 ≤ 43742928148337^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378201573 10000000000 43742928148337 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344550403/2500000000 : ℝ)^2049 ≤ (43742928571203/100000000000000 : ℝ)^1537 := by
    have hnat : (1344550403 : ℕ)^2049*100000000000000^1537 ≤ 43742928571203^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344550403 2500000000 43742928571203 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103491277/10000000000 : ℝ), (5378201573/10000000000 : ℝ), (1344550403/2500000000 : ℝ)] ![(500565730897/4000000000000 : ℝ), (43742928148337/100000000000000 : ℝ), (43742928571203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103491277/10000000000 : ℝ)|^2049 ≤ (500565730897/4000000000000 : ℝ)^1537
        have hw : |(-2103491277/10000000000 : ℝ)|=(2103491277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5378201573/10000000000 : ℝ)|^2049 ≤ (43742928148337/100000000000000 : ℝ)^1537
        have hw : |(5378201573/10000000000 : ℝ)|=(5378201573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344550403/2500000000 : ℝ)|^2049 ≤ (43742928571203/100000000000000 : ℝ)^1537
        have hw : |(1344550403/2500000000 : ℝ)|=(1344550403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_1 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5294439043/10000000000 : ℝ)*x 0 + (-2216704553/10000000000 : ℝ)*x 1 + (2689100817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294439043/10000000000 : ℝ)^2049 ≤ (1338658667237/3125000000000 : ℝ)^1537 := by
    have hnat : (5294439043 : ℕ)^2049*3125000000000^1537 ≤ 1338658667237^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294439043 10000000000 1338658667237 3125000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216704553/10000000000 : ℝ)^2049 ≤ (13419993820129/100000000000000 : ℝ)^1537 := by
    have hnat : (2216704553 : ℕ)^2049*100000000000000^1537 ≤ 13419993820129^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216704553 10000000000 13419993820129 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2689100817/5000000000 : ℝ)^2049 ≤ (2733933050609/6250000000000 : ℝ)^1537 := by
    have hnat : (2689100817 : ℕ)^2049*6250000000000^1537 ≤ 2733933050609^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689100817 5000000000 2733933050609 6250000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294439043/10000000000 : ℝ), (-2216704553/10000000000 : ℝ), (2689100817/5000000000 : ℝ)] ![(1338658667237/3125000000000 : ℝ), (13419993820129/100000000000000 : ℝ), (2733933050609/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294439043/10000000000 : ℝ)|^2049 ≤ (1338658667237/3125000000000 : ℝ)^1537
        have hw : |(5294439043/10000000000 : ℝ)|=(5294439043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216704553/10000000000 : ℝ)|^2049 ≤ (13419993820129/100000000000000 : ℝ)^1537
        have hw : |(-2216704553/10000000000 : ℝ)|=(2216704553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2689100817/5000000000 : ℝ)|^2049 ≤ (2733933050609/6250000000000 : ℝ)^1537
        have hw : |(2689100817/5000000000 : ℝ)|=(2689100817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_2 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1058887809/2000000000 : ℝ)*x 0 + (5378201563/10000000000 : ℝ)*x 1 + (-1108352323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058887809/2000000000 : ℝ)^2049 ≤ (10709269343289/25000000000000 : ℝ)^1537 := by
    have hnat : (1058887809 : ℕ)^2049*25000000000000^1537 ≤ 10709269343289^1537*2000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058887809 2000000000 10709269343289 25000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5378201563/10000000000 : ℝ)^2049 ≤ (43742928039909/100000000000000 : ℝ)^1537 := by
    have hnat : (5378201563 : ℕ)^2049*100000000000000^1537 ≤ 43742928039909^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378201563 10000000000 43742928039909 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108352323/5000000000 : ℝ)^2049 ≤ (13419994570707/100000000000000 : ℝ)^1537 := by
    have hnat : (1108352323 : ℕ)^2049*100000000000000^1537 ≤ 13419994570707^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108352323 5000000000 13419994570707 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058887809/2000000000 : ℝ), (5378201563/10000000000 : ℝ), (-1108352323/5000000000 : ℝ)] ![(10709269343289/25000000000000 : ℝ), (43742928039909/100000000000000 : ℝ), (13419994570707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058887809/2000000000 : ℝ)|^2049 ≤ (10709269343289/25000000000000 : ℝ)^1537
        have hw : |(1058887809/2000000000 : ℝ)|=(1058887809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5378201563/10000000000 : ℝ)|^2049 ≤ (43742928039909/100000000000000 : ℝ)^1537
        have hw : |(5378201563/10000000000 : ℝ)|=(5378201563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108352323/5000000000 : ℝ)|^2049 ≤ (13419994570707/100000000000000 : ℝ)^1537
        have hw : |(-1108352323/5000000000 : ℝ)|=(1108352323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_3 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4493762307/10000000000 : ℝ)*x 0 + (4332277717/10000000000 : ℝ)*x 1 + (433227773/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493762307/10000000000 : ℝ)^2049 ≤ (34426177388191/100000000000000 : ℝ)^1537 := by
    have hnat : (4493762307 : ℕ)^2049*100000000000000^1537 ≤ 34426177388191^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493762307 10000000000 34426177388191 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4332277717/10000000000 : ℝ)^2049 ≤ (8196727808407/25000000000000 : ℝ)^1537 := by
    have hnat : (4332277717 : ℕ)^2049*25000000000000^1537 ≤ 8196727808407^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332277717 10000000000 8196727808407 25000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433227773/1000000000 : ℝ)^2049 ≤ (16393455682393/50000000000000 : ℝ)^1537 := by
    have hnat : (433227773 : ℕ)^2049*50000000000000^1537 ≤ 16393455682393^1537*1000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433227773 1000000000 16393455682393 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493762307/10000000000 : ℝ), (4332277717/10000000000 : ℝ), (433227773/1000000000 : ℝ)] ![(34426177388191/100000000000000 : ℝ), (8196727808407/25000000000000 : ℝ), (16393455682393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493762307/10000000000 : ℝ)|^2049 ≤ (34426177388191/100000000000000 : ℝ)^1537
        have hw : |(4493762307/10000000000 : ℝ)|=(4493762307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4332277717/10000000000 : ℝ)|^2049 ≤ (8196727808407/25000000000000 : ℝ)^1537
        have hw : |(4332277717/10000000000 : ℝ)|=(4332277717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433227773/1000000000 : ℝ)|^2049 ≤ (16393455682393/50000000000000 : ℝ)^1537
        have hw : |(433227773/1000000000 : ℝ)|=(433227773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_4 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-148015213/625000000 : ℝ)*x 0 + (659886587/1250000000 : ℝ)*x 1 + (2639546357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (148015213/625000000 : ℝ)^2049 ≤ (732837116139/5000000000000 : ℝ)^1537 := by
    have hnat : (148015213 : ℕ)^2049*5000000000000^1537 ≤ 732837116139^1537*625000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148015213 625000000 732837116139 5000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659886587/1250000000 : ℝ)^2049 ≤ (42671628739109/100000000000000 : ℝ)^1537 := by
    have hnat : (659886587 : ℕ)^2049*100000000000000^1537 ≤ 42671628739109^1537*1250000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659886587 1250000000 42671628739109 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639546357/5000000000 : ℝ)^2049 ≤ (42671628933073/100000000000000 : ℝ)^1537 := by
    have hnat : (2639546357 : ℕ)^2049*100000000000000^1537 ≤ 42671628933073^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639546357 5000000000 42671628933073 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-148015213/625000000 : ℝ), (659886587/1250000000 : ℝ), (2639546357/5000000000 : ℝ)] ![(732837116139/5000000000000 : ℝ), (42671628739109/100000000000000 : ℝ), (42671628933073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-148015213/625000000 : ℝ)|^2049 ≤ (732837116139/5000000000000 : ℝ)^1537
        have hw : |(-148015213/625000000 : ℝ)|=(148015213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659886587/1250000000 : ℝ)|^2049 ≤ (42671628739109/100000000000000 : ℝ)^1537
        have hw : |(659886587/1250000000 : ℝ)|=(659886587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2639546357/5000000000 : ℝ)|^2049 ≤ (42671628933073/100000000000000 : ℝ)^1537
        have hw : |(2639546357/5000000000 : ℝ)|=(2639546357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_5 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (134117063/250000000 : ℝ)*x 0 + (-281905979/1250000000 : ℝ)*x 1 + (5279092857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134117063/250000000 : ℝ)^2049 ≤ (8719281207261/20000000000000 : ℝ)^1537 := by
    have hnat : (134117063 : ℕ)^2049*20000000000000^1537 ≤ 8719281207261^1537*250000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134117063 250000000 8719281207261 20000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281905979/1250000000 : ℝ)^2049 ≤ (13731963482523/100000000000000 : ℝ)^1537 := by
    have hnat : (281905979 : ℕ)^2049*100000000000000^1537 ≤ 13731963482523^1537*1250000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281905979 1250000000 13731963482523 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279092857/10000000000 : ℝ)^2049 ≤ (42671630474007/100000000000000 : ℝ)^1537 := by
    have hnat : (5279092857 : ℕ)^2049*100000000000000^1537 ≤ 42671630474007^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279092857 10000000000 42671630474007 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134117063/250000000 : ℝ), (-281905979/1250000000 : ℝ), (5279092857/10000000000 : ℝ)] ![(8719281207261/20000000000000 : ℝ), (13731963482523/100000000000000 : ℝ), (42671630474007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134117063/250000000 : ℝ)|^2049 ≤ (8719281207261/20000000000000 : ℝ)^1537
        have hw : |(134117063/250000000 : ℝ)|=(134117063/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-281905979/1250000000 : ℝ)|^2049 ≤ (13731963482523/100000000000000 : ℝ)^1537
        have hw : |(-281905979/1250000000 : ℝ)|=(281905979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279092857/10000000000 : ℝ)|^2049 ≤ (42671630474007/100000000000000 : ℝ)^1537
        have hw : |(5279092857/10000000000 : ℝ)|=(5279092857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_6 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1341170689/2500000000 : ℝ)*x 0 + (527909243/1000000000 : ℝ)*x 1 + (-2255248083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341170689/2500000000 : ℝ)^2049 ≤ (21798204296523/50000000000000 : ℝ)^1537 := by
    have hnat : (1341170689 : ℕ)^2049*50000000000000^1537 ≤ 21798204296523^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341170689 2500000000 21798204296523 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527909243/1000000000 : ℝ)^2049 ≤ (10667906468189/25000000000000 : ℝ)^1537 := by
    have hnat : (527909243 : ℕ)^2049*25000000000000^1537 ≤ 10667906468189^1537*1000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527909243 1000000000 10667906468189 25000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255248083/10000000000 : ℝ)^2049 ≤ (13731965519941/100000000000000 : ℝ)^1537 := by
    have hnat : (2255248083 : ℕ)^2049*100000000000000^1537 ≤ 13731965519941^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255248083 10000000000 13731965519941 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341170689/2500000000 : ℝ), (527909243/1000000000 : ℝ), (-2255248083/10000000000 : ℝ)] ![(21798204296523/50000000000000 : ℝ), (10667906468189/25000000000000 : ℝ), (13731965519941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341170689/2500000000 : ℝ)|^2049 ≤ (21798204296523/50000000000000 : ℝ)^1537
        have hw : |(1341170689/2500000000 : ℝ)|=(1341170689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527909243/1000000000 : ℝ)|^2049 ≤ (10667906468189/25000000000000 : ℝ)^1537
        have hw : |(527909243/1000000000 : ℝ)|=(527909243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2255248083/10000000000 : ℝ)|^2049 ≤ (13731965519941/100000000000000 : ℝ)^1537
        have hw : |(-2255248083/10000000000 : ℝ)|=(2255248083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_7 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068800643/2500000000 : ℝ)*x 0 + (2220768009/5000000000 : ℝ)*x 1 + (277595947/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068800643/2500000000 : ℝ)^2049 ≤ (16106170914403/50000000000000 : ℝ)^1537 := by
    have hnat : (1068800643 : ℕ)^2049*50000000000000^1537 ≤ 16106170914403^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068800643 2500000000 16106170914403 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220768009/5000000000 : ℝ)^2049 ≤ (16946916742479/50000000000000 : ℝ)^1537 := by
    have hnat : (2220768009 : ℕ)^2049*50000000000000^1537 ≤ 16946916742479^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220768009 5000000000 16946916742479 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277595947/625000000 : ℝ)^2049 ≤ (529591010547/1562500000000 : ℝ)^1537 := by
    have hnat : (277595947 : ℕ)^2049*1562500000000^1537 ≤ 529591010547^1537*625000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277595947 625000000 529591010547 1562500000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068800643/2500000000 : ℝ), (2220768009/5000000000 : ℝ), (277595947/625000000 : ℝ)] ![(16106170914403/50000000000000 : ℝ), (16946916742479/50000000000000 : ℝ), (529591010547/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068800643/2500000000 : ℝ)|^2049 ≤ (16106170914403/50000000000000 : ℝ)^1537
        have hw : |(1068800643/2500000000 : ℝ)|=(1068800643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2220768009/5000000000 : ℝ)|^2049 ≤ (16946916742479/50000000000000 : ℝ)^1537
        have hw : |(2220768009/5000000000 : ℝ)|=(2220768009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277595947/625000000 : ℝ)|^2049 ≤ (529591010547/1562500000000 : ℝ)^1537
        have hw : |(277595947/625000000 : ℝ)|=(277595947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_8 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2313056799/10000000000 : ℝ)*x 0 + (2605984409/5000000000 : ℝ)*x 1 + (2693895899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2313056799/10000000000 : ℝ)^2049 ≤ (14203202765853/100000000000000 : ℝ)^1537 := by
    have hnat : (2313056799 : ℕ)^2049*100000000000000^1537 ≤ 14203202765853^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313056799 10000000000 14203202765853 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605984409/5000000000 : ℝ)^2049 ≤ (41949853928703/100000000000000 : ℝ)^1537 := by
    have hnat : (2605984409 : ℕ)^2049*100000000000000^1537 ≤ 41949853928703^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605984409 5000000000 41949853928703 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693895899/5000000000 : ℝ)^2049 ≤ (43846943293357/100000000000000 : ℝ)^1537 := by
    have hnat : (2693895899 : ℕ)^2049*100000000000000^1537 ≤ 43846943293357^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693895899 5000000000 43846943293357 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2313056799/10000000000 : ℝ), (2605984409/5000000000 : ℝ), (2693895899/5000000000 : ℝ)] ![(14203202765853/100000000000000 : ℝ), (41949853928703/100000000000000 : ℝ), (43846943293357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2313056799/10000000000 : ℝ)|^2049 ≤ (14203202765853/100000000000000 : ℝ)^1537
        have hw : |(-2313056799/10000000000 : ℝ)|=(2313056799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605984409/5000000000 : ℝ)|^2049 ≤ (41949853928703/100000000000000 : ℝ)^1537
        have hw : |(2605984409/5000000000 : ℝ)|=(2605984409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693895899/5000000000 : ℝ)|^2049 ≤ (43846943293357/100000000000000 : ℝ)^1537
        have hw : |(2693895899/5000000000 : ℝ)|=(2693895899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_9 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5287637597/10000000000 : ℝ)*x 0 + (-553225779/2500000000 : ℝ)*x 1 + (2693896041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287637597/10000000000 : ℝ)^2049 ≤ (21381865690159/50000000000000 : ℝ)^1537 := by
    have hnat : (5287637597 : ℕ)^2049*50000000000000^1537 ≤ 21381865690159^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287637597 10000000000 21381865690159 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553225779/2500000000 : ℝ)^2049 ≤ (3347330557753/25000000000000 : ℝ)^1537 := by
    have hnat : (553225779 : ℕ)^2049*25000000000000^1537 ≤ 3347330557753^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553225779 2500000000 3347330557753 25000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693896041/5000000000 : ℝ)^2049 ≤ (21923473187261/50000000000000 : ℝ)^1537 := by
    have hnat : (2693896041 : ℕ)^2049*50000000000000^1537 ≤ 21923473187261^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693896041 5000000000 21923473187261 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287637597/10000000000 : ℝ), (-553225779/2500000000 : ℝ), (2693896041/5000000000 : ℝ)] ![(21381865690159/50000000000000 : ℝ), (3347330557753/25000000000000 : ℝ), (21923473187261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287637597/10000000000 : ℝ)|^2049 ≤ (21381865690159/50000000000000 : ℝ)^1537
        have hw : |(5287637597/10000000000 : ℝ)|=(5287637597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553225779/2500000000 : ℝ)|^2049 ≤ (3347330557753/25000000000000 : ℝ)^1537
        have hw : |(-553225779/2500000000 : ℝ)|=(553225779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693896041/5000000000 : ℝ)|^2049 ≤ (21923473187261/50000000000000 : ℝ)^1537
        have hw : |(2693896041/5000000000 : ℝ)|=(2693896041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_10 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643819049/5000000000 : ℝ)*x 0 + (5387791833/10000000000 : ℝ)*x 1 + (-1106451391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643819049/5000000000 : ℝ)^2049 ≤ (8552747356377/20000000000000 : ℝ)^1537 := by
    have hnat : (2643819049 : ℕ)^2049*20000000000000^1537 ≤ 8552747356377^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643819049 5000000000 8552747356377 20000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387791833/10000000000 : ℝ)^2049 ≤ (21923471836539/50000000000000 : ℝ)^1537 := by
    have hnat : (5387791833 : ℕ)^2049*50000000000000^1537 ≤ 21923471836539^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387791833 10000000000 21923471836539 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106451391/5000000000 : ℝ)^2049 ≤ (13389319536931/100000000000000 : ℝ)^1537 := by
    have hnat : (1106451391 : ℕ)^2049*100000000000000^1537 ≤ 13389319536931^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106451391 5000000000 13389319536931 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643819049/5000000000 : ℝ), (5387791833/10000000000 : ℝ), (-1106451391/5000000000 : ℝ)] ![(8552747356377/20000000000000 : ℝ), (21923471836539/50000000000000 : ℝ), (13389319536931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643819049/5000000000 : ℝ)|^2049 ≤ (8552747356377/20000000000000 : ℝ)^1537
        have hw : |(2643819049/5000000000 : ℝ)|=(2643819049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387791833/10000000000 : ℝ)|^2049 ≤ (21923471836539/50000000000000 : ℝ)^1537
        have hw : |(5387791833/10000000000 : ℝ)|=(5387791833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106451391/5000000000 : ℝ)|^2049 ≤ (13389319536931/100000000000000 : ℝ)^1537
        have hw : |(-1106451391/5000000000 : ℝ)|=(1106451391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_11 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1128659471/2500000000 : ℝ)*x 0 + (1080424901/2500000000 : ℝ)*x 1 + (540212409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128659471/2500000000 : ℝ)^2049 ≤ (34639541237937/100000000000000 : ℝ)^1537 := by
    have hnat : (1128659471 : ℕ)^2049*100000000000000^1537 ≤ 34639541237937^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128659471 2500000000 34639541237937 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080424901/2500000000 : ℝ)^2049 ≤ (6536046209931/20000000000000 : ℝ)^1537 := by
    have hnat : (1080424901 : ℕ)^2049*20000000000000^1537 ≤ 6536046209931^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080424901 2500000000 6536046209931 20000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540212409/1250000000 : ℝ)^2049 ≤ (32680227702801/100000000000000 : ℝ)^1537 := by
    have hnat : (540212409 : ℕ)^2049*100000000000000^1537 ≤ 32680227702801^1537*1250000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540212409 1250000000 32680227702801 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1128659471/2500000000 : ℝ), (1080424901/2500000000 : ℝ), (540212409/1250000000 : ℝ)] ![(34639541237937/100000000000000 : ℝ), (6536046209931/20000000000000 : ℝ), (32680227702801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1128659471/2500000000 : ℝ)|^2049 ≤ (34639541237937/100000000000000 : ℝ)^1537
        have hw : |(1128659471/2500000000 : ℝ)|=(1128659471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080424901/2500000000 : ℝ)|^2049 ≤ (6536046209931/20000000000000 : ℝ)^1537
        have hw : |(1080424901/2500000000 : ℝ)|=(1080424901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540212409/1250000000 : ℝ)|^2049 ≤ (32680227702801/100000000000000 : ℝ)^1537
        have hw : |(540212409/1250000000 : ℝ)|=(540212409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_12 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-10795447/50000000 : ℝ)*x 0 + (1360984771/2500000000 : ℝ)*x 1 + (164722759/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10795447/50000000 : ℝ)^2049 ≤ (12957022478251/100000000000000 : ℝ)^1537 := by
    have hnat : (10795447 : ℕ)^2049*100000000000000^1537 ≤ 12957022478251^1537*50000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10795447 50000000 12957022478251 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360984771/2500000000 : ℝ)^2049 ≤ (8891429953033/20000000000000 : ℝ)^1537 := by
    have hnat : (1360984771 : ℕ)^2049*20000000000000^1537 ≤ 8891429953033^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360984771 2500000000 8891429953033 20000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164722759/312500000 : ℝ)^2049 ≤ (5323228467567/12500000000000 : ℝ)^1537 := by
    have hnat : (164722759 : ℕ)^2049*12500000000000^1537 ≤ 5323228467567^1537*312500000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164722759 312500000 5323228467567 12500000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10795447/50000000 : ℝ), (1360984771/2500000000 : ℝ), (164722759/312500000 : ℝ)] ![(12957022478251/100000000000000 : ℝ), (8891429953033/20000000000000 : ℝ), (5323228467567/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10795447/50000000 : ℝ)|^2049 ≤ (12957022478251/100000000000000 : ℝ)^1537
        have hw : |(-10795447/50000000 : ℝ)|=(10795447/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360984771/2500000000 : ℝ)|^2049 ≤ (8891429953033/20000000000000 : ℝ)^1537
        have hw : |(1360984771/2500000000 : ℝ)|=(1360984771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164722759/312500000 : ℝ)|^2049 ≤ (5323228467567/12500000000000 : ℝ)^1537
        have hw : |(164722759/312500000 : ℝ)|=(164722759/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_13 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167822649/312500000 : ℝ)*x 0 + (-2258286303/10000000000 : ℝ)*x 1 + (131778199/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167822649/312500000 : ℝ)^2049 ≤ (1746301715003/4000000000000 : ℝ)^1537 := by
    have hnat : (167822649 : ℕ)^2049*4000000000000^1537 ≤ 1746301715003^1537*312500000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167822649 312500000 1746301715003 4000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258286303/10000000000 : ℝ)^2049 ≤ (429894778257/3125000000000 : ℝ)^1537 := by
    have hnat : (2258286303 : ℕ)^2049*3125000000000^1537 ≤ 429894778257^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258286303 10000000000 429894778257 3125000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131778199/250000000 : ℝ)^2049 ≤ (42585824207863/100000000000000 : ℝ)^1537 := by
    have hnat : (131778199 : ℕ)^2049*100000000000000^1537 ≤ 42585824207863^1537*250000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131778199 250000000 42585824207863 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167822649/312500000 : ℝ), (-2258286303/10000000000 : ℝ), (131778199/250000000 : ℝ)] ![(1746301715003/4000000000000 : ℝ), (429894778257/3125000000000 : ℝ), (42585824207863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167822649/312500000 : ℝ)|^2049 ≤ (1746301715003/4000000000000 : ℝ)^1537
        have hw : |(167822649/312500000 : ℝ)|=(167822649/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2258286303/10000000000 : ℝ)|^2049 ≤ (429894778257/3125000000000 : ℝ)^1537
        have hw : |(-2258286303/10000000000 : ℝ)|=(2258286303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131778199/250000000 : ℝ)|^2049 ≤ (42585824207863/100000000000000 : ℝ)^1537
        have hw : |(131778199/250000000 : ℝ)|=(131778199/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_14 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370324477/10000000000 : ℝ)*x 0 + (2635564263/5000000000 : ℝ)*x 1 + (-112914297/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370324477/10000000000 : ℝ)^2049 ≤ (43657539721379/100000000000000 : ℝ)^1537 := by
    have hnat : (5370324477 : ℕ)^2049*100000000000000^1537 ≤ 43657539721379^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370324477 10000000000 43657539721379 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635564263/5000000000 : ℝ)^2049 ≤ (21292915151939/50000000000000 : ℝ)^1537 := by
    have hnat : (2635564263 : ℕ)^2049*50000000000000^1537 ≤ 21292915151939^1537*5000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635564263 5000000000 21292915151939 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112914297/500000000 : ℝ)^2049 ≤ (6878314978179/50000000000000 : ℝ)^1537 := by
    have hnat : (112914297 : ℕ)^2049*50000000000000^1537 ≤ 6878314978179^1537*500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112914297 500000000 6878314978179 50000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370324477/10000000000 : ℝ), (2635564263/5000000000 : ℝ), (-112914297/500000000 : ℝ)] ![(43657539721379/100000000000000 : ℝ), (21292915151939/50000000000000 : ℝ), (6878314978179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370324477/10000000000 : ℝ)|^2049 ≤ (43657539721379/100000000000000 : ℝ)^1537
        have hw : |(5370324477/10000000000 : ℝ)|=(5370324477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635564263/5000000000 : ℝ)|^2049 ≤ (21292915151939/50000000000000 : ℝ)^1537
        have hw : |(2635564263/5000000000 : ℝ)|=(2635564263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112914297/500000000 : ℝ)|^2049 ≤ (6878314978179/50000000000000 : ℝ)^1537
        have hw : |(-112914297/500000000 : ℝ)|=(112914297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1003_box_15 (p : ℝ) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4257408059/10000000000 : ℝ)*x 0 + (1112577937/2500000000 : ℝ)*x 1 + (4450311151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257408059/10000000000 : ℝ)^2049 ≤ (32033726660663/100000000000000 : ℝ)^1537 := by
    have hnat : (4257408059 : ℕ)^2049*100000000000000^1537 ≤ 32033726660663^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257408059 10000000000 32033726660663 100000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112577937/2500000000 : ℝ)^2049 ≤ (8495784924987/25000000000000 : ℝ)^1537 := by
    have hnat : (1112577937 : ℕ)^2049*25000000000000^1537 ≤ 8495784924987^1537*2500000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112577937 2500000000 8495784924987 25000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4450311151/10000000000 : ℝ)^2049 ≤ (1699156681129/5000000000000 : ℝ)^1537 := by
    have hnat : (4450311151 : ℕ)^2049*5000000000000^1537 ≤ 1699156681129^1537*10000000000^2049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450311151 10000000000 1699156681129 5000000000000 2049 1537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2049/512 : ℝ)) 2049 1537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257408059/10000000000 : ℝ), (1112577937/2500000000 : ℝ), (4450311151/10000000000 : ℝ)] ![(32033726660663/100000000000000 : ℝ), (8495784924987/25000000000000 : ℝ), (1699156681129/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257408059/10000000000 : ℝ)|^2049 ≤ (32033726660663/100000000000000 : ℝ)^1537
        have hw : |(4257408059/10000000000 : ℝ)|=(4257408059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1112577937/2500000000 : ℝ)|^2049 ≤ (8495784924987/25000000000000 : ℝ)^1537
        have hw : |(1112577937/2500000000 : ℝ)|=(1112577937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4450311151/10000000000 : ℝ)|^2049 ≤ (1699156681129/5000000000000 : ℝ)^1537
        have hw : |(4450311151/10000000000 : ℝ)|=(4450311151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1003_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29353803/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6981/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11839/20000 : ℝ) ∧ (19843/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82807/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6981/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6981/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6981/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6981/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6981/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6981/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11163/100000 : ℝ) ^ (8195/2048 : ℝ) ≤ (967406194967741/6250000000000000000 : ℝ) := by
    have hpowers : (11163/100000 : ℝ)^8195 ≤ (967406194967741/6250000000000000000 : ℝ)^2048 := by
      have hnat : (11163 : ℕ)^8195*6250000000000000000^2048 ≤ 967406194967741^2048*100000^8195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11163 100000 967406194967741 6250000000000000000 8195 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11163/100000 : ℝ)) (X := (967406194967741/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8195 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6981/50000 : ℝ) ^ (8195/2048 : ℝ) ≤ (18945585042767197/50000000000000000000 : ℝ) := by
    have hpowers : (6981/50000 : ℝ)^8195 ≤ (18945585042767197/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6981 : ℕ)^8195*50000000000000000000^2048 ≤ 18945585042767197^2048*50000^8195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6981 50000 18945585042767197 50000000000000000000 8195 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6981/50000 : ℝ)) (X := (18945585042767197/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8195 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125967406194967741/3125000000000000000 : ℝ) ≤ (10000773551834117/10000000000000000 : ℝ) ^ (8195/2048 : ℝ) := by
    have hpowers : (3125967406194967741/3125000000000000000 : ℝ)^2048 ≤ (10000773551834117/10000000000000000 : ℝ)^8195 := by
      have hnat : (3125967406194967741 : ℕ)^2048*10000000000000000^8195 ≤ 10000773551834117^8195*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125967406194967741 3125000000000000000 10000773551834117 10000000000000000 2048 8195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000773551834117/10000000000000000 : ℝ)) (X := (3125967406194967741/3125000000000000000 : ℝ)) (by norm_num) 8195 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (400213478676820073/400000000000000000 : ℝ) ≤ (10001333486413199/10000000000000000 : ℝ) ^ (8195/2048 : ℝ) := by
    have hpowers : (400213478676820073/400000000000000000 : ℝ)^2048 ≤ (10001333486413199/10000000000000000 : ℝ)^8195 := by
      have hnat : (400213478676820073 : ℕ)^2048*10000000000000000^8195 ≤ 10001333486413199^8195*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400213478676820073 400000000000000000 10001333486413199 10000000000000000 2048 8195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001333486413199/10000000000000000 : ℝ)) (X := (400213478676820073/400000000000000000 : ℝ)) (by norm_num) 8195 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018945585042767197/25000000000000000000 : ℝ) ≤ (10001893420992281/10000000000000000 : ℝ) ^ (8195/2048 : ℝ) := by
    have hpowers : (25018945585042767197/25000000000000000000 : ℝ)^2048 ≤ (10001893420992281/10000000000000000 : ℝ)^8195 := by
      have hnat : (25018945585042767197 : ℕ)^2048*10000000000000000^8195 ≤ 10001893420992281^8195*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018945585042767197 25000000000000000000 10001893420992281 10000000000000000 2048 8195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001893420992281/10000000000000000 : ℝ)) (X := (25018945585042767197/25000000000000000000 : ℝ)) (by norm_num) 8195 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(967406194967741/6250000000000000000 : ℝ) ≤ ((3108851563574567639/3110000000000000000 : ℝ)+2*(93322429847/46650000000000 : ℝ)*(11163/100000 : ℝ))^(8195/2048 : ℝ) := by
    rw [show (3108851563574567639/3110000000000000000 : ℝ)+2*(93322429847/46650000000000 : ℝ)*(11163/100000 : ℝ)=(10000773551834117/10000000000000000 : ℝ) by norm_num, show 1+2*(967406194967741/6250000000000000000 : ℝ)=(3125967406194967741/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18945585042767197/50000000000000000000 : ℝ)+(967406194967741/6250000000000000000 : ℝ) ≤ ((3108851563574567639/3110000000000000000 : ℝ)+(93322429847/46650000000000 : ℝ)*((6981/50000 : ℝ)+(11163/100000 : ℝ)))^(8195/2048 : ℝ) := by
    rw [show (3108851563574567639/3110000000000000000 : ℝ)+(93322429847/46650000000000 : ℝ)*((6981/50000 : ℝ)+(11163/100000 : ℝ))=(10001333486413199/10000000000000000 : ℝ) by norm_num, show 1+(18945585042767197/50000000000000000000 : ℝ)+(967406194967741/6250000000000000000 : ℝ)=(400213478676820073/400000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18945585042767197/50000000000000000000 : ℝ) ≤ ((3108851563574567639/3110000000000000000 : ℝ)+2*(93322429847/46650000000000 : ℝ)*(6981/50000 : ℝ))^(8195/2048 : ℝ) := by
    rw [show (3108851563574567639/3110000000000000000 : ℝ)+2*(93322429847/46650000000000 : ℝ)*(6981/50000 : ℝ)=(10001893420992281/10000000000000000 : ℝ) by norm_num, show 1+2*(18945585042767197/50000000000000000000 : ℝ)=(25018945585042767197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3108851563574567639/3110000000000000000 : ℝ)*(X 1 0+X 2 0)+(93322429847/46650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8195/2048 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (6981/50000 : ℝ)) (c := (3108851563574567639/3110000000000000000 : ℝ)) (alpha := (93322429847/46650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3108851563574567639/3110000000000000000 : ℝ)*(X 0 1+X 2 1)+(93322429847/46650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8195/2048 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (6981/50000 : ℝ)) (c := (3108851563574567639/3110000000000000000 : ℝ)) (alpha := (93322429847/46650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3108851563574567639/3110000000000000000 : ℝ)*(X 0 2+X 1 2)+(93322429847/46650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8195/2048 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (6981/50000 : ℝ)) (c := (3108851563574567639/3110000000000000000 : ℝ)) (alpha := (93322429847/46650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2103491277/10000000000 : ℝ)*X 0 0+(5378201573/10000000000 : ℝ)*X 0 1+(1344550403/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294439043/10000000000 : ℝ)*X 1 0+(-2216704553/10000000000 : ℝ)*X 1 1+(2689100817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1058887809/2000000000 : ℝ)*X 2 0+(5378201563/10000000000 : ℝ)*X 2 1+(-1108352323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4493762307/10000000000 : ℝ)*X 0 0+(4332277717/10000000000 : ℝ)*X 0 1+(433227773/1000000000 : ℝ)*X 0 2+(4493762307/10000000000 : ℝ)*X 1 0+(4332277717/10000000000 : ℝ)*X 1 1+(433227773/1000000000 : ℝ)*X 1 2+(4493762307/10000000000 : ℝ)*X 2 0+(4332277717/10000000000 : ℝ)*X 2 1+(433227773/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-148015213/625000000 : ℝ)*X 0 0+(659886587/1250000000 : ℝ)*X 0 1+(2639546357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((134117063/250000000 : ℝ)*X 1 0+(-281905979/1250000000 : ℝ)*X 1 1+(5279092857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1341170689/2500000000 : ℝ)*X 2 0+(527909243/1000000000 : ℝ)*X 2 1+(-2255248083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1068800643/2500000000 : ℝ)*X 0 0+(2220768009/5000000000 : ℝ)*X 0 1+(277595947/625000000 : ℝ)*X 0 2+(1068800643/2500000000 : ℝ)*X 1 0+(2220768009/5000000000 : ℝ)*X 1 1+(277595947/625000000 : ℝ)*X 1 2+(1068800643/2500000000 : ℝ)*X 2 0+(2220768009/5000000000 : ℝ)*X 2 1+(277595947/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2313056799/10000000000 : ℝ)*X 0 0+(2605984409/5000000000 : ℝ)*X 0 1+(2693895899/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5287637597/10000000000 : ℝ)*X 1 0+(-553225779/2500000000 : ℝ)*X 1 1+(2693896041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2643819049/5000000000 : ℝ)*X 2 0+(5387791833/10000000000 : ℝ)*X 2 1+(-1106451391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1128659471/2500000000 : ℝ)*X 0 0+(1080424901/2500000000 : ℝ)*X 0 1+(540212409/1250000000 : ℝ)*X 0 2+(1128659471/2500000000 : ℝ)*X 1 0+(1080424901/2500000000 : ℝ)*X 1 1+(540212409/1250000000 : ℝ)*X 1 2+(1128659471/2500000000 : ℝ)*X 2 0+(1080424901/2500000000 : ℝ)*X 2 1+(540212409/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-10795447/50000000 : ℝ)*X 0 0+(1360984771/2500000000 : ℝ)*X 0 1+(164722759/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((167822649/312500000 : ℝ)*X 1 0+(-2258286303/10000000000 : ℝ)*X 1 1+(131778199/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370324477/10000000000 : ℝ)*X 2 0+(2635564263/5000000000 : ℝ)*X 2 1+(-112914297/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4257408059/10000000000 : ℝ)*X 0 0+(1112577937/2500000000 : ℝ)*X 0 1+(4450311151/10000000000 : ℝ)*X 0 2+(4257408059/10000000000 : ℝ)*X 1 0+(1112577937/2500000000 : ℝ)*X 1 1+(4450311151/10000000000 : ℝ)*X 1 2+(4257408059/10000000000 : ℝ)*X 2 0+(1112577937/2500000000 : ℝ)*X 2 1+(4450311151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1003_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-4837626176654697766770402487129/7775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10187421/6250000000000 : ℝ)*(lower0) + (6458243/50000000000000 : ℝ)*(upper3) + (21947431/20000000000000 : ℝ)*(lower5) + (380302271562637/10000000000000 : ℝ)*(major0) + (380302271562637/10000000000000 : ℝ)*(major1) + (380302271562637/10000000000000 : ℝ)*(major2) + (15860721363/100000000000000 : ℝ)*(sp2) + (2517809603189947/50000000000000 : ℝ)*(sp4) + (2517805255495861/50000000000000 : ℝ)*(sp5) + (2517803908615557/50000000000000 : ℝ)*(sp6) + (518210257942467/20000000000000 : ℝ)*(sp7) + (4471572583/100000000000000 : ℝ)*(sp8) + (3291740189/25000000000000 : ℝ)*(sp13) + (5527718871/5000000000000 : ℝ)*(sp15) + (647790461022439/25000000000000 : ℝ)*(f.failure) + (2517811838976239/50000000000000 : ℝ)*(f.sum) + (1442976545167/933000000000000000000000000 : ℝ)*base66 + (4176012990783487871/93300000000000000000000000000000 : ℝ)*base68 + (1555434598015912129/93300000000000000000000000000000 : ℝ)*base69 + (1293515321954512129/93300000000000000000000000000000 : ℝ)*base71 + (22488922951919/466500000000000000000000000 : ℝ)*base74 + (1444398178074712129/93300000000000000000000000000000 : ℝ)*base75 + (1576551650810212129/93300000000000000000000000000000 : ℝ)*base77 + (2612906810132212129/93300000000000000000000000000000 : ℝ)*base79 + (290084768423/116625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2985517/500000000000000000000 : ℝ)*base89 + (2985517/500000000000000000000 : ℝ)*base91 + (2985517/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11839/20000 : ℝ) ≤ (23012853568001185744671979922781/38875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4204167/25000000000000 : ℝ)*(lower0) + (870383/50000000000000 : ℝ)*(upper1) + (11132543/25000000000000 : ℝ)*(upper2) + (966228252295407/25000000000000 : ℝ)*(major0) + (966228252295407/25000000000000 : ℝ)*(major1) + (966228252295407/25000000000000 : ℝ)*(major2) + (507676161935681/10000000000000 : ℝ)*(sp0) + (5076760179879957/100000000000000 : ℝ)*(sp1) + (2538364408352031/50000000000000 : ℝ)*(sp2) + (1316663873409569/50000000000000 : ℝ)*(sp3) + (3143069119/100000000000000 : ℝ)*(sp5) + (17253122507/50000000000000 : ℝ)*(sp10) + (2598268773/100000000000000 : ℝ)*(sp11) + (851796133/50000000000000 : ℝ)*(sp12) + (329166293135989/12500000000000 : ℝ)*(f.failure) + (1269190830737269/25000000000000 : ℝ)*(f.sum) + (432593986363/194375000000000000000000000 : ℝ)*base65 + (62870205921134073/77750000000000000000000000000000 : ℝ)*base67 + (697479077988134073/77750000000000000000000000000000 : ℝ)*base69 + (82311468500615927/77750000000000000000000000000000 : ℝ)*base72 + (13889111908051/1555000000000000000000000000 : ℝ)*base74 + (436578503932384073/77750000000000000000000000000000 : ℝ)*base75 + (64178856935865927/77750000000000000000000000000000 : ℝ)*base78 + (1787735832862634073/77750000000000000000000000000000 : ℝ)*base79 + (526809061291/388750000000000000000000000 : ℝ)*base81 + (3316167/250000000000000000000 : ℝ)*base89 + (3316167/250000000000000000000 : ℝ)*base91 + (3316167/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19843/25000 : ℝ) ≤ (61713331847605473890520954985653/77750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103518471/100000000000000 : ℝ)*(lower3) + (72441779/25000000000000 : ℝ)*(upper4) + (357061/2500000000000 : ℝ)*(lower5) + (2166601982640597/50000000000000 : ℝ)*(major0) + (2166601982640597/50000000000000 : ℝ)*(major1) + (2166601982640597/50000000000000 : ℝ)*(major2) + (731402177/100000000000000 : ℝ)*(sp0) + (11083795149/4000000000000 : ℝ)*(sp1) + (284203508491/100000000000000 : ℝ)*(sp2) + (167511475191/100000000000000 : ℝ)*(sp3) + (2843776099931067/50000000000000 : ℝ)*(sp8) + (2843637918192793/50000000000000 : ℝ)*(sp9) + (5687268727755819/100000000000000 : ℝ)*(sp10) + (2952229467738163/100000000000000 : ℝ)*(sp11) + (1476198489606677/50000000000000 : ℝ)*(f.failure) + (5687552931264311/100000000000000 : ℝ)*(f.sum) + (1491166101329/777500000000000000000000000 : ℝ)*base66 + (245501976538440483/155500000000000000000000000000000 : ℝ)*base67 + (228500914293440483/155500000000000000000000000000000 : ℝ)*base69 + (872997142211440483/155500000000000000000000000000000 : ℝ)*base71 + (2467046074411/777500000000000000000000000 : ℝ)*base73 + (241115004940440483/155500000000000000000000000000000 : ℝ)*base75 + (1306455516341440483/155500000000000000000000000000000 : ℝ)*base77 + (1293193236539940483/155500000000000000000000000000000 : ℝ)*base79 + (519104864251/777500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4142631/1000000000000000000000 : ℝ)*base89 + (4142631/1000000000000000000000 : ℝ)*base91 + (4142631/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82807/100000 : ℝ) ≤ (-64380749206641557574451389320451/77750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58745601/20000000000000 : ℝ)*(lower0) + (7681571/100000000000000 : ℝ)*(upper1) + (25366623/50000000000000 : ℝ)*(upper3) + (7346667/2500000000000 : ℝ)*(upper5) + (2183680995510103/50000000000000 : ℝ)*(major0) + (2183680995510103/50000000000000 : ℝ)*(major1) + (2183680995510103/50000000000000 : ℝ)*(major2) + (6097930419/100000000000000 : ℝ)*(sp4) + (149223916319/50000000000000 : ℝ)*(sp5) + (7897499959/12500000000000 : ℝ)*(sp7) + (1157329838016301/20000000000000 : ℝ)*(sp12) + (5786356840179287/100000000000000 : ℝ)*(sp13) + (1446663822002981/25000000000000 : ℝ)*(sp14) + (743901780351427/25000000000000 : ℝ)*(sp15) + (148783515070269/5000000000000 : ℝ)*(f.failure) + (1446663822002981/25000000000000 : ℝ)*(f.sum) + (1934474250587/583125000000000000000000000 : ℝ)*base66 + (13341586259453729549/466500000000000000000000000000000 : ℝ)*base68 + (3606780487335270451/466500000000000000000000000000000 : ℝ)*base69 + (2248087726914270451/466500000000000000000000000000000 : ℝ)*base71 + (172814266924469/4665000000000000000000000000 : ℝ)*base73 + (20680539354884729549/466500000000000000000000000000000 : ℝ)*base76 + (5688853842576270451/466500000000000000000000000000000 : ℝ)*base77 + (4128660080376270451/466500000000000000000000000000000 : ℝ)*base79 + (358579281769/72890625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1383007/100000000000000000000 : ℝ)*base89 + (1383007/100000000000000000000 : ℝ)*base91 + (1383007/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1003_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29353803/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6981/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11839/20000 : ℝ) else (19843/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82807/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1003_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29353803/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6981/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11839/20000 : ℝ) else (19843/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82807/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1003_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
