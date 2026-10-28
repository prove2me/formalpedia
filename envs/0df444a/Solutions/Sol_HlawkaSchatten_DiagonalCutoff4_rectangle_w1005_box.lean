-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1005_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:48:15.620102+00:00
-- url     : https://prove2.me/submissions/5b8c1800-3252-47c1-b4cf-657e0cb58791

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
theorem support_rectangle_w1005_box_0 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051276513/5000000000 : ℝ)*x 0 + (2689088071/5000000000 : ℝ)*x 1 + (2689088129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051276513/5000000000 : ℝ)^4099 ≤ (3127203883931/25000000000000 : ℝ)^3075 := by
    have hnat : (1051276513 : ℕ)^4099*25000000000000^3075 ≤ 3127203883931^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051276513 5000000000 3127203883931 25000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689088071/5000000000 : ℝ)^4099 ≤ (1749823663833/4000000000000 : ℝ)^3075 := by
    have hnat : (2689088071 : ℕ)^4099*4000000000000^3075 ≤ 1749823663833^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689088071 5000000000 1749823663833 4000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2689088129/5000000000 : ℝ)^4099 ≤ (21872796426781/50000000000000 : ℝ)^3075 := by
    have hnat : (2689088129 : ℕ)^4099*50000000000000^3075 ≤ 21872796426781^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689088129 5000000000 21872796426781 50000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051276513/5000000000 : ℝ), (2689088071/5000000000 : ℝ), (2689088129/5000000000 : ℝ)] ![(3127203883931/25000000000000 : ℝ), (1749823663833/4000000000000 : ℝ), (21872796426781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051276513/5000000000 : ℝ)|^4099 ≤ (3127203883931/25000000000000 : ℝ)^3075
        have hw : |(-1051276513/5000000000 : ℝ)|=(1051276513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689088071/5000000000 : ℝ)|^4099 ≤ (1749823663833/4000000000000 : ℝ)^3075
        have hw : |(2689088071/5000000000 : ℝ)|=(2689088071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2689088129/5000000000 : ℝ)|^4099 ≤ (21872796426781/50000000000000 : ℝ)^3075
        have hw : |(2689088129/5000000000 : ℝ)|=(2689088129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_1 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294462097/10000000000 : ℝ)*x 0 + (-221570599/1000000000 : ℝ)*x 1 + (537817671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294462097/10000000000 : ℝ)^4099 ≤ (535503464753/1250000000000 : ℝ)^3075 := by
    have hnat : (5294462097 : ℕ)^4099*1250000000000^3075 ≤ 535503464753^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294462097 10000000000 535503464753 1250000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221570599/1000000000 : ℝ)^4099 ≤ (13414125049849/100000000000000 : ℝ)^3075 := by
    have hnat : (221570599 : ℕ)^4099*100000000000000^3075 ≤ 13414125049849^3075*1000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221570599 1000000000 13414125049849 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537817671/1000000000 : ℝ)^4099 ≤ (21872798877201/50000000000000 : ℝ)^3075 := by
    have hnat : (537817671 : ℕ)^4099*50000000000000^3075 ≤ 21872798877201^3075*1000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537817671 1000000000 21872798877201 50000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294462097/10000000000 : ℝ), (-221570599/1000000000 : ℝ), (537817671/1000000000 : ℝ)] ![(535503464753/1250000000000 : ℝ), (13414125049849/100000000000000 : ℝ), (21872798877201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294462097/10000000000 : ℝ)|^4099 ≤ (535503464753/1250000000000 : ℝ)^3075
        have hw : |(5294462097/10000000000 : ℝ)|=(5294462097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221570599/1000000000 : ℝ)|^4099 ≤ (13414125049849/100000000000000 : ℝ)^3075
        have hw : |(-221570599/1000000000 : ℝ)|=(221570599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537817671/1000000000 : ℝ)|^4099 ≤ (21872798877201/50000000000000 : ℝ)^3075
        have hw : |(537817671/1000000000 : ℝ)|=(537817671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_2 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529446183/1000000000 : ℝ)*x 0 + (5378176003/10000000000 : ℝ)*x 1 + (-2215707297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529446183/1000000000 : ℝ)^4099 ≤ (42840274300359/100000000000000 : ℝ)^3075 := by
    have hnat : (529446183 : ℕ)^4099*100000000000000^3075 ≤ 42840274300359^3075*1000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529446183 1000000000 42840274300359 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5378176003/10000000000 : ℝ)^4099 ≤ (10936397522177/25000000000000 : ℝ)^3075 := by
    have hnat : (5378176003 : ℕ)^4099*25000000000000^3075 ≤ 10936397522177^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378176003 10000000000 10936397522177 25000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215707297/10000000000 : ℝ)^4099 ≤ (13414135597571/100000000000000 : ℝ)^3075 := by
    have hnat : (2215707297 : ℕ)^4099*100000000000000^3075 ≤ 13414135597571^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215707297 10000000000 13414135597571 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529446183/1000000000 : ℝ), (5378176003/10000000000 : ℝ), (-2215707297/10000000000 : ℝ)] ![(42840274300359/100000000000000 : ℝ), (10936397522177/25000000000000 : ℝ), (13414135597571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529446183/1000000000 : ℝ)|^4099 ≤ (42840274300359/100000000000000 : ℝ)^3075
        have hw : |(529446183/1000000000 : ℝ)|=(529446183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5378176003/10000000000 : ℝ)|^4099 ≤ (10936397522177/25000000000000 : ℝ)^3075
        have hw : |(5378176003/10000000000 : ℝ)|=(5378176003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2215707297/10000000000 : ℝ)|^4099 ≤ (13414135597571/100000000000000 : ℝ)^3075
        have hw : |(-2215707297/10000000000 : ℝ)|=(2215707297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_3 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (449344887/1000000000 : ℝ)*x 0 + (2165996897/5000000000 : ℝ)*x 1 + (2165997123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449344887/1000000000 : ℝ)^4099 ≤ (34425959586733/100000000000000 : ℝ)^3075 := by
    have hnat : (449344887 : ℕ)^4099*100000000000000^3075 ≤ 34425959586733^3075*1000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449344887 1000000000 34425959586733 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2165996897/5000000000 : ℝ)^4099 ≤ (32787017917389/100000000000000 : ℝ)^3075 := by
    have hnat : (2165996897 : ℕ)^4099*100000000000000^3075 ≤ 32787017917389^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165996897 5000000000 32787017917389 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165997123/5000000000 : ℝ)^4099 ≤ (8196755619401/25000000000000 : ℝ)^3075 := by
    have hnat : (2165997123 : ℕ)^4099*25000000000000^3075 ≤ 8196755619401^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165997123 5000000000 8196755619401 25000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449344887/1000000000 : ℝ), (2165996897/5000000000 : ℝ), (2165997123/5000000000 : ℝ)] ![(34425959586733/100000000000000 : ℝ), (32787017917389/100000000000000 : ℝ), (8196755619401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449344887/1000000000 : ℝ)|^4099 ≤ (34425959586733/100000000000000 : ℝ)^3075
        have hw : |(449344887/1000000000 : ℝ)|=(449344887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2165996897/5000000000 : ℝ)|^4099 ≤ (32787017917389/100000000000000 : ℝ)^3075
        have hw : |(2165996897/5000000000 : ℝ)|=(2165996897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2165997123/5000000000 : ℝ)|^4099 ≤ (8196755619401/25000000000000 : ℝ)^3075
        have hw : |(2165997123/5000000000 : ℝ)|=(2165997123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_4 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1183585913/5000000000 : ℝ)*x 0 + (5279122797/10000000000 : ℝ)*x 1 + (5279122693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1183585913/5000000000 : ℝ)^4099 ≤ (14650188527013/100000000000000 : ℝ)^3075 := by
    have hnat : (1183585913 : ℕ)^4099*100000000000000^3075 ≤ 14650188527013^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183585913 5000000000 14650188527013 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279122797/10000000000 : ℝ)^4099 ≤ (5334363285597/12500000000000 : ℝ)^3075 := by
    have hnat : (5279122797 : ℕ)^4099*12500000000000^3075 ≤ 5334363285597^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279122797 10000000000 5334363285597 12500000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279122693/10000000000 : ℝ)^4099 ≤ (10668726291027/25000000000000 : ℝ)^3075 := by
    have hnat : (5279122693 : ℕ)^4099*25000000000000^3075 ≤ 10668726291027^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279122693 10000000000 10668726291027 25000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1183585913/5000000000 : ℝ), (5279122797/10000000000 : ℝ), (5279122693/10000000000 : ℝ)] ![(14650188527013/100000000000000 : ℝ), (5334363285597/12500000000000 : ℝ), (10668726291027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1183585913/5000000000 : ℝ)|^4099 ≤ (14650188527013/100000000000000 : ℝ)^3075
        have hw : |(-1183585913/5000000000 : ℝ)|=(1183585913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279122797/10000000000 : ℝ)|^4099 ≤ (5334363285597/12500000000000 : ℝ)^3075
        have hw : |(5279122797/10000000000 : ℝ)|=(5279122797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279122693/10000000000 : ℝ)|^4099 ≤ (10668726291027/25000000000000 : ℝ)^3075
        have hw : |(5279122693/10000000000 : ℝ)|=(5279122693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_5 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335291439/625000000 : ℝ)*x 0 + (-112711777/500000000 : ℝ)*x 1 + (263956119/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335291439/625000000 : ℝ)^4099 ≤ (43599136053771/100000000000000 : ℝ)^3075 := by
    have hnat : (335291439 : ℕ)^4099*100000000000000^3075 ≤ 43599136053771^3075*625000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335291439 625000000 43599136053771 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112711777/500000000 : ℝ)^4099 ≤ (13725962144043/100000000000000 : ℝ)^3075 := by
    have hnat : (112711777 : ℕ)^4099*100000000000000^3075 ≤ 13725962144043^3075*500000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112711777 500000000 13725962144043 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263956119/500000000 : ℝ)^4099 ≤ (42674901791329/100000000000000 : ℝ)^3075 := by
    have hnat : (263956119 : ℕ)^4099*100000000000000^3075 ≤ 42674901791329^3075*500000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263956119 500000000 42674901791329 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335291439/625000000 : ℝ), (-112711777/500000000 : ℝ), (263956119/500000000 : ℝ)] ![(43599136053771/100000000000000 : ℝ), (13725962144043/100000000000000 : ℝ), (42674901791329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335291439/625000000 : ℝ)|^4099 ≤ (43599136053771/100000000000000 : ℝ)^3075
        have hw : |(335291439/625000000 : ℝ)|=(335291439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112711777/500000000 : ℝ)|^4099 ≤ (13725962144043/100000000000000 : ℝ)^3075
        have hw : |(-112711777/500000000 : ℝ)|=(112711777/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263956119/500000000 : ℝ)|^4099 ≤ (42674901791329/100000000000000 : ℝ)^3075
        have hw : |(263956119/500000000 : ℝ)|=(263956119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_6 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682331257/5000000000 : ℝ)*x 0 + (1055824597/2000000000 : ℝ)*x 1 + (-2254235417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682331257/5000000000 : ℝ)^4099 ≤ (43599130528693/100000000000000 : ℝ)^3075 := by
    have hnat : (2682331257 : ℕ)^4099*100000000000000^3075 ≤ 43599130528693^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682331257 5000000000 43599130528693 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055824597/2000000000 : ℝ)^4099 ≤ (42674908310599/100000000000000 : ℝ)^3075 := by
    have hnat : (1055824597 : ℕ)^4099*100000000000000^3075 ≤ 42674908310599^3075*2000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055824597 2000000000 42674908310599 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254235417/10000000000 : ℝ)^4099 ≤ (13725961145697/100000000000000 : ℝ)^3075 := by
    have hnat : (2254235417 : ℕ)^4099*100000000000000^3075 ≤ 13725961145697^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254235417 10000000000 13725961145697 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682331257/5000000000 : ℝ), (1055824597/2000000000 : ℝ), (-2254235417/10000000000 : ℝ)] ![(43599130528693/100000000000000 : ℝ), (42674908310599/100000000000000 : ℝ), (13725961145697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682331257/5000000000 : ℝ)|^4099 ≤ (43599130528693/100000000000000 : ℝ)^3075
        have hw : |(2682331257/5000000000 : ℝ)|=(2682331257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055824597/2000000000 : ℝ)|^4099 ≤ (42674908310599/100000000000000 : ℝ)^3075
        have hw : |(1055824597/2000000000 : ℝ)|=(1055824597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2254235417/10000000000 : ℝ)|^4099 ≤ (13725961145697/100000000000000 : ℝ)^3075
        have hw : |(-2254235417/10000000000 : ℝ)|=(2254235417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_7 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274928179/10000000000 : ℝ)*x 0 + (177649277/400000000 : ℝ)*x 1 + (2220616403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274928179/10000000000 : ℝ)^4099 ≤ (32212551074411/100000000000000 : ℝ)^3075 := by
    have hnat : (4274928179 : ℕ)^4099*100000000000000^3075 ≤ 32212551074411^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274928179 10000000000 32212551074411 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177649277/400000000 : ℝ)^4099 ≤ (3389371997261/10000000000000 : ℝ)^3075 := by
    have hnat : (177649277 : ℕ)^4099*10000000000000^3075 ≤ 3389371997261^3075*400000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177649277 400000000 3389371997261 10000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220616403/5000000000 : ℝ)^4099 ≤ (16946864467507/50000000000000 : ℝ)^3075 := by
    have hnat : (2220616403 : ℕ)^4099*50000000000000^3075 ≤ 16946864467507^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220616403 5000000000 16946864467507 50000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274928179/10000000000 : ℝ), (177649277/400000000 : ℝ), (2220616403/5000000000 : ℝ)] ![(32212551074411/100000000000000 : ℝ), (3389371997261/10000000000000 : ℝ), (16946864467507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274928179/10000000000 : ℝ)|^4099 ≤ (32212551074411/100000000000000 : ℝ)^3075
        have hw : |(4274928179/10000000000 : ℝ)|=(4274928179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177649277/400000000 : ℝ)|^4099 ≤ (3389371997261/10000000000000 : ℝ)^3075
        have hw : |(177649277/400000000 : ℝ)|=(177649277/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220616403/5000000000 : ℝ)|^4099 ≤ (16946864467507/50000000000000 : ℝ)^3075
        have hw : |(2220616403/5000000000 : ℝ)|=(2220616403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_8 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-144500661/625000000 : ℝ)*x 0 + (5212032263/10000000000 : ℝ)*x 1 + (5387767067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144500661/625000000 : ℝ)^4099 ≤ (14196891211489/100000000000000 : ℝ)^3075 := by
    have hnat : (144500661 : ℕ)^4099*100000000000000^3075 ≤ 14196891211489^3075*625000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144500661 625000000 14196891211489 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212032263/10000000000 : ℝ)^4099 ≤ (41953496076381/100000000000000 : ℝ)^3075 := by
    have hnat : (5212032263 : ℕ)^4099*100000000000000^3075 ≤ 41953496076381^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212032263 10000000000 41953496076381 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387767067/10000000000 : ℝ)^4099 ≤ (43849612697519/100000000000000 : ℝ)^3075 := by
    have hnat : (5387767067 : ℕ)^4099*100000000000000^3075 ≤ 43849612697519^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387767067 10000000000 43849612697519 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-144500661/625000000 : ℝ), (5212032263/10000000000 : ℝ), (5387767067/10000000000 : ℝ)] ![(14196891211489/100000000000000 : ℝ), (41953496076381/100000000000000 : ℝ), (43849612697519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-144500661/625000000 : ℝ)|^4099 ≤ (14196891211489/100000000000000 : ℝ)^3075
        have hw : |(-144500661/625000000 : ℝ)|=(144500661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212032263/10000000000 : ℝ)|^4099 ≤ (41953496076381/100000000000000 : ℝ)^3075
        have hw : |(5212032263/10000000000 : ℝ)|=(5212032263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387767067/10000000000 : ℝ)|^4099 ≤ (43849612697519/100000000000000 : ℝ)^3075
        have hw : |(5387767067/10000000000 : ℝ)|=(5387767067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_9 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287660307/10000000000 : ℝ)*x 0 + (-2211904487/10000000000 : ℝ)*x 1 + (5387767433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287660307/10000000000 : ℝ)^4099 ≤ (10691732074051/25000000000000 : ℝ)^3075 := by
    have hnat : (5287660307 : ℕ)^4099*25000000000000^3075 ≤ 10691732074051^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287660307 10000000000 10691732074051 25000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211904487/10000000000 : ℝ)^4099 ≤ (13383455018237/100000000000000 : ℝ)^3075 := by
    have hnat : (2211904487 : ℕ)^4099*100000000000000^3075 ≤ 13383455018237^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211904487 10000000000 13383455018237 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387767433/10000000000 : ℝ)^4099 ≤ (43849616668253/100000000000000 : ℝ)^3075 := by
    have hnat : (5387767433 : ℕ)^4099*100000000000000^3075 ≤ 43849616668253^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387767433 10000000000 43849616668253 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287660307/10000000000 : ℝ), (-2211904487/10000000000 : ℝ), (5387767433/10000000000 : ℝ)] ![(10691732074051/25000000000000 : ℝ), (13383455018237/100000000000000 : ℝ), (43849616668253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287660307/10000000000 : ℝ)|^4099 ≤ (10691732074051/25000000000000 : ℝ)^3075
        have hw : |(5287660307/10000000000 : ℝ)|=(5287660307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211904487/10000000000 : ℝ)|^4099 ≤ (13383455018237/100000000000000 : ℝ)^3075
        have hw : |(-2211904487/10000000000 : ℝ)|=(2211904487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387767433/10000000000 : ℝ)|^4099 ≤ (43849616668253/100000000000000 : ℝ)^3075
        have hw : |(5387767433/10000000000 : ℝ)|=(5387767433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_10 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057532193/2000000000 : ℝ)*x 0 + (2693883547/5000000000 : ℝ)*x 1 + (-34561001/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057532193/2000000000 : ℝ)^4099 ≤ (42766935390401/100000000000000 : ℝ)^3075 := by
    have hnat : (1057532193 : ℕ)^4099*100000000000000^3075 ≤ 42766935390401^3075*2000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057532193 2000000000 42766935390401 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693883547/5000000000 : ℝ)^4099 ≤ (21924806495221/50000000000000 : ℝ)^3075 := by
    have hnat : (2693883547 : ℕ)^4099*50000000000000^3075 ≤ 21924806495221^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693883547 5000000000 21924806495221 50000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34561001/156250000 : ℝ)^4099 ≤ (1672931450813/12500000000000 : ℝ)^3075 := by
    have hnat : (34561001 : ℕ)^4099*12500000000000^3075 ≤ 1672931450813^3075*156250000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34561001 156250000 1672931450813 12500000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057532193/2000000000 : ℝ), (2693883547/5000000000 : ℝ), (-34561001/156250000 : ℝ)] ![(42766935390401/100000000000000 : ℝ), (21924806495221/50000000000000 : ℝ), (1672931450813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057532193/2000000000 : ℝ)|^4099 ≤ (42766935390401/100000000000000 : ℝ)^3075
        have hw : |(1057532193/2000000000 : ℝ)|=(1057532193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693883547/5000000000 : ℝ)|^4099 ≤ (21924806495221/50000000000000 : ℝ)^3075
        have hw : |(2693883547/5000000000 : ℝ)|=(2693883547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34561001/156250000 : ℝ)|^4099 ≤ (1672931450813/12500000000000 : ℝ)^3075
        have hw : |(-34561001/156250000 : ℝ)|=(34561001/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_11 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2257167517/5000000000 : ℝ)*x 0 + (67522041/156250000 : ℝ)*x 1 + (4321410223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257167517/5000000000 : ℝ)^4099 ≤ (34639427876647/100000000000000 : ℝ)^3075 := by
    have hnat : (2257167517 : ℕ)^4099*100000000000000^3075 ≤ 34639427876647^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257167517 5000000000 34639427876647 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67522041/156250000 : ℝ)^4099 ≤ (32680288074231/100000000000000 : ℝ)^3075 := by
    have hnat : (67522041 : ℕ)^4099*100000000000000^3075 ≤ 32680288074231^3075*156250000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67522041 156250000 32680288074231 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4321410223/10000000000 : ℝ)^4099 ≤ (32680284031847/100000000000000 : ℝ)^3075 := by
    have hnat : (4321410223 : ℕ)^4099*100000000000000^3075 ≤ 32680284031847^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321410223 10000000000 32680284031847 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257167517/5000000000 : ℝ), (67522041/156250000 : ℝ), (4321410223/10000000000 : ℝ)] ![(34639427876647/100000000000000 : ℝ), (32680288074231/100000000000000 : ℝ), (32680284031847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257167517/5000000000 : ℝ)|^4099 ≤ (34639427876647/100000000000000 : ℝ)^3075
        have hw : |(2257167517/5000000000 : ℝ)|=(2257167517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67522041/156250000 : ℝ)|^4099 ≤ (32680288074231/100000000000000 : ℝ)^3075
        have hw : |(67522041/156250000 : ℝ)|=(67522041/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4321410223/10000000000 : ℝ)|^4099 ≤ (32680284031847/100000000000000 : ℝ)^3075
        have hw : |(4321410223/10000000000 : ℝ)|=(4321410223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_12 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158124889/10000000000 : ℝ)*x 0 + (1360970421/2500000000 : ℝ)*x 1 + (2635578377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158124889/10000000000 : ℝ)^4099 ≤ (12951457903073/100000000000000 : ℝ)^3075 := by
    have hnat : (2158124889 : ℕ)^4099*100000000000000^3075 ≤ 12951457903073^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158124889 10000000000 12951457903073 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360970421/2500000000 : ℝ)^4099 ≤ (44459453540551/100000000000000 : ℝ)^3075 := by
    have hnat : (1360970421 : ℕ)^4099*100000000000000^3075 ≤ 44459453540551^3075*2500000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360970421 2500000000 44459453540551 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635578377/5000000000 : ℝ)^4099 ≤ (42589088541527/100000000000000 : ℝ)^3075 := by
    have hnat : (2635578377 : ℕ)^4099*100000000000000^3075 ≤ 42589088541527^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635578377 5000000000 42589088541527 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158124889/10000000000 : ℝ), (1360970421/2500000000 : ℝ), (2635578377/5000000000 : ℝ)] ![(12951457903073/100000000000000 : ℝ), (44459453540551/100000000000000 : ℝ), (42589088541527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158124889/10000000000 : ℝ)|^4099 ≤ (12951457903073/100000000000000 : ℝ)^3075
        have hw : |(-2158124889/10000000000 : ℝ)|=(2158124889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360970421/2500000000 : ℝ)|^4099 ≤ (44459453540551/100000000000000 : ℝ)^3075
        have hw : |(1360970421/2500000000 : ℝ)|=(1360970421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635578377/5000000000 : ℝ)|^4099 ≤ (42589088541527/100000000000000 : ℝ)^3075
        have hw : |(2635578377/5000000000 : ℝ)|=(2635578377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_13 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370306041/10000000000 : ℝ)*x 0 + (-564318653/2500000000 : ℝ)*x 1 + (5271156421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370306041/10000000000 : ℝ)^4099 ≤ (21830140152593/50000000000000 : ℝ)^3075 := by
    have hnat : (5370306041 : ℕ)^4099*50000000000000^3075 ≤ 21830140152593^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370306041 10000000000 21830140152593 50000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564318653/2500000000 : ℝ)^4099 ≤ (1375063473391/10000000000000 : ℝ)^3075 := by
    have hnat : (564318653 : ℕ)^4099*10000000000000^3075 ≤ 1375063473391^3075*2500000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564318653 2500000000 1375063473391 10000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271156421/10000000000 : ℝ)^4099 ≤ (42589084955039/100000000000000 : ℝ)^3075 := by
    have hnat : (5271156421 : ℕ)^4099*100000000000000^3075 ≤ 42589084955039^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271156421 10000000000 42589084955039 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370306041/10000000000 : ℝ), (-564318653/2500000000 : ℝ), (5271156421/10000000000 : ℝ)] ![(21830140152593/50000000000000 : ℝ), (1375063473391/10000000000000 : ℝ), (42589084955039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370306041/10000000000 : ℝ)|^4099 ≤ (21830140152593/50000000000000 : ℝ)^3075
        have hw : |(5370306041/10000000000 : ℝ)|=(5370306041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-564318653/2500000000 : ℝ)|^4099 ≤ (1375063473391/10000000000000 : ℝ)^3075
        have hw : |(-564318653/2500000000 : ℝ)|=(564318653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271156421/10000000000 : ℝ)|^4099 ≤ (42589084955039/100000000000000 : ℝ)^3075
        have hw : |(5271156421/10000000000 : ℝ)|=(5271156421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_14 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370305749/10000000000 : ℝ)*x 0 + (2635578497/5000000000 : ℝ)*x 1 + (-3526991/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370305749/10000000000 : ℝ)^4099 ≤ (436602771407/1000000000000 : ℝ)^3075 := by
    have hnat : (5370305749 : ℕ)^4099*1000000000000^3075 ≤ 436602771407^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370305749 10000000000 436602771407 1000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635578497/5000000000 : ℝ)^4099 ≤ (2661818195399/6250000000000 : ℝ)^3075 := by
    have hnat : (2635578497 : ℕ)^4099*6250000000000^3075 ≤ 2661818195399^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635578497 5000000000 2661818195399 6250000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3526991/15625000 : ℝ)^4099 ≤ (2750126342633/20000000000000 : ℝ)^3075 := by
    have hnat : (3526991 : ℕ)^4099*20000000000000^3075 ≤ 2750126342633^3075*15625000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3526991 15625000 2750126342633 20000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370305749/10000000000 : ℝ), (2635578497/5000000000 : ℝ), (-3526991/15625000 : ℝ)] ![(436602771407/1000000000000 : ℝ), (2661818195399/6250000000000 : ℝ), (2750126342633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370305749/10000000000 : ℝ)|^4099 ≤ (436602771407/1000000000000 : ℝ)^3075
        have hw : |(5370305749/10000000000 : ℝ)|=(5370305749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635578497/5000000000 : ℝ)|^4099 ≤ (2661818195399/6250000000000 : ℝ)^3075
        have hw : |(2635578497/5000000000 : ℝ)|=(2635578497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3526991/15625000 : ℝ)|^4099 ≤ (2750126342633/20000000000000 : ℝ)^3075
        have hw : |(-3526991/15625000 : ℝ)|=(3526991/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1005_box_15 (p : ℝ) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425712433/1000000000 : ℝ)*x 0 + (4450013183/10000000000 : ℝ)*x 1 + (2225006289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425712433/1000000000 : ℝ)^4099 ≤ (32033844118977/100000000000000 : ℝ)^3075 := by
    have hnat : (425712433 : ℕ)^4099*100000000000000^3075 ≤ 32033844118977^3075*1000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425712433 1000000000 32033844118977 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4450013183/10000000000 : ℝ)^4099 ≤ (33983081011457/100000000000000 : ℝ)^3075 := by
    have hnat : (4450013183 : ℕ)^4099*100000000000000^3075 ≤ 33983081011457^3075*10000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450013183 10000000000 33983081011457 100000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225006289/5000000000 : ℝ)^4099 ≤ (8495768713187/25000000000000 : ℝ)^3075 := by
    have hnat : (2225006289 : ℕ)^4099*25000000000000^3075 ≤ 8495768713187^3075*5000000000^4099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225006289 5000000000 8495768713187 25000000000000 4099 3075 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4099/1024 : ℝ)) 4099 3075 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425712433/1000000000 : ℝ), (4450013183/10000000000 : ℝ), (2225006289/5000000000 : ℝ)] ![(32033844118977/100000000000000 : ℝ), (33983081011457/100000000000000 : ℝ), (8495768713187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425712433/1000000000 : ℝ)|^4099 ≤ (32033844118977/100000000000000 : ℝ)^3075
        have hw : |(425712433/1000000000 : ℝ)|=(425712433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4450013183/10000000000 : ℝ)|^4099 ≤ (33983081011457/100000000000000 : ℝ)^3075
        have hw : |(4450013183/10000000000 : ℝ)|=(4450013183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2225006289/5000000000 : ℝ)|^4099 ≤ (8495768713187/25000000000000 : ℝ)^3075
        have hw : |(2225006289/5000000000 : ℝ)|=(2225006289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1005_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5872313/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14799/25000 : ℝ) ∧ (39689/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20703/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2233/20000 : ℝ) ^ (8197/2048 : ℝ) ≤ (3864117773034309/25000000000000000000 : ℝ) := by
    have hpowers : (2233/20000 : ℝ)^8197 ≤ (3864117773034309/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2233 : ℕ)^8197*25000000000000000000^2048 ≤ 3864117773034309^2048*20000^8197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2233 20000 3864117773034309 25000000000000000000 8197 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2233/20000 : ℝ)) (X := (3864117773034309/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8197 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13963/100000 : ℝ) ^ (8197/2048 : ℝ) ≤ (37829229681914653/100000000000000000000 : ℝ) := by
    have hpowers : (13963/100000 : ℝ)^8197 ≤ (37829229681914653/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13963 : ℕ)^8197*100000000000000000000^2048 ≤ 37829229681914653^2048*100000^8197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13963 100000 37829229681914653 100000000000000000000 8197 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13963/100000 : ℝ)) (X := (37829229681914653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8197 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503864117773034309/12500000000000000000 : ℝ) ≤ (10000772262612419/10000000000000000 : ℝ) ^ (8197/2048 : ℝ) := by
    have hpowers : (12503864117773034309/12500000000000000000 : ℝ)^2048 ≤ (10000772262612419/10000000000000000 : ℝ)^8197 := by
      have hnat : (12503864117773034309 : ℕ)^2048*10000000000000000^8197 ≤ 10000772262612419^8197*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503864117773034309 12500000000000000000 10000772262612419 10000000000000000 2048 8197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000772262612419/10000000000000000 : ℝ)) (X := (12503864117773034309/12500000000000000000 : ℝ)) (by norm_num) 8197 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053285700774051889/100000000000000000000 : ℝ) ≤ (10001331063940453/10000000000000000 : ℝ) ^ (8197/2048 : ℝ) := by
    have hpowers : (100053285700774051889/100000000000000000000 : ℝ)^2048 ≤ (10001331063940453/10000000000000000 : ℝ)^8197 := by
      have hnat : (100053285700774051889 : ℕ)^2048*10000000000000000^8197 ≤ 10001331063940453^8197*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053285700774051889 100000000000000000000 10001331063940453 10000000000000000 2048 8197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001331063940453/10000000000000000 : ℝ)) (X := (100053285700774051889/100000000000000000000 : ℝ)) (by norm_num) 8197 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037829229681914653/50000000000000000000 : ℝ) ≤ (10001889865268487/10000000000000000 : ℝ) ^ (8197/2048 : ℝ) := by
    have hpowers : (50037829229681914653/50000000000000000000 : ℝ)^2048 ≤ (10001889865268487/10000000000000000 : ℝ)^8197 := by
      have hnat : (50037829229681914653 : ℕ)^2048*10000000000000000^8197 ≤ 10001889865268487^8197*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037829229681914653 50000000000000000000 10001889865268487 10000000000000000 2048 8197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001889865268487/10000000000000000 : ℝ)) (X := (50037829229681914653/50000000000000000000 : ℝ)) (by norm_num) 8197 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3864117773034309/25000000000000000000 : ℝ) ≤ ((13984841378567274571/13990000000000000000 : ℝ)+2*(279400664017/139900000000000 : ℝ)*(2233/20000 : ℝ))^(8197/2048 : ℝ) := by
    rw [show (13984841378567274571/13990000000000000000 : ℝ)+2*(279400664017/139900000000000 : ℝ)*(2233/20000 : ℝ)=(10000772262612419/10000000000000000 : ℝ) by norm_num, show 1+2*(3864117773034309/25000000000000000000 : ℝ)=(12503864117773034309/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37829229681914653/100000000000000000000 : ℝ)+(3864117773034309/25000000000000000000 : ℝ) ≤ ((13984841378567274571/13990000000000000000 : ℝ)+(279400664017/139900000000000 : ℝ)*((13963/100000 : ℝ)+(2233/20000 : ℝ)))^(8197/2048 : ℝ) := by
    rw [show (13984841378567274571/13990000000000000000 : ℝ)+(279400664017/139900000000000 : ℝ)*((13963/100000 : ℝ)+(2233/20000 : ℝ))=(10001331063940453/10000000000000000 : ℝ) by norm_num, show 1+(37829229681914653/100000000000000000000 : ℝ)+(3864117773034309/25000000000000000000 : ℝ)=(100053285700774051889/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37829229681914653/100000000000000000000 : ℝ) ≤ ((13984841378567274571/13990000000000000000 : ℝ)+2*(279400664017/139900000000000 : ℝ)*(13963/100000 : ℝ))^(8197/2048 : ℝ) := by
    rw [show (13984841378567274571/13990000000000000000 : ℝ)+2*(279400664017/139900000000000 : ℝ)*(13963/100000 : ℝ)=(10001889865268487/10000000000000000 : ℝ) by norm_num, show 1+2*(37829229681914653/100000000000000000000 : ℝ)=(50037829229681914653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13984841378567274571/13990000000000000000 : ℝ)*(X 1 0+X 2 0)+(279400664017/139900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8197/2048 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (13963/100000 : ℝ)) (c := (13984841378567274571/13990000000000000000 : ℝ)) (alpha := (279400664017/139900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13984841378567274571/13990000000000000000 : ℝ)*(X 0 1+X 2 1)+(279400664017/139900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8197/2048 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (13963/100000 : ℝ)) (c := (13984841378567274571/13990000000000000000 : ℝ)) (alpha := (279400664017/139900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13984841378567274571/13990000000000000000 : ℝ)*(X 0 2+X 1 2)+(279400664017/139900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8197/2048 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (13963/100000 : ℝ)) (c := (13984841378567274571/13990000000000000000 : ℝ)) (alpha := (279400664017/139900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1051276513/5000000000 : ℝ)*X 0 0+(2689088071/5000000000 : ℝ)*X 0 1+(2689088129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294462097/10000000000 : ℝ)*X 1 0+(-221570599/1000000000 : ℝ)*X 1 1+(537817671/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529446183/1000000000 : ℝ)*X 2 0+(5378176003/10000000000 : ℝ)*X 2 1+(-2215707297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((449344887/1000000000 : ℝ)*X 0 0+(2165996897/5000000000 : ℝ)*X 0 1+(2165997123/5000000000 : ℝ)*X 0 2+(449344887/1000000000 : ℝ)*X 1 0+(2165996897/5000000000 : ℝ)*X 1 1+(2165997123/5000000000 : ℝ)*X 1 2+(449344887/1000000000 : ℝ)*X 2 0+(2165996897/5000000000 : ℝ)*X 2 1+(2165997123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1183585913/5000000000 : ℝ)*X 0 0+(5279122797/10000000000 : ℝ)*X 0 1+(5279122693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335291439/625000000 : ℝ)*X 1 0+(-112711777/500000000 : ℝ)*X 1 1+(263956119/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682331257/5000000000 : ℝ)*X 2 0+(1055824597/2000000000 : ℝ)*X 2 1+(-2254235417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4274928179/10000000000 : ℝ)*X 0 0+(177649277/400000000 : ℝ)*X 0 1+(2220616403/5000000000 : ℝ)*X 0 2+(4274928179/10000000000 : ℝ)*X 1 0+(177649277/400000000 : ℝ)*X 1 1+(2220616403/5000000000 : ℝ)*X 1 2+(4274928179/10000000000 : ℝ)*X 2 0+(177649277/400000000 : ℝ)*X 2 1+(2220616403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-144500661/625000000 : ℝ)*X 0 0+(5212032263/10000000000 : ℝ)*X 0 1+(5387767067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5287660307/10000000000 : ℝ)*X 1 0+(-2211904487/10000000000 : ℝ)*X 1 1+(5387767433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057532193/2000000000 : ℝ)*X 2 0+(2693883547/5000000000 : ℝ)*X 2 1+(-34561001/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2257167517/5000000000 : ℝ)*X 0 0+(67522041/156250000 : ℝ)*X 0 1+(4321410223/10000000000 : ℝ)*X 0 2+(2257167517/5000000000 : ℝ)*X 1 0+(67522041/156250000 : ℝ)*X 1 1+(4321410223/10000000000 : ℝ)*X 1 2+(2257167517/5000000000 : ℝ)*X 2 0+(67522041/156250000 : ℝ)*X 2 1+(4321410223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2158124889/10000000000 : ℝ)*X 0 0+(1360970421/2500000000 : ℝ)*X 0 1+(2635578377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370306041/10000000000 : ℝ)*X 1 0+(-564318653/2500000000 : ℝ)*X 1 1+(5271156421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370305749/10000000000 : ℝ)*X 2 0+(2635578497/5000000000 : ℝ)*X 2 1+(-3526991/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((425712433/1000000000 : ℝ)*X 0 0+(4450013183/10000000000 : ℝ)*X 0 1+(2225006289/5000000000 : ℝ)*X 0 2+(425712433/1000000000 : ℝ)*X 1 0+(4450013183/10000000000 : ℝ)*X 1 1+(2225006289/5000000000 : ℝ)*X 1 2+(425712433/1000000000 : ℝ)*X 2 0+(4450013183/10000000000 : ℝ)*X 2 1+(2225006289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1005_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-108807887474465346420021333251961/174875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12436373/20000000000000 : ℝ)*(upper0) + (67875799/50000000000000 : ℝ)*(upper2) + (5219421/25000000000000 : ℝ)*(lower4) + (17304031/10000000000000 : ℝ)*(upper5) + (1902298622148697/50000000000000 : ℝ)*(major0) + (1902298622148697/50000000000000 : ℝ)*(major1) + (1902298622148697/50000000000000 : ℝ)*(major2) + (7960351597/50000000000000 : ℝ)*(sp1) + (325821487/20000000000000 : ℝ)*(sp2) + (8241899993/100000000000000 : ℝ)*(sp3) + (629798157277741/12500000000000 : ℝ)*(sp4) + (2519184668759367/50000000000000 : ℝ)*(sp5) + (5038383629114493/100000000000000 : ℝ)*(sp6) + (259154111474867/10000000000000 : ℝ)*(sp7) + (1295774678324331/50000000000000 : ℝ)*(f.failure) + (629798157277741/12500000000000 : ℝ)*(f.sum) + (4761577817129/3497500000000000000000000000 : ℝ)*base65 + (6151397859922216013/699500000000000000000000000000000 : ℝ)*base68 + (3503314771574783987/699500000000000000000000000000000 : ℝ)*base69 + (5810448430610783987/699500000000000000000000000000000 : ℝ)*base71 + (13340661879221/3497500000000000000000000000 : ℝ)*base74 + (1973461715652783987/699500000000000000000000000000000 : ℝ)*base75 + (2473139514019783987/699500000000000000000000000000000 : ℝ)*base77 + (3201818589924783987/699500000000000000000000000000000 : ℝ)*base79 + (8758096674923/1748750000000000000000000000 : ℝ)*base82 + (852397/200000000000000000000 : ℝ)*base90 + (852397/200000000000000000000 : ℝ)*base92 + (852397/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14799/25000 : ℝ) ≤ (1656372775130195750679181129953/2798000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1053/12500000000 : ℝ)*(lower0) + (244580921/50000000000000 : ℝ)*(upper2) + (69288657/100000000000000 : ℝ)*(lower4) + (76090753/25000000000000 : ℝ)*(lower5) + (15466016495519/400000000000 : ℝ)*(major0) + (15466016495519/400000000000 : ℝ)*(major1) + (15466016495519/400000000000 : ℝ)*(major2) + (2539761563593211/50000000000000 : ℝ)*(sp0) + (1269874297676333/25000000000000 : ℝ)*(sp1) + (1015911484315801/20000000000000 : ℝ)*(sp2) + (52674246618891/2000000000000 : ℝ)*(sp3) + (30115436837/50000000000000 : ℝ)*(sp5) + (5676852207/100000000000000 : ℝ)*(sp7) + (4286799073/12500000000000 : ℝ)*(sp12) + (1316859003898379/50000000000000 : ℝ)*(f.failure) + (1015911484315801/20000000000000 : ℝ)*(f.sum) + (733277511/279800000000000000000000000 : ℝ)*base65 + (51973462635332651/5596000000000000000000000000000 : ℝ)*base68 + (17380357437463349/5596000000000000000000000000000 : ℝ)*base69 + (11161971054620651/5596000000000000000000000000000 : ℝ)*base72 + (1810604152137/279800000000000000000000000 : ℝ)*base73 + (7408505763175349/5596000000000000000000000000000 : ℝ)*base75 + (60415078424459349/5596000000000000000000000000000 : ℝ)*base77 + (55862343575207349/5596000000000000000000000000000 : ℝ)*base79 + (838450734007/1399000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1680627/200000000000000000000 : ℝ)*base89 + (1680627/200000000000000000000 : ℝ)*base91 + (1680627/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (39689/50000 : ℝ) ≤ (13881652126838935711376884935051/17487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137038057/100000000000000 : ℝ)*(lower3) + (367939501/100000000000000 : ℝ)*(upper4) + (11170443/100000000000000 : ℝ)*(lower5) + (216739048172127/5000000000000 : ℝ)*(major0) + (216739048172127/5000000000000 : ℝ)*(major1) + (216739048172127/5000000000000 : ℝ)*(major2) + (1045236103/100000000000000 : ℝ)*(sp0) + (180544036861/50000000000000 : ℝ)*(sp1) + (351594943989/100000000000000 : ℝ)*(sp2) + (106278163123/50000000000000 : ℝ)*(sp3) + (1138082012267533/20000000000000 : ℝ)*(sp8) + (2845025009250023/50000000000000 : ℝ)*(sp9) + (5690059511629779/100000000000000 : ℝ)*(sp10) + (1476239060868547/50000000000000 : ℝ)*(sp11) + (2952690678063339/100000000000000 : ℝ)*(f.failure) + (711301388321721/12500000000000 : ℝ)*(f.sum) + (4878129165033/699500000000000000000000000 : ℝ)*base66 + (343336160249032517/69950000000000000000000000000000 : ℝ)*base67 + (786326198715667483/69950000000000000000000000000000 : ℝ)*base70 + (543429633827417483/69950000000000000000000000000000 : ℝ)*base72 + (3574382401117/699500000000000000000000000 : ℝ)*base73 + (867362952575217483/69950000000000000000000000000000 : ℝ)*base76 + (397634768884967483/69950000000000000000000000000000 : ℝ)*base78 + (394415834407367483/69950000000000000000000000000000 : ℝ)*base80 + (196977497803/55960000000000000000000000 : ℝ)*base82 + (433107/400000000000000000000 : ℝ)*base89 + (433107/400000000000000000000 : ℝ)*base91 + (433107/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-20703/25000 : ℝ) ≤ (-72406579607579451397425875352921/87437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150009563/50000000000000 : ℝ)*(lower0) + (4198639/50000000000000 : ℝ)*(upper1) + (49370339/100000000000000 : ℝ)*(upper3) + (60415207/20000000000000 : ℝ)*(upper5) + (1092236251132117/25000000000000 : ℝ)*(major0) + (1092236251132117/25000000000000 : ℝ)*(major1) + (1092236251132117/25000000000000 : ℝ)*(major2) + (95737641/1562500000000 : ℝ)*(sp4) + (149790717163/50000000000000 : ℝ)*(sp5) + (31585118169/50000000000000 : ℝ)*(sp7) + (5789525112132153/100000000000000 : ℝ)*(sp12) + (5789231657906851/100000000000000 : ℝ)*(sp13) + (723691404917647/12500000000000 : ℝ)*(sp14) + (743974693732853/25000000000000 : ℝ)*(sp15) + (11903847780671/400000000000 : ℝ)*(f.failure) + (723691404917647/12500000000000 : ℝ)*(f.sum) + (14622920432061/6995000000000000000000000000 : ℝ)*base65 + (11670928675440896807/349750000000000000000000000000000 : ℝ)*base67 + (11172117056576103193/349750000000000000000000000000000 : ℝ)*base70 + (3362732720178646807/349750000000000000000000000000000 : ℝ)*base71 + (157238885144463/3497500000000000000000000000 : ℝ)*base73 + (10870504854263146807/349750000000000000000000000000000 : ℝ)*base75 + (3527789500055896807/349750000000000000000000000000000 : ℝ)*base77 + (10503505437831896807/349750000000000000000000000000000 : ℝ)*base79 + (3234669755053/874375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (25977/1600000000000000000 : ℝ)*base90 + (25977/1600000000000000000 : ℝ)*base92 + (25977/1600000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1005_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5872313/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14799/25000 : ℝ) else (39689/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20703/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1005_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8197/2048 : ℝ) ≤ p) (hpb : p ≤ (4099/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5872313/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14799/25000 : ℝ) else (39689/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20703/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1005_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
