-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:09:07.225414+00:00
-- url     : https://prove2.me/submissions/5ebd3bd9-14e9-4e4c-82e6-50119d142504

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
theorem support_rectangle_w1069_s6_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101123291/5000000000 : ℝ)*x 0 + (337178337/625000000 : ℝ)*x 1 + (5263988707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101123291/5000000000 : ℝ)^4131 ≤ (13374845465447/100000000000000 : ℝ)^3107 := by
    have hnat : (1101123291 : ℕ)^4131*100000000000000^3107 ≤ 13374845465447^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101123291 5000000000 13374845465447 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337178337/625000000 : ℝ)^4131 ≤ (8803916831217/20000000000000 : ℝ)^3107 := by
    have hnat : (337178337 : ℕ)^4131*20000000000000^3107 ≤ 8803916831217^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337178337 625000000 8803916831217 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263988707/10000000000 : ℝ)^4131 ≤ (42605570364683/100000000000000 : ℝ)^3107 := by
    have hnat : (5263988707 : ℕ)^4131*100000000000000^3107 ≤ 42605570364683^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263988707 10000000000 42605570364683 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101123291/5000000000 : ℝ), (337178337/625000000 : ℝ), (5263988707/10000000000 : ℝ)] ![(13374845465447/100000000000000 : ℝ), (8803916831217/20000000000000 : ℝ), (42605570364683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101123291/5000000000 : ℝ)|^4131 ≤ (13374845465447/100000000000000 : ℝ)^3107
        have hw : |(-1101123291/5000000000 : ℝ)|=(1101123291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337178337/625000000 : ℝ)|^4131 ≤ (8803916831217/20000000000000 : ℝ)^3107
        have hw : |(337178337/625000000 : ℝ)|=(337178337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263988707/10000000000 : ℝ)|^4131 ≤ (42605570364683/100000000000000 : ℝ)^3107
        have hw : |(5263988707/10000000000 : ℝ)|=(5263988707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s6_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672554297/5000000000 : ℝ)*x 0 + (-2268649991/10000000000 : ℝ)*x 1 + (2631994393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672554297/5000000000 : ℝ)^4131 ≤ (43480736338193/100000000000000 : ℝ)^3107 := by
    have hnat : (2672554297 : ℕ)^4131*100000000000000^3107 ≤ 43480736338193^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672554297 5000000000 43480736338193 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2268649991/10000000000 : ℝ)^4131 ≤ (6956846216243/50000000000000 : ℝ)^3107 := by
    have hnat : (2268649991 : ℕ)^4131*50000000000000^3107 ≤ 6956846216243^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268649991 10000000000 6956846216243 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631994393/5000000000 : ℝ)^4131 ≤ (42605571214827/100000000000000 : ℝ)^3107 := by
    have hnat : (2631994393 : ℕ)^4131*100000000000000^3107 ≤ 42605571214827^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631994393 5000000000 42605571214827 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672554297/5000000000 : ℝ), (-2268649991/10000000000 : ℝ), (2631994393/5000000000 : ℝ)] ![(43480736338193/100000000000000 : ℝ), (6956846216243/50000000000000 : ℝ), (42605571214827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672554297/5000000000 : ℝ)|^4131 ≤ (43480736338193/100000000000000 : ℝ)^3107
        have hw : |(2672554297/5000000000 : ℝ)|=(2672554297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2268649991/10000000000 : ℝ)|^4131 ≤ (6956846216243/50000000000000 : ℝ)^3107
        have hw : |(-2268649991/10000000000 : ℝ)|=(2268649991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631994393/5000000000 : ℝ)|^4131 ≤ (42605571214827/100000000000000 : ℝ)^3107
        have hw : |(2631994393/5000000000 : ℝ)|=(2631994393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s6_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334069263/625000000 : ℝ)*x 0 + (328999313/625000000 : ℝ)*x 1 + (-2268650211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334069263/625000000 : ℝ)^4131 ≤ (5435091520417/12500000000000 : ℝ)^3107 := by
    have hnat : (334069263 : ℕ)^4131*12500000000000^3107 ≤ 5435091520417^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334069263 625000000 5435091520417 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328999313/625000000 : ℝ)^4131 ≤ (42605573603839/100000000000000 : ℝ)^3107 := by
    have hnat : (328999313 : ℕ)^4131*100000000000000^3107 ≤ 42605573603839^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328999313 625000000 42605573603839 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2268650211/10000000000 : ℝ)^4131 ≤ (13913694226441/100000000000000 : ℝ)^3107 := by
    have hnat : (2268650211 : ℕ)^4131*100000000000000^3107 ≤ 13913694226441^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268650211 10000000000 13913694226441 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334069263/625000000 : ℝ), (328999313/625000000 : ℝ), (-2268650211/10000000000 : ℝ)] ![(5435091520417/12500000000000 : ℝ), (42605573603839/100000000000000 : ℝ), (13913694226441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334069263/625000000 : ℝ)|^4131 ≤ (5435091520417/12500000000000 : ℝ)^3107
        have hw : |(334069263/625000000 : ℝ)|=(334069263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328999313/625000000 : ℝ)|^4131 ≤ (42605573603839/100000000000000 : ℝ)^3107
        have hw : |(328999313/625000000 : ℝ)|=(328999313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2268650211/10000000000 : ℝ)|^4131 ≤ (13913694226441/100000000000000 : ℝ)^3107
        have hw : |(-2268650211/10000000000 : ℝ)|=(2268650211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s6_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2187516811/5000000000 : ℝ)*x 0 + (53107797/125000000 : ℝ)*x 1 + (2252626621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187516811/5000000000 : ℝ)^4131 ≤ (33316289540673/100000000000000 : ℝ)^3107 := by
    have hnat : (2187516811 : ℕ)^4131*100000000000000^3107 ≤ 33316289540673^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187516811 5000000000 33316289540673 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53107797/125000000 : ℝ)^4131 ≤ (16021270361733/50000000000000 : ℝ)^3107 := by
    have hnat : (53107797 : ℕ)^4131*50000000000000^3107 ≤ 16021270361733^3107*125000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53107797 125000000 16021270361733 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252626621/5000000000 : ℝ)^4131 ≤ (34641169721773/100000000000000 : ℝ)^3107 := by
    have hnat : (2252626621 : ℕ)^4131*100000000000000^3107 ≤ 34641169721773^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252626621 5000000000 34641169721773 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187516811/5000000000 : ℝ), (53107797/125000000 : ℝ), (2252626621/5000000000 : ℝ)] ![(33316289540673/100000000000000 : ℝ), (16021270361733/50000000000000 : ℝ), (34641169721773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187516811/5000000000 : ℝ)|^4131 ≤ (33316289540673/100000000000000 : ℝ)^3107
        have hw : |(2187516811/5000000000 : ℝ)|=(2187516811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53107797/125000000 : ℝ)|^4131 ≤ (16021270361733/50000000000000 : ℝ)^3107
        have hw : |(53107797/125000000 : ℝ)|=(53107797/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252626621/5000000000 : ℝ)|^4131 ≤ (34641169721773/100000000000000 : ℝ)^3107
        have hw : |(2252626621/5000000000 : ℝ)|=(2252626621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s6_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202251717/10000000000 : ℝ)*x 0 + (1052863857/2000000000 : ℝ)*x 1 + (5394521649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202251717/10000000000 : ℝ)^4131 ≤ (6687443465019/50000000000000 : ℝ)^3107 := by
    have hnat : (2202251717 : ℕ)^4131*50000000000000^3107 ≤ 6687443465019^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202251717 10000000000 6687443465019 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052863857/2000000000 : ℝ)^4131 ≤ (42609127855753/100000000000000 : ℝ)^3107 := by
    have hnat : (1052863857 : ℕ)^4131*100000000000000^3107 ≤ 42609127855753^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052863857 2000000000 42609127855753 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394521649/10000000000 : ℝ)^4131 ≤ (44015985191301/100000000000000 : ℝ)^3107 := by
    have hnat : (5394521649 : ℕ)^4131*100000000000000^3107 ≤ 44015985191301^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394521649 10000000000 44015985191301 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202251717/10000000000 : ℝ), (1052863857/2000000000 : ℝ), (5394521649/10000000000 : ℝ)] ![(6687443465019/50000000000000 : ℝ), (42609127855753/100000000000000 : ℝ), (44015985191301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202251717/10000000000 : ℝ)|^4131 ≤ (6687443465019/50000000000000 : ℝ)^3107
        have hw : |(-2202251717/10000000000 : ℝ)|=(2202251717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052863857/2000000000 : ℝ)|^4131 ≤ (42609127855753/100000000000000 : ℝ)^3107
        have hw : |(1052863857/2000000000 : ℝ)|=(1052863857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394521649/10000000000 : ℝ)|^4131 ≤ (44015985191301/100000000000000 : ℝ)^3107
        have hw : |(5394521649/10000000000 : ℝ)|=(5394521649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s6_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656069271/5000000000 : ℝ)*x 0 + (-133632329/625000000 : ℝ)*x 1 + (1348630413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656069271/5000000000 : ℝ)^4131 ≤ (8624901077273/20000000000000 : ℝ)^3107 := by
    have hnat : (2656069271 : ℕ)^4131*20000000000000^3107 ≤ 8624901077273^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656069271 5000000000 8624901077273 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133632329/625000000 : ℝ)^4131 ≤ (3214877346131/25000000000000 : ℝ)^3107 := by
    have hnat : (133632329 : ℕ)^4131*25000000000000^3107 ≤ 3214877346131^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133632329 625000000 3214877346131 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348630413/2500000000 : ℝ)^4131 ≤ (22007992611923/50000000000000 : ℝ)^3107 := by
    have hnat : (1348630413 : ℕ)^4131*50000000000000^3107 ≤ 22007992611923^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348630413 2500000000 22007992611923 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656069271/5000000000 : ℝ), (-133632329/625000000 : ℝ), (1348630413/2500000000 : ℝ)] ![(8624901077273/20000000000000 : ℝ), (3214877346131/25000000000000 : ℝ), (22007992611923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656069271/5000000000 : ℝ)|^4131 ≤ (8624901077273/20000000000000 : ℝ)^3107
        have hw : |(2656069271/5000000000 : ℝ)|=(2656069271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133632329/625000000 : ℝ)|^4131 ≤ (3214877346131/25000000000000 : ℝ)^3107
        have hw : |(-133632329/625000000 : ℝ)|=(133632329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348630413/2500000000 : ℝ)|^4131 ≤ (22007992611923/50000000000000 : ℝ)^3107
        have hw : |(1348630413/2500000000 : ℝ)|=(1348630413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s6_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312138399/10000000000 : ℝ)*x 0 + (5394521847/10000000000 : ℝ)*x 1 + (-267264649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312138399/10000000000 : ℝ)^4131 ≤ (5390562980359/12500000000000 : ℝ)^3107 := by
    have hnat : (5312138399 : ℕ)^4131*12500000000000^3107 ≤ 5390562980359^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312138399 10000000000 5390562980359 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394521847/10000000000 : ℝ)^4131 ≤ (2750999208707/6250000000000 : ℝ)^3107 := by
    have hnat : (5394521847 : ℕ)^4131*6250000000000^3107 ≤ 2750999208707^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394521847 10000000000 2750999208707 6250000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267264649/1250000000 : ℝ)^4131 ≤ (12859508808767/100000000000000 : ℝ)^3107 := by
    have hnat : (267264649 : ℕ)^4131*100000000000000^3107 ≤ 12859508808767^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267264649 1250000000 12859508808767 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312138399/10000000000 : ℝ), (5394521847/10000000000 : ℝ), (-267264649/1250000000 : ℝ)] ![(5390562980359/12500000000000 : ℝ), (2750999208707/6250000000000 : ℝ), (12859508808767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312138399/10000000000 : ℝ)|^4131 ≤ (5390562980359/12500000000000 : ℝ)^3107
        have hw : |(5312138399/10000000000 : ℝ)|=(5312138399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394521847/10000000000 : ℝ)|^4131 ≤ (2750999208707/6250000000000 : ℝ)^3107
        have hw : |(5394521847/10000000000 : ℝ)|=(5394521847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267264649/1250000000 : ℝ)|^4131 ≤ (12859508808767/100000000000000 : ℝ)^3107
        have hw : |(-267264649/1250000000 : ℝ)|=(267264649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s6_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375043777/10000000000 : ℝ)*x 0 + (180184199/400000000 : ℝ)*x 1 + (2124637197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375043777/10000000000 : ℝ)^4131 ≤ (33316392358701/100000000000000 : ℝ)^3107 := by
    have hnat : (4375043777 : ℕ)^4131*100000000000000^3107 ≤ 33316392358701^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375043777 10000000000 33316392358701 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180184199/400000000 : ℝ)^4131 ≤ (8658635627311/25000000000000 : ℝ)^3107 := by
    have hnat : (180184199 : ℕ)^4131*25000000000000^3107 ≤ 8658635627311^3107*400000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180184199 400000000 8658635627311 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124637197/5000000000 : ℝ)^4131 ≤ (8012266279919/25000000000000 : ℝ)^3107 := by
    have hnat : (2124637197 : ℕ)^4131*25000000000000^3107 ≤ 8012266279919^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124637197 5000000000 8012266279919 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375043777/10000000000 : ℝ), (180184199/400000000 : ℝ), (2124637197/5000000000 : ℝ)] ![(33316392358701/100000000000000 : ℝ), (8658635627311/25000000000000 : ℝ), (8012266279919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375043777/10000000000 : ℝ)|^4131 ≤ (33316392358701/100000000000000 : ℝ)^3107
        have hw : |(4375043777/10000000000 : ℝ)|=(4375043777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180184199/400000000 : ℝ)|^4131 ≤ (8658635627311/25000000000000 : ℝ)^3107
        have hw : |(180184199/400000000 : ℝ)|=(180184199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124637197/5000000000 : ℝ)|^4131 ≤ (8012266279919/25000000000000 : ℝ)^3107
        have hw : |(2124637197/5000000000 : ℝ)|=(2124637197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2249/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (438/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11203/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (7316073924853347/50000000000000000000 : ℝ) := by
    have hpowers : (11203/100000 : ℝ)^8261 ≤ (7316073924853347/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11203 : ℕ)^8261*50000000000000000000^2048 ≤ 7316073924853347^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11203 100000 7316073924853347 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11203/100000 : ℝ)) (X := (7316073924853347/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14059/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (7313766753947919/20000000000000000000 : ℝ) := by
    have hpowers : (14059/100000 : ℝ)^8261 ≤ (7313766753947919/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14059 : ℕ)^8261*20000000000000000000^2048 ≤ 7313766753947919^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14059 100000 7313766753947919 20000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14059/100000 : ℝ)) (X := (7313766753947919/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007316073924853347/25000000000000000000 : ℝ) ≤ (2500181354204283/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25007316073924853347/25000000000000000000 : ℝ)^2048 ≤ (2500181354204283/2500000000000000 : ℝ)^8261 := by
      have hnat : (25007316073924853347 : ℕ)^2048*2500000000000000^8261 ≤ 2500181354204283^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007316073924853347 25000000000000000000 2500181354204283 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500181354204283/2500000000000000 : ℝ)) (X := (25007316073924853347/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051200981619446289/100000000000000000000 : ℝ) ≤ (10001269088813773/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (100051200981619446289/100000000000000000000 : ℝ)^2048 ≤ (10001269088813773/10000000000000000 : ℝ)^8261 := by
      have hnat : (100051200981619446289 : ℕ)^2048*10000000000000000^8261 ≤ 10001269088813773^8261*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051200981619446289 100000000000000000000 10001269088813773 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001269088813773/10000000000000000 : ℝ)) (X := (100051200981619446289/100000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007313766753947919/10000000000000000000 : ℝ) ≤ (5000906380405207/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (10007313766753947919/10000000000000000000 : ℝ)^2048 ≤ (5000906380405207/5000000000000000 : ℝ)^8261 := by
      have hnat : (10007313766753947919 : ℕ)^2048*5000000000000000^8261 ≤ 5000906380405207^8261*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007313766753947919 10000000000000000000 5000906380405207 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000906380405207/5000000000000000 : ℝ)) (X := (10007313766753947919/10000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7316073924853347/50000000000000000000 : ℝ) ≤ ((839702655166852669/840000000000000000 : ℝ)+2*(543671996641/285600000000000 : ℝ)*(11203/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (839702655166852669/840000000000000000 : ℝ)+2*(543671996641/285600000000000 : ℝ)*(11203/100000 : ℝ)=(2500181354204283/2500000000000000 : ℝ) by norm_num, show 1+2*(7316073924853347/50000000000000000000 : ℝ)=(25007316073924853347/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7313766753947919/20000000000000000000 : ℝ)+(7316073924853347/50000000000000000000 : ℝ) ≤ ((839702655166852669/840000000000000000 : ℝ)+(543671996641/285600000000000 : ℝ)*((14059/100000 : ℝ)+(11203/100000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (839702655166852669/840000000000000000 : ℝ)+(543671996641/285600000000000 : ℝ)*((14059/100000 : ℝ)+(11203/100000 : ℝ))=(10001269088813773/10000000000000000 : ℝ) by norm_num, show 1+(7313766753947919/20000000000000000000 : ℝ)+(7316073924853347/50000000000000000000 : ℝ)=(100051200981619446289/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7313766753947919/20000000000000000000 : ℝ) ≤ ((839702655166852669/840000000000000000 : ℝ)+2*(543671996641/285600000000000 : ℝ)*(14059/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (839702655166852669/840000000000000000 : ℝ)+2*(543671996641/285600000000000 : ℝ)*(14059/100000 : ℝ)=(5000906380405207/5000000000000000 : ℝ) by norm_num, show 1+2*(7313766753947919/20000000000000000000 : ℝ)=(10007313766753947919/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (839702655166852669/840000000000000000 : ℝ)*(X 1 0+X 2 0)+(543671996641/285600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (839702655166852669/840000000000000000 : ℝ)) (alpha := (543671996641/285600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (839702655166852669/840000000000000000 : ℝ)*(X 0 1+X 2 1)+(543671996641/285600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (839702655166852669/840000000000000000 : ℝ)) (alpha := (543671996641/285600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (839702655166852669/840000000000000000 : ℝ)*(X 0 2+X 1 2)+(543671996641/285600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (839702655166852669/840000000000000000 : ℝ)) (alpha := (543671996641/285600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1101123291/5000000000 : ℝ)*X 0 0+(337178337/625000000 : ℝ)*X 0 1+(5263988707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672554297/5000000000 : ℝ)*X 1 0+(-2268649991/10000000000 : ℝ)*X 1 1+(2631994393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334069263/625000000 : ℝ)*X 2 0+(328999313/625000000 : ℝ)*X 2 1+(-2268650211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187516811/5000000000 : ℝ)*X 0 0+(53107797/125000000 : ℝ)*X 0 1+(2252626621/5000000000 : ℝ)*X 0 2+(2187516811/5000000000 : ℝ)*X 1 0+(53107797/125000000 : ℝ)*X 1 1+(2252626621/5000000000 : ℝ)*X 1 2+(2187516811/5000000000 : ℝ)*X 2 0+(53107797/125000000 : ℝ)*X 2 1+(2252626621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2202251717/10000000000 : ℝ)*X 0 0+(1052863857/2000000000 : ℝ)*X 0 1+(5394521649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656069271/5000000000 : ℝ)*X 1 0+(-133632329/625000000 : ℝ)*X 1 1+(1348630413/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312138399/10000000000 : ℝ)*X 2 0+(5394521847/10000000000 : ℝ)*X 2 1+(-267264649/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375043777/10000000000 : ℝ)*X 0 0+(180184199/400000000 : ℝ)*X 0 1+(2124637197/5000000000 : ℝ)*X 0 2+(4375043777/10000000000 : ℝ)*X 1 0+(180184199/400000000 : ℝ)*X 1 1+(2124637197/5000000000 : ℝ)*X 1 2+(4375043777/10000000000 : ℝ)*X 2 0+(180184199/400000000 : ℝ)*X 2 1+(2124637197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (458891154971876593257/280000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79525911/12500000000000 : ℝ)*(base19) + (163992839/100000000000000 : ℝ)*(base23) + (67393599/100000000000000 : ℝ)*(upper2) + (33062139/20000000000000 : ℝ)*(upper3) + (5769110745379197/100000000000000 : ℝ)*(major0) + (5769110745379197/100000000000000 : ℝ)*(major1) + (5769110745379197/100000000000000 : ℝ)*(major2) + (7641511955906427/100000000000000 : ℝ)*(sp0) + (3820763181546821/50000000000000 : ℝ)*(sp1) + (1528303860567253/20000000000000 : ℝ)*(sp2) + (3896681625763103/100000000000000 : ℝ)*(sp3) + (1880424313/12500000000000 : ℝ)*(sp4) + (7532471827/100000000000000 : ℝ)*(sp6) + (256221289/2000000000000 : ℝ)*(sp7) + (1948347218413777/50000000000000 : ℝ)*(f.failure) + (764152699930093/10000000000000 : ℝ)*(f.sum) + (2265770097407/280000000000000000000000000 : ℝ)*base65 + (95320281820141069/28000000000000000000000000000000 : ℝ)*base68 + (206748361783858931/28000000000000000000000000000000 : ℝ)*base69 + (305530562100141069/28000000000000000000000000000000 : ℝ)*base72 + (1100472264687/280000000000000000000000000 : ℝ)*base73 + (604248636227858931/28000000000000000000000000000000 : ℝ)*base75 + (1265753039858931/28000000000000000000000000000000 : ℝ)*base77 + (191682829640141069/28000000000000000000000000000000 : ℝ)*base80 + (1007774703367/280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (25482677/2500000000000000000000 : ℝ)*base89 + (25482677/2500000000000000000000 : ℝ)*base91 + (25482677/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14618281062313373011/5440000000000000000000000 : ℝ) := by norm_num
    linear_combination (154534873/25000000000000 : ℝ)*(base19) + (496248099/100000000000000 : ℝ)*(base23) + (2676951/10000000000000 : ℝ)*(upper2) + (6093823/6250000000000 : ℝ)*(upper3) + (3369533/5000000000000 : ℝ)*(upper5) + (46387356175307/800000000000 : ℝ)*(major0) + (46387356175307/800000000000 : ℝ)*(major1) + (46387356175307/800000000000 : ℝ)*(major2) + (14516324111/100000000000000 : ℝ)*(sp1) + (10034856421/50000000000000 : ℝ)*(sp2) + (7680348165525459/100000000000000 : ℝ)*(sp4) + (1536066606212371/20000000000000 : ℝ)*(sp5) + (3840163799782259/50000000000000 : ℝ)*(sp6) + (3916490788728481/100000000000000 : ℝ)*(sp7) + (3916490788728481/100000000000000 : ℝ)*(f.failure) + (7680348165525459/100000000000000 : ℝ)*(f.sum) + (344111662853/408000000000000000000000000 : ℝ)*base65 + (7126717515607927/1632000000000000000000000000000 : ℝ)*base68 + (18878863656712073/1632000000000000000000000000000 : ℝ)*base69 + (282614233480073/1632000000000000000000000000000 : ℝ)*base71 + (1689542150107/408000000000000000000000000 : ℝ)*base74 + (6511860585367927/1632000000000000000000000000000 : ℝ)*base76 + (10734091603912073/1632000000000000000000000000000 : ℝ)*base77 + (3975796620151927/1632000000000000000000000000000 : ℝ)*base80 + (1764619655957/408000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (45309819/5000000000000000000000 : ℝ)*base90 + (45309819/5000000000000000000000 : ℝ)*base92 + (45309819/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1069_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1069_s7_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202283241/10000000000 : ℝ)*x 0 + (2697197087/5000000000 : ℝ)*x 1 + (5264424137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202283241/10000000000 : ℝ)^4131 ≤ (13375141483757/100000000000000 : ℝ)^3107 := by
    have hnat : (2202283241 : ℕ)^4131*100000000000000^3107 ≤ 13375141483757^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202283241 10000000000 13375141483757 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697197087/5000000000 : ℝ)^4131 ≤ (1375456321207/3125000000000 : ℝ)^3107 := by
    have hnat : (2697197087 : ℕ)^4131*3125000000000^3107 ≤ 1375456321207^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697197087 5000000000 1375456321207 3125000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264424137/10000000000 : ℝ)^4131 ≤ (21305128114147/50000000000000 : ℝ)^3107 := by
    have hnat : (5264424137 : ℕ)^4131*50000000000000^3107 ≤ 21305128114147^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264424137 10000000000 21305128114147 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202283241/10000000000 : ℝ), (2697197087/5000000000 : ℝ), (5264424137/10000000000 : ℝ)] ![(13375141483757/100000000000000 : ℝ), (1375456321207/3125000000000 : ℝ), (21305128114147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202283241/10000000000 : ℝ)|^4131 ≤ (13375141483757/100000000000000 : ℝ)^3107
        have hw : |(-2202283241/10000000000 : ℝ)|=(2202283241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697197087/5000000000 : ℝ)|^4131 ≤ (1375456321207/3125000000000 : ℝ)^3107
        have hw : |(2697197087/5000000000 : ℝ)|=(2697197087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264424137/10000000000 : ℝ)|^4131 ≤ (21305128114147/50000000000000 : ℝ)^3107
        have hw : |(5264424137/10000000000 : ℝ)|=(5264424137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s7_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344994499/10000000000 : ℝ)*x 0 + (-1134113693/5000000000 : ℝ)*x 1 + (1316105917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344994499/10000000000 : ℝ)^4131 ≤ (4347950232619/10000000000000 : ℝ)^3107 := by
    have hnat : (5344994499 : ℕ)^4131*10000000000000^3107 ≤ 4347950232619^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344994499 10000000000 4347950232619 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134113693/5000000000 : ℝ)^4131 ≤ (13910246473203/100000000000000 : ℝ)^3107 := by
    have hnat : (1134113693 : ℕ)^4131*100000000000000^3107 ≤ 13910246473203^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134113693 5000000000 13910246473203 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316105917/2500000000 : ℝ)^4131 ≤ (426102511811/1000000000000 : ℝ)^3107 := by
    have hnat : (1316105917 : ℕ)^4131*1000000000000^3107 ≤ 426102511811^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316105917 2500000000 426102511811 1000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344994499/10000000000 : ℝ), (-1134113693/5000000000 : ℝ), (1316105917/2500000000 : ℝ)] ![(4347950232619/10000000000000 : ℝ), (13910246473203/100000000000000 : ℝ), (426102511811/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344994499/10000000000 : ℝ)|^4131 ≤ (4347950232619/10000000000000 : ℝ)^3107
        have hw : |(5344994499/10000000000 : ℝ)|=(5344994499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1134113693/5000000000 : ℝ)|^4131 ≤ (13910246473203/100000000000000 : ℝ)^3107
        have hw : |(-1134113693/5000000000 : ℝ)|=(1134113693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316105917/2500000000 : ℝ)|^4131 ≤ (426102511811/1000000000000 : ℝ)^3107
        have hw : |(1316105917/2500000000 : ℝ)|=(1316105917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s7_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344994399/10000000000 : ℝ)*x 0 + (2632212051/5000000000 : ℝ)*x 1 + (-1134113473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344994399/10000000000 : ℝ)^4131 ≤ (43479501244629/100000000000000 : ℝ)^3107 := by
    have hnat : (5344994399 : ℕ)^4131*100000000000000^3107 ≤ 43479501244629^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344994399 10000000000 43479501244629 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632212051/5000000000 : ℝ)^4131 ≤ (21305127925819/50000000000000 : ℝ)^3107 := by
    have hnat : (2632212051 : ℕ)^4131*50000000000000^3107 ≤ 21305127925819^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632212051 5000000000 21305127925819 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134113473/5000000000 : ℝ)^4131 ≤ (6955121442757/50000000000000 : ℝ)^3107 := by
    have hnat : (1134113473 : ℕ)^4131*50000000000000^3107 ≤ 6955121442757^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134113473 5000000000 6955121442757 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344994399/10000000000 : ℝ), (2632212051/5000000000 : ℝ), (-1134113473/5000000000 : ℝ)] ![(43479501244629/100000000000000 : ℝ), (21305127925819/50000000000000 : ℝ), (6955121442757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344994399/10000000000 : ℝ)|^4131 ≤ (43479501244629/100000000000000 : ℝ)^3107
        have hw : |(5344994399/10000000000 : ℝ)|=(5344994399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632212051/5000000000 : ℝ)|^4131 ≤ (21305127925819/50000000000000 : ℝ)^3107
        have hw : |(2632212051/5000000000 : ℝ)|=(2632212051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134113473/5000000000 : ℝ)|^4131 ≤ (6955121442757/50000000000000 : ℝ)^3107
        have hw : |(-1134113473/5000000000 : ℝ)|=(1134113473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s7_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2187528491/5000000000 : ℝ)*x 0 + (4249496651/10000000000 : ℝ)*x 1 + (1126093467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187528491/5000000000 : ℝ)^4131 ≤ (8329131514423/25000000000000 : ℝ)^3107 := by
    have hnat : (2187528491 : ℕ)^4131*25000000000000^3107 ≤ 8329131514423^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187528491 5000000000 8329131514423 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249496651/10000000000 : ℝ)^4131 ≤ (16025646966569/50000000000000 : ℝ)^3107 := by
    have hnat : (4249496651 : ℕ)^4131*50000000000000^3107 ≤ 16025646966569^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249496651 10000000000 16025646966569 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126093467/2500000000 : ℝ)^4131 ≤ (17316089992937/50000000000000 : ℝ)^3107 := by
    have hnat : (1126093467 : ℕ)^4131*50000000000000^3107 ≤ 17316089992937^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126093467 2500000000 17316089992937 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187528491/5000000000 : ℝ), (4249496651/10000000000 : ℝ), (1126093467/2500000000 : ℝ)] ![(8329131514423/25000000000000 : ℝ), (16025646966569/50000000000000 : ℝ), (17316089992937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187528491/5000000000 : ℝ)|^4131 ≤ (8329131514423/25000000000000 : ℝ)^3107
        have hw : |(2187528491/5000000000 : ℝ)|=(2187528491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249496651/10000000000 : ℝ)|^4131 ≤ (16025646966569/50000000000000 : ℝ)^3107
        have hw : |(4249496651/10000000000 : ℝ)|=(4249496651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126093467/2500000000 : ℝ)|^4131 ≤ (17316089992937/50000000000000 : ℝ)^3107
        have hw : |(1126093467/2500000000 : ℝ)|=(1126093467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s7_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202288887/10000000000 : ℝ)*x 0 + (1316187411/2500000000 : ℝ)*x 1 + (5394067063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202288887/10000000000 : ℝ)^4131 ≤ (1671898384359/12500000000000 : ℝ)^3107 := by
    have hnat : (2202288887 : ℕ)^4131*12500000000000^3107 ≤ 1671898384359^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202288887 10000000000 1671898384359 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316187411/2500000000 : ℝ)^4131 ≤ (42613759243103/100000000000000 : ℝ)^3107 := by
    have hnat : (1316187411 : ℕ)^4131*100000000000000^3107 ≤ 42613759243103^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316187411 2500000000 42613759243103 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394067063/10000000000 : ℝ)^4131 ≤ (22005526831931/50000000000000 : ℝ)^3107 := by
    have hnat : (5394067063 : ℕ)^4131*50000000000000^3107 ≤ 22005526831931^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394067063 10000000000 22005526831931 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202288887/10000000000 : ℝ), (1316187411/2500000000 : ℝ), (5394067063/10000000000 : ℝ)] ![(1671898384359/12500000000000 : ℝ), (42613759243103/100000000000000 : ℝ), (22005526831931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202288887/10000000000 : ℝ)|^4131 ≤ (1671898384359/12500000000000 : ℝ)^3107
        have hw : |(-2202288887/10000000000 : ℝ)|=(2202288887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316187411/2500000000 : ℝ)|^4131 ≤ (42613759243103/100000000000000 : ℝ)^3107
        have hw : |(1316187411/2500000000 : ℝ)|=(1316187411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394067063/10000000000 : ℝ)|^4131 ≤ (22005526831931/50000000000000 : ℝ)^3107
        have hw : |(5394067063/10000000000 : ℝ)|=(5394067063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s7_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312250289/10000000000 : ℝ)*x 0 + (-427716701/2000000000 : ℝ)*x 1 + (2697033389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312250289/10000000000 : ℝ)^4131 ≤ (43125711549509/100000000000000 : ℝ)^3107 := by
    have hnat : (5312250289 : ℕ)^4131*100000000000000^3107 ≤ 43125711549509^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312250289 10000000000 43125711549509 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427716701/2000000000 : ℝ)^4131 ≤ (1286323787371/10000000000000 : ℝ)^3107 := by
    have hnat : (427716701 : ℕ)^4131*10000000000000^3107 ≤ 1286323787371^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427716701 2000000000 1286323787371 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697033389/5000000000 : ℝ)^4131 ≤ (44011050572113/100000000000000 : ℝ)^3107 := by
    have hnat : (2697033389 : ℕ)^4131*100000000000000^3107 ≤ 44011050572113^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697033389 5000000000 44011050572113 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312250289/10000000000 : ℝ), (-427716701/2000000000 : ℝ), (2697033389/5000000000 : ℝ)] ![(43125711549509/100000000000000 : ℝ), (1286323787371/10000000000000 : ℝ), (44011050572113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312250289/10000000000 : ℝ)|^4131 ≤ (43125711549509/100000000000000 : ℝ)^3107
        have hw : |(5312250289/10000000000 : ℝ)|=(5312250289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427716701/2000000000 : ℝ)|^4131 ≤ (1286323787371/10000000000000 : ℝ)^3107
        have hw : |(-427716701/2000000000 : ℝ)|=(427716701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697033389/5000000000 : ℝ)|^4131 ≤ (44011050572113/100000000000000 : ℝ)^3107
        have hw : |(2697033389/5000000000 : ℝ)|=(2697033389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s7_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328062527/2500000000 : ℝ)*x 0 + (2697033563/5000000000 : ℝ)*x 1 + (-85543331/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328062527/2500000000 : ℝ)^4131 ≤ (43125709595843/100000000000000 : ℝ)^3107 := by
    have hnat : (1328062527 : ℕ)^4131*100000000000000^3107 ≤ 43125709595843^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328062527 2500000000 43125709595843 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697033563/5000000000 : ℝ)^4131 ≤ (44011054347301/100000000000000 : ℝ)^3107 := by
    have hnat : (2697033563 : ℕ)^4131*100000000000000^3107 ≤ 44011054347301^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697033563 5000000000 44011054347301 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85543331/400000000 : ℝ)^4131 ≤ (12863236034353/100000000000000 : ℝ)^3107 := by
    have hnat : (85543331 : ℕ)^4131*100000000000000^3107 ≤ 12863236034353^3107*400000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85543331 400000000 12863236034353 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328062527/2500000000 : ℝ), (2697033563/5000000000 : ℝ), (-85543331/400000000 : ℝ)] ![(43125709595843/100000000000000 : ℝ), (44011054347301/100000000000000 : ℝ), (12863236034353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328062527/2500000000 : ℝ)|^4131 ≤ (43125709595843/100000000000000 : ℝ)^3107
        have hw : |(1328062527/2500000000 : ℝ)|=(1328062527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697033563/5000000000 : ℝ)|^4131 ≤ (44011054347301/100000000000000 : ℝ)^3107
        have hw : |(2697033563/5000000000 : ℝ)|=(2697033563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85543331/400000000 : ℝ)|^4131 ≤ (12863236034353/100000000000000 : ℝ)^3107
        have hw : |(-85543331/400000000 : ℝ)|=(85543331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s7_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375065751/10000000000 : ℝ)*x 0 + (4503735197/10000000000 : ℝ)*x 1 + (4250138817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375065751/10000000000 : ℝ)^4131 ≤ (6663322968561/20000000000000 : ℝ)^3107 := by
    have hnat : (4375065751 : ℕ)^4131*20000000000000^3107 ≤ 6663322968561^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375065751 10000000000 6663322968561 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503735197/10000000000 : ℝ)^4131 ≤ (1385026051629/4000000000000 : ℝ)^3107 := by
    have hnat : (4503735197 : ℕ)^4131*4000000000000^3107 ≤ 1385026051629^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503735197 10000000000 1385026051629 4000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250138817/10000000000 : ℝ)^4131 ≤ (32057733848203/100000000000000 : ℝ)^3107 := by
    have hnat : (4250138817 : ℕ)^4131*100000000000000^3107 ≤ 32057733848203^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250138817 10000000000 32057733848203 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375065751/10000000000 : ℝ), (4503735197/10000000000 : ℝ), (4250138817/10000000000 : ℝ)] ![(6663322968561/20000000000000 : ℝ), (1385026051629/4000000000000 : ℝ), (32057733848203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375065751/10000000000 : ℝ)|^4131 ≤ (6663322968561/20000000000000 : ℝ)^3107
        have hw : |(4375065751/10000000000 : ℝ)|=(4375065751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503735197/10000000000 : ℝ)|^4131 ≤ (1385026051629/4000000000000 : ℝ)^3107
        have hw : |(4503735197/10000000000 : ℝ)|=(4503735197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250138817/10000000000 : ℝ)|^4131 ≤ (32057733848203/100000000000000 : ℝ)^3107
        have hw : |(4250138817/10000000000 : ℝ)|=(4250138817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (438/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5627/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (438/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (438/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (438/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (438/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (438/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (438/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2249/20000 : ℝ) ^ (8261/2048 : ℝ) ≤ (3713670239800821/25000000000000000000 : ℝ) := by
    have hpowers : (2249/20000 : ℝ)^8261 ≤ (3713670239800821/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2249 : ℕ)^8261*25000000000000000000^2048 ≤ 3713670239800821^2048*20000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2249 20000 3713670239800821 25000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2249/20000 : ℝ)) (X := (3713670239800821/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (438/3125 : ℝ) ^ (8261/2048 : ℝ) ≤ (18059882696099137/50000000000000000000 : ℝ) := by
    have hpowers : (438/3125 : ℝ)^8261 ≤ (18059882696099137/50000000000000000000 : ℝ)^2048 := by
      have hnat : (438 : ℕ)^8261*50000000000000000000^2048 ≤ 18059882696099137^2048*3125^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        438 3125 18059882696099137 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (438/3125 : ℝ)) (X := (18059882696099137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503713670239800821/12500000000000000000 : ℝ) ≤ (5000368224045469/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (12503713670239800821/12500000000000000000 : ℝ)^2048 ≤ (5000368224045469/5000000000000000 : ℝ)^8261 := by
      have hnat : (12503713670239800821 : ℕ)^2048*5000000000000000^8261 ≤ 5000368224045469^8261*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503713670239800821 12500000000000000000 5000368224045469 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000368224045469/5000000000000000 : ℝ)) (X := (12503713670239800821/12500000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025487223175700779/50000000000000000000 : ℝ) ≤ (625078967180771/625000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50025487223175700779/50000000000000000000 : ℝ)^2048 ≤ (625078967180771/625000000000000 : ℝ)^8261 := by
      have hnat : (50025487223175700779 : ℕ)^2048*625000000000000^8261 ≤ 625078967180771^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025487223175700779 50000000000000000000 625078967180771 625000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625078967180771/625000000000000 : ℝ)) (X := (50025487223175700779/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018059882696099137/25000000000000000000 : ℝ) ≤ (5000895250846867/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25018059882696099137/25000000000000000000 : ℝ)^2048 ≤ (5000895250846867/5000000000000000 : ℝ)^8261 := by
      have hnat : (25018059882696099137 : ℕ)^2048*5000000000000000^8261 ≤ 5000895250846867^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018059882696099137 25000000000000000000 5000895250846867 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000895250846867/5000000000000000 : ℝ)) (X := (25018059882696099137/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3713670239800821/25000000000000000000 : ℝ) ≤ ((13850093932448274089/13855000000000000000 : ℝ)+2*(263513400699/138550000000000 : ℝ)*(2249/20000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (13850093932448274089/13855000000000000000 : ℝ)+2*(263513400699/138550000000000 : ℝ)*(2249/20000 : ℝ)=(5000368224045469/5000000000000000 : ℝ) by norm_num, show 1+2*(3713670239800821/25000000000000000000 : ℝ)=(12503713670239800821/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18059882696099137/50000000000000000000 : ℝ)+(3713670239800821/25000000000000000000 : ℝ) ≤ ((13850093932448274089/13855000000000000000 : ℝ)+(263513400699/138550000000000 : ℝ)*((438/3125 : ℝ)+(2249/20000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (13850093932448274089/13855000000000000000 : ℝ)+(263513400699/138550000000000 : ℝ)*((438/3125 : ℝ)+(2249/20000 : ℝ))=(625078967180771/625000000000000 : ℝ) by norm_num, show 1+(18059882696099137/50000000000000000000 : ℝ)+(3713670239800821/25000000000000000000 : ℝ)=(50025487223175700779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18059882696099137/50000000000000000000 : ℝ) ≤ ((13850093932448274089/13855000000000000000 : ℝ)+2*(263513400699/138550000000000 : ℝ)*(438/3125 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (13850093932448274089/13855000000000000000 : ℝ)+2*(263513400699/138550000000000 : ℝ)*(438/3125 : ℝ)=(5000895250846867/5000000000000000 : ℝ) by norm_num, show 1+2*(18059882696099137/50000000000000000000 : ℝ)=(25018059882696099137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13850093932448274089/13855000000000000000 : ℝ)*(X 1 0+X 2 0)+(263513400699/138550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (13850093932448274089/13855000000000000000 : ℝ)) (alpha := (263513400699/138550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13850093932448274089/13855000000000000000 : ℝ)*(X 0 1+X 2 1)+(263513400699/138550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (13850093932448274089/13855000000000000000 : ℝ)) (alpha := (263513400699/138550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13850093932448274089/13855000000000000000 : ℝ)*(X 0 2+X 1 2)+(263513400699/138550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (13850093932448274089/13855000000000000000 : ℝ)) (alpha := (263513400699/138550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2202283241/10000000000 : ℝ)*X 0 0+(2697197087/5000000000 : ℝ)*X 0 1+(5264424137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344994499/10000000000 : ℝ)*X 1 0+(-1134113693/5000000000 : ℝ)*X 1 1+(1316105917/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344994399/10000000000 : ℝ)*X 2 0+(2632212051/5000000000 : ℝ)*X 2 1+(-1134113473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187528491/5000000000 : ℝ)*X 0 0+(4249496651/10000000000 : ℝ)*X 0 1+(1126093467/2500000000 : ℝ)*X 0 2+(2187528491/5000000000 : ℝ)*X 1 0+(4249496651/10000000000 : ℝ)*X 1 1+(1126093467/2500000000 : ℝ)*X 1 2+(2187528491/5000000000 : ℝ)*X 2 0+(4249496651/10000000000 : ℝ)*X 2 1+(1126093467/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2202288887/10000000000 : ℝ)*X 0 0+(1316187411/2500000000 : ℝ)*X 0 1+(5394067063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312250289/10000000000 : ℝ)*X 1 0+(-427716701/2000000000 : ℝ)*X 1 1+(2697033389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328062527/2500000000 : ℝ)*X 2 0+(2697033563/5000000000 : ℝ)*X 2 1+(-85543331/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375065751/10000000000 : ℝ)*X 0 0+(4503735197/10000000000 : ℝ)*X 0 1+(4250138817/10000000000 : ℝ)*X 0 2+(4375065751/10000000000 : ℝ)*X 1 0+(4503735197/10000000000 : ℝ)*X 1 1+(4250138817/10000000000 : ℝ)*X 1 2+(4375065751/10000000000 : ℝ)*X 2 0+(4503735197/10000000000 : ℝ)*X 2 1+(4250138817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (574391050789038803460236013/86593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180475309/50000000000000 : ℝ)*(base19) + (135120847/50000000000000 : ℝ)*(lower2) + (131666177/100000000000000 : ℝ)*(lower4) + (149082471/50000000000000 : ℝ)*(upper5) + (726096809262387/12500000000000 : ℝ)*(major0) + (726096809262387/12500000000000 : ℝ)*(major1) + (726096809262387/12500000000000 : ℝ)*(major2) + (7694063778196799/100000000000000 : ℝ)*(sp0) + (38470243838733/500000000000 : ℝ)*(sp1) + (7694056027110737/100000000000000 : ℝ)*(sp2) + (98086847631471/2500000000000 : ℝ)*(sp3) + (7324749791/50000000000000 : ℝ)*(sp5) + (3875543031/50000000000000 : ℝ)*(sp6) + (11043636879/100000000000000 : ℝ)*(sp7) + (3923484948895719/100000000000000 : ℝ)*(f.failure) + (7694063778196799/100000000000000 : ℝ)*(f.sum) + (9849868264271/6927500000000000000000000000 : ℝ)*base66 + (650353527873252943/173187500000000000000000000000000 : ℝ)*base67 + (2222560269786565443/173187500000000000000000000000000 : ℝ)*base69 + (355629867770877943/173187500000000000000000000000000 : ℝ)*base71 + (73659226154307/13855000000000000000000000000 : ℝ)*base74 + (5224613500627627943/173187500000000000000000000000000 : ℝ)*base75 + (2505973639637690443/173187500000000000000000000000000 : ℝ)*base77 + (3011638324050752943/173187500000000000000000000000000 : ℝ)*base79 + (59593637331197/13855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25125981/5000000000000000000000 : ℝ)*base90 + (25125981/5000000000000000000000 : ℝ)*base92 + (25125981/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (804622441378974340271179173/138550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (479326853/25000000000000 : ℝ)*(base19) + (1456359273/50000000000000 : ℝ)*(base23) + (255253779/50000000000000 : ℝ)*(upper2) + (239927933/100000000000000 : ℝ)*(upper3) + (1167616486278319/20000000000000 : ℝ)*(major0) + (1167616486278319/20000000000000 : ℝ)*(major1) + (1167616486278319/20000000000000 : ℝ)*(major2) + (3261136403/10000000000000 : ℝ)*(sp1) + (80938760313/100000000000000 : ℝ)*(sp2) + (3307150507/100000000000000 : ℝ)*(sp3) + (1546576784350859/20000000000000 : ℝ)*(sp4) + (7732849393082853/100000000000000 : ℝ)*(sp5) + (7732800070275437/100000000000000 : ℝ)*(sp6) + (78865548805933/2000000000000 : ℝ)*(sp7) + (985820186861789/25000000000000 : ℝ)*(f.failure) + (1546576784350859/20000000000000 : ℝ)*(f.sum) + (5224436988827/2771000000000000000000000000 : ℝ)*base66 + (1269501634459423609/277100000000000000000000000000000 : ℝ)*base68 + (833162412969823609/277100000000000000000000000000000 : ℝ)*base70 + (2690222333450176391/277100000000000000000000000000000 : ℝ)*base71 + (114770675877/138550000000000000000000000 : ℝ)*base74 + (1893439589031723609/277100000000000000000000000000000 : ℝ)*base76 + (724248100498576391/277100000000000000000000000000000 : ℝ)*base77 + (5090302468376223609/277100000000000000000000000000000 : ℝ)*base80 + (5878684313299/2771000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16660911/1250000000000000000000 : ℝ)*base90 + (16660911/1250000000000000000000 : ℝ)*base92 + (16660911/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1069_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (438/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1069_s8_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220229043/1000000000 : ℝ)*x 0 + (2697149543/5000000000 : ℝ)*x 1 + (5264514597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220229043/1000000000 : ℝ)^4131 ≤ (835949970907/6250000000000 : ℝ)^3107 := by
    have hnat : (220229043 : ℕ)^4131*6250000000000^3107 ≤ 835949970907^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220229043 1000000000 835949970907 6250000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697149543/5000000000 : ℝ)^4131 ≤ (8802714144673/20000000000000 : ℝ)^3107 := by
    have hnat : (2697149543 : ℕ)^4131*20000000000000^3107 ≤ 8802714144673^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697149543 5000000000 8802714144673 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264514597/10000000000 : ℝ)^4131 ≤ (42611229726217/100000000000000 : ℝ)^3107 := by
    have hnat : (5264514597 : ℕ)^4131*100000000000000^3107 ≤ 42611229726217^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264514597 10000000000 42611229726217 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220229043/1000000000 : ℝ), (2697149543/5000000000 : ℝ), (5264514597/10000000000 : ℝ)] ![(835949970907/6250000000000 : ℝ), (8802714144673/20000000000000 : ℝ), (42611229726217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220229043/1000000000 : ℝ)|^4131 ≤ (835949970907/6250000000000 : ℝ)^3107
        have hw : |(-220229043/1000000000 : ℝ)|=(220229043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697149543/5000000000 : ℝ)|^4131 ≤ (8802714144673/20000000000000 : ℝ)^3107
        have hw : |(2697149543/5000000000 : ℝ)|=(2697149543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264514597/10000000000 : ℝ)|^4131 ≤ (42611229726217/100000000000000 : ℝ)^3107
        have hw : |(5264514597/10000000000 : ℝ)|=(5264514597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s8_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336242833/2500000000 : ℝ)*x 0 + (-1134069057/5000000000 : ℝ)*x 1 + (5264514591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336242833/2500000000 : ℝ)^4131 ≤ (43479251761003/100000000000000 : ℝ)^3107 := by
    have hnat : (1336242833 : ℕ)^4131*100000000000000^3107 ≤ 43479251761003^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336242833 2500000000 43479251761003 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134069057/5000000000 : ℝ)^4131 ≤ (13909518568333/100000000000000 : ℝ)^3107 := by
    have hnat : (1134069057 : ℕ)^4131*100000000000000^3107 ≤ 13909518568333^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134069057 5000000000 13909518568333 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264514591/10000000000 : ℝ)^4131 ≤ (42611229661647/100000000000000 : ℝ)^3107 := by
    have hnat : (5264514591 : ℕ)^4131*100000000000000^3107 ≤ 42611229661647^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264514591 10000000000 42611229661647 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336242833/2500000000 : ℝ), (-1134069057/5000000000 : ℝ), (5264514591/10000000000 : ℝ)] ![(43479251761003/100000000000000 : ℝ), (13909518568333/100000000000000 : ℝ), (42611229661647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336242833/2500000000 : ℝ)|^4131 ≤ (43479251761003/100000000000000 : ℝ)^3107
        have hw : |(1336242833/2500000000 : ℝ)|=(1336242833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1134069057/5000000000 : ℝ)|^4131 ≤ (13909518568333/100000000000000 : ℝ)^3107
        have hw : |(-1134069057/5000000000 : ℝ)|=(1134069057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264514591/10000000000 : ℝ)|^4131 ≤ (42611229661647/100000000000000 : ℝ)^3107
        have hw : |(5264514591/10000000000 : ℝ)|=(5264514591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s8_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344971339/10000000000 : ℝ)*x 0 + (658064323/1250000000 : ℝ)*x 1 + (-2268138113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344971339/10000000000 : ℝ)^4131 ≤ (5434906479589/12500000000000 : ℝ)^3107 := by
    have hnat : (5344971339 : ℕ)^4131*12500000000000^3107 ≤ 5434906479589^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344971339 10000000000 5434906479589 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658064323/1250000000 : ℝ)^4131 ≤ (8522245917263/20000000000000 : ℝ)^3107 := by
    have hnat : (658064323 : ℕ)^4131*20000000000000^3107 ≤ 8522245917263^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658064323 1250000000 8522245917263 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2268138113/10000000000 : ℝ)^4131 ≤ (13909518560179/100000000000000 : ℝ)^3107 := by
    have hnat : (2268138113 : ℕ)^4131*100000000000000^3107 ≤ 13909518560179^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268138113 10000000000 13909518560179 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344971339/10000000000 : ℝ), (658064323/1250000000 : ℝ), (-2268138113/10000000000 : ℝ)] ![(5434906479589/12500000000000 : ℝ), (8522245917263/20000000000000 : ℝ), (13909518560179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344971339/10000000000 : ℝ)|^4131 ≤ (5434906479589/12500000000000 : ℝ)^3107
        have hw : |(5344971339/10000000000 : ℝ)|=(5344971339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658064323/1250000000 : ℝ)|^4131 ≤ (8522245917263/20000000000000 : ℝ)^3107
        have hw : |(658064323/1250000000 : ℝ)|=(658064323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2268138113/10000000000 : ℝ)|^4131 ≤ (13909518560179/100000000000000 : ℝ)^3107
        have hw : |(-2268138113/10000000000 : ℝ)|=(2268138113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s8_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375061253/10000000000 : ℝ)*x 0 + (1062419843/2500000000 : ℝ)*x 1 + (450419039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375061253/10000000000 : ℝ)^4131 ≤ (16658284650533/50000000000000 : ℝ)^3107 := by
    have hnat : (4375061253 : ℕ)^4131*50000000000000^3107 ≤ 16658284650533^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375061253 10000000000 16658284650533 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062419843/2500000000 : ℝ)^4131 ≤ (32053126304763/100000000000000 : ℝ)^3107 := by
    have hnat : (1062419843 : ℕ)^4131*100000000000000^3107 ≤ 32053126304763^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062419843 2500000000 32053126304763 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450419039/1000000000 : ℝ)^4131 ≤ (8657576096253/25000000000000 : ℝ)^3107 := by
    have hnat : (450419039 : ℕ)^4131*25000000000000^3107 ≤ 8657576096253^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450419039 1000000000 8657576096253 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375061253/10000000000 : ℝ), (1062419843/2500000000 : ℝ), (450419039/1000000000 : ℝ)] ![(16658284650533/50000000000000 : ℝ), (32053126304763/100000000000000 : ℝ), (8657576096253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375061253/10000000000 : ℝ)|^4131 ≤ (16658284650533/50000000000000 : ℝ)^3107
        have hw : |(4375061253/10000000000 : ℝ)|=(4375061253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062419843/2500000000 : ℝ)|^4131 ≤ (32053126304763/100000000000000 : ℝ)^3107
        have hw : |(1062419843/2500000000 : ℝ)|=(1062419843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450419039/1000000000 : ℝ)|^4131 ≤ (8657576096253/25000000000000 : ℝ)^3107
        have hw : |(450419039/1000000000 : ℝ)|=(450419039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s8_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202295511/10000000000 : ℝ)*x 0 + (5264839607/10000000000 : ℝ)*x 1 + (2696986443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202295511/10000000000 : ℝ)^4131 ≤ (13375240563327/100000000000000 : ℝ)^3107 := by
    have hnat : (2202295511 : ℕ)^4131*100000000000000^3107 ≤ 13375240563327^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202295511 10000000000 13375240563327 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264839607/10000000000 : ℝ)^4131 ≤ (10653681853051/25000000000000 : ℝ)^3107 := by
    have hnat : (5264839607 : ℕ)^4131*25000000000000^3107 ≤ 10653681853051^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264839607 10000000000 10653681853051 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696986443/5000000000 : ℝ)^4131 ≤ (44010032011911/100000000000000 : ℝ)^3107 := by
    have hnat : (2696986443 : ℕ)^4131*100000000000000^3107 ≤ 44010032011911^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696986443 5000000000 44010032011911 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202295511/10000000000 : ℝ), (5264839607/10000000000 : ℝ), (2696986443/5000000000 : ℝ)] ![(13375240563327/100000000000000 : ℝ), (10653681853051/25000000000000 : ℝ), (44010032011911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202295511/10000000000 : ℝ)|^4131 ≤ (13375240563327/100000000000000 : ℝ)^3107
        have hw : |(-2202295511/10000000000 : ℝ)|=(2202295511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264839607/10000000000 : ℝ)|^4131 ≤ (10653681853051/25000000000000 : ℝ)^3107
        have hw : |(5264839607/10000000000 : ℝ)|=(5264839607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696986443/5000000000 : ℝ)|^4131 ≤ (44010032011911/100000000000000 : ℝ)^3107
        have hw : |(2696986443/5000000000 : ℝ)|=(2696986443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s8_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312273419/10000000000 : ℝ)*x 0 + (-1069339773/5000000000 : ℝ)*x 1 + (2696986481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312273419/10000000000 : ℝ)^4131 ≤ (43125961208741/100000000000000 : ℝ)^3107 := by
    have hnat : (5312273419 : ℕ)^4131*100000000000000^3107 ≤ 43125961208741^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312273419 10000000000 43125961208741 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069339773/5000000000 : ℝ)^4131 ≤ (12864005938607/100000000000000 : ℝ)^3107 := by
    have hnat : (1069339773 : ℕ)^4131*100000000000000^3107 ≤ 12864005938607^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069339773 5000000000 12864005938607 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696986481/5000000000 : ℝ)^4131 ≤ (44010032836373/100000000000000 : ℝ)^3107 := by
    have hnat : (2696986481 : ℕ)^4131*100000000000000^3107 ≤ 44010032836373^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696986481 5000000000 44010032836373 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312273419/10000000000 : ℝ), (-1069339773/5000000000 : ℝ), (2696986481/5000000000 : ℝ)] ![(43125961208741/100000000000000 : ℝ), (12864005938607/100000000000000 : ℝ), (44010032836373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312273419/10000000000 : ℝ)|^4131 ≤ (43125961208741/100000000000000 : ℝ)^3107
        have hw : |(5312273419/10000000000 : ℝ)|=(5312273419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069339773/5000000000 : ℝ)|^4131 ≤ (12864005938607/100000000000000 : ℝ)^3107
        have hw : |(-1069339773/5000000000 : ℝ)|=(1069339773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696986481/5000000000 : ℝ)|^4131 ≤ (44010032836373/100000000000000 : ℝ)^3107
        have hw : |(2696986481/5000000000 : ℝ)|=(2696986481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s8_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328068249/2500000000 : ℝ)*x 0 + (1078794589/2000000000 : ℝ)*x 1 + (-106934007/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328068249/2500000000 : ℝ)^4131 ≤ (21562978321493/50000000000000 : ℝ)^3107 := by
    have hnat : (1328068249 : ℕ)^4131*50000000000000^3107 ≤ 21562978321493^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328068249 2500000000 21562978321493 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078794589/2000000000 : ℝ)^4131 ≤ (22005016325977/50000000000000 : ℝ)^3107 := by
    have hnat : (1078794589 : ℕ)^4131*50000000000000^3107 ≤ 22005016325977^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078794589 2000000000 22005016325977 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106934007/500000000 : ℝ)^4131 ≤ (2572802137803/20000000000000 : ℝ)^3107 := by
    have hnat : (106934007 : ℕ)^4131*20000000000000^3107 ≤ 2572802137803^3107*500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106934007 500000000 2572802137803 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328068249/2500000000 : ℝ), (1078794589/2000000000 : ℝ), (-106934007/500000000 : ℝ)] ![(21562978321493/50000000000000 : ℝ), (22005016325977/50000000000000 : ℝ), (2572802137803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328068249/2500000000 : ℝ)|^4131 ≤ (21562978321493/50000000000000 : ℝ)^3107
        have hw : |(1328068249/2500000000 : ℝ)|=(1328068249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078794589/2000000000 : ℝ)|^4131 ≤ (22005016325977/50000000000000 : ℝ)^3107
        have hw : |(1078794589/2000000000 : ℝ)|=(1078794589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106934007/500000000 : ℝ)|^4131 ≤ (2572802137803/20000000000000 : ℝ)^3107
        have hw : |(-106934007/500000000 : ℝ)|=(106934007/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s8_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43750709/100000000 : ℝ)*x 0 + (4503552909/10000000000 : ℝ)*x 1 + (212515971/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43750709/100000000 : ℝ)^4131 ≤ (33316666975863/100000000000000 : ℝ)^3107 := by
    have hnat : (43750709 : ℕ)^4131*100000000000000^3107 ≤ 33316666975863^3107*100000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43750709 100000000 33316666975863 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503552909/10000000000 : ℝ)^4131 ≤ (34623787941623/100000000000000 : ℝ)^3107 := by
    have hnat : (4503552909 : ℕ)^4131*100000000000000^3107 ≤ 34623787941623^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503552909 10000000000 34623787941623 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212515971/500000000 : ℝ)^4131 ≤ (6411909014009/20000000000000 : ℝ)^3107 := by
    have hnat : (212515971 : ℕ)^4131*20000000000000^3107 ≤ 6411909014009^3107*500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212515971 500000000 6411909014009 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43750709/100000000 : ℝ), (4503552909/10000000000 : ℝ), (212515971/500000000 : ℝ)] ![(33316666975863/100000000000000 : ℝ), (34623787941623/100000000000000 : ℝ), (6411909014009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43750709/100000000 : ℝ)|^4131 ≤ (33316666975863/100000000000000 : ℝ)^3107
        have hw : |(43750709/100000000 : ℝ)|=(43750709/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503552909/10000000000 : ℝ)|^4131 ≤ (34623787941623/100000000000000 : ℝ)^3107
        have hw : |(4503552909/10000000000 : ℝ)|=(4503552909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212515971/500000000 : ℝ)|^4131 ≤ (6411909014009/20000000000000 : ℝ)^3107
        have hw : |(212515971/500000000 : ℝ)|=(212515971/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1407/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2801/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5627/50000 : ℝ) ^ (8261/2048 : ℝ) ≤ (7451347942095727/50000000000000000000 : ℝ) := by
    have hpowers : (5627/50000 : ℝ)^8261 ≤ (7451347942095727/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5627 : ℕ)^8261*50000000000000000000^2048 ≤ 7451347942095727^2048*50000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5627 50000 7451347942095727 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5627/50000 : ℝ)) (X := (7451347942095727/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14007/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (9006575422186329/25000000000000000000 : ℝ) := by
    have hpowers : (14007/100000 : ℝ)^8261 ≤ (9006575422186329/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14007 : ℕ)^8261*25000000000000000000^2048 ≤ 9006575422186329^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14007 100000 9006575422186329 25000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14007/100000 : ℝ)) (X := (9006575422186329/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007451347942095727/25000000000000000000 : ℝ) ≤ (1000073882825229/1000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25007451347942095727/25000000000000000000 : ℝ)^2048 ≤ (1000073882825229/1000000000000000 : ℝ)^8261 := by
      have hnat : (25007451347942095727 : ℕ)^2048*1000000000000000^8261 ≤ 1000073882825229^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007451347942095727 25000000000000000000 1000073882825229 1000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000073882825229/1000000000000000 : ℝ)) (X := (25007451347942095727/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005092899757293677/10000000000000000000 : ℝ) ≤ (10001262348594719/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (10005092899757293677/10000000000000000000 : ℝ)^2048 ≤ (10001262348594719/10000000000000000 : ℝ)^8261 := by
      have hnat : (10005092899757293677 : ℕ)^2048*10000000000000000^8261 ≤ 10001262348594719^8261*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005092899757293677 10000000000000000000 10001262348594719 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001262348594719/10000000000000000 : ℝ)) (X := (10005092899757293677/10000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509006575422186329/12500000000000000000 : ℝ) ≤ (2500446467234287/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (12509006575422186329/12500000000000000000 : ℝ)^2048 ≤ (2500446467234287/2500000000000000 : ℝ)^8261 := by
      have hnat : (12509006575422186329 : ℕ)^2048*2500000000000000^8261 ≤ 2500446467234287^8261*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509006575422186329 12500000000000000000 2500446467234287 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500446467234287/2500000000000000 : ℝ)) (X := (12509006575422186329/12500000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7451347942095727/50000000000000000000 : ℝ) ≤ ((13760125299155581219/13765000000000000000 : ℝ)+2*(523520342429/275300000000000 : ℝ)*(5627/50000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (13760125299155581219/13765000000000000000 : ℝ)+2*(523520342429/275300000000000 : ℝ)*(5627/50000 : ℝ)=(1000073882825229/1000000000000000 : ℝ) by norm_num, show 1+2*(7451347942095727/50000000000000000000 : ℝ)=(25007451347942095727/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9006575422186329/25000000000000000000 : ℝ)+(7451347942095727/50000000000000000000 : ℝ) ≤ ((13760125299155581219/13765000000000000000 : ℝ)+(523520342429/275300000000000 : ℝ)*((14007/100000 : ℝ)+(5627/50000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (13760125299155581219/13765000000000000000 : ℝ)+(523520342429/275300000000000 : ℝ)*((14007/100000 : ℝ)+(5627/50000 : ℝ))=(10001262348594719/10000000000000000 : ℝ) by norm_num, show 1+(9006575422186329/25000000000000000000 : ℝ)+(7451347942095727/50000000000000000000 : ℝ)=(10005092899757293677/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9006575422186329/25000000000000000000 : ℝ) ≤ ((13760125299155581219/13765000000000000000 : ℝ)+2*(523520342429/275300000000000 : ℝ)*(14007/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (13760125299155581219/13765000000000000000 : ℝ)+2*(523520342429/275300000000000 : ℝ)*(14007/100000 : ℝ)=(2500446467234287/2500000000000000 : ℝ) by norm_num, show 1+2*(9006575422186329/25000000000000000000 : ℝ)=(12509006575422186329/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13760125299155581219/13765000000000000000 : ℝ)*(X 1 0+X 2 0)+(523520342429/275300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (13760125299155581219/13765000000000000000 : ℝ)) (alpha := (523520342429/275300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13760125299155581219/13765000000000000000 : ℝ)*(X 0 1+X 2 1)+(523520342429/275300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (13760125299155581219/13765000000000000000 : ℝ)) (alpha := (523520342429/275300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13760125299155581219/13765000000000000000 : ℝ)*(X 0 2+X 1 2)+(523520342429/275300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (13760125299155581219/13765000000000000000 : ℝ)) (alpha := (523520342429/275300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-220229043/1000000000 : ℝ)*X 0 0+(2697149543/5000000000 : ℝ)*X 0 1+(5264514597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336242833/2500000000 : ℝ)*X 1 0+(-1134069057/5000000000 : ℝ)*X 1 1+(5264514591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344971339/10000000000 : ℝ)*X 2 0+(658064323/1250000000 : ℝ)*X 2 1+(-2268138113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375061253/10000000000 : ℝ)*X 0 0+(1062419843/2500000000 : ℝ)*X 0 1+(450419039/1000000000 : ℝ)*X 0 2+(4375061253/10000000000 : ℝ)*X 1 0+(1062419843/2500000000 : ℝ)*X 1 1+(450419039/1000000000 : ℝ)*X 1 2+(4375061253/10000000000 : ℝ)*X 2 0+(1062419843/2500000000 : ℝ)*X 2 1+(450419039/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2202295511/10000000000 : ℝ)*X 0 0+(5264839607/10000000000 : ℝ)*X 0 1+(2696986443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312273419/10000000000 : ℝ)*X 1 0+(-1069339773/5000000000 : ℝ)*X 1 1+(2696986481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328068249/2500000000 : ℝ)*X 2 0+(1078794589/2000000000 : ℝ)*X 2 1+(-106934007/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43750709/100000000 : ℝ)*X 0 0+(4503552909/10000000000 : ℝ)*X 0 1+(212515971/500000000 : ℝ)*X 0 2+(43750709/100000000 : ℝ)*X 1 0+(4503552909/10000000000 : ℝ)*X 1 1+(212515971/500000000 : ℝ)*X 1 2+(43750709/100000000 : ℝ)*X 2 0+(4503552909/10000000000 : ℝ)*X 2 1+(212515971/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6378062192050846753077/1720625000000000000000000000 : ℝ) := by norm_num
    linear_combination (146248791/20000000000000 : ℝ)*(base19) + (692209501/100000000000000 : ℝ)*(base23) + (3282173/12500000000000 : ℝ)*(lower2) + (90756833/100000000000000 : ℝ)*(upper3) + (28512901/50000000000000 : ℝ)*(upper5) + (5817121815471641/100000000000000 : ℝ)*(major0) + (5817121815471641/100000000000000 : ℝ)*(major1) + (5817121815471641/100000000000000 : ℝ)*(major2) + (770510104042157/10000000000000 : ℝ)*(sp0) + (7705119689906699/100000000000000 : ℝ)*(sp1) + (7705119728941153/100000000000000 : ℝ)*(sp2) + (491139063016243/12500000000000 : ℝ)*(sp3) + (4845182271/25000000000000 : ℝ)*(sp4) + (2645525429/25000000000000 : ℝ)*(sp7) + (196456154311583/5000000000000 : ℝ)*(f.failure) + (3852560210575327/50000000000000 : ℝ)*(f.sum) + (81647983662131/13765000000000000000000000000 : ℝ)*base66 + (7321076547236160379/1376500000000000000000000000000000 : ℝ)*base67 + (23161260713874839621/1376500000000000000000000000000000 : ℝ)*base70 + (36796545554316160379/1376500000000000000000000000000000 : ℝ)*base71 + (61523197396401/13765000000000000000000000000 : ℝ)*base74 + (23172095689092339621/1376500000000000000000000000000000 : ℝ)*base76 + (12334677335507339621/1376500000000000000000000000000000 : ℝ)*base78 + (9027165233720160379/1376500000000000000000000000000000 : ℝ)*base79 + (28067218774563/6882500000000000000000000000 : ℝ)*base82 + (1494683/250000000000000000000 : ℝ)*base89 + (1494683/250000000000000000000 : ℝ)*base91 + (1494683/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133913495218503405190101/13765000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1797052379/100000000000000 : ℝ)*(base19) + (503490921/50000000000000 : ℝ)*(base23) + (120503623/50000000000000 : ℝ)*(lower1) + (54716163/100000000000000 : ℝ)*(upper2) + (32069673/50000000000000 : ℝ)*(upper3) + (237610329/100000000000000 : ℝ)*(upper5) + (5846411490981713/100000000000000 : ℝ)*(major0) + (5846411490981713/100000000000000 : ℝ)*(major1) + (5846411490981713/100000000000000 : ℝ)*(major2) + (4491284383/10000000000000 : ℝ)*(sp1) + (3871958060581157/50000000000000 : ℝ)*(sp4) + (1548773882253221/20000000000000 : ℝ)*(sp5) + (7743915114180473/100000000000000 : ℝ)*(sp6) + (394890653651609/10000000000000 : ℝ)*(sp7) + (394890653651609/10000000000000 : ℝ)*(f.failure) + (3871958060581157/50000000000000 : ℝ)*(f.sum) + (27760473634813/13765000000000000000000000000 : ℝ)*base66 + (24512159303847098147/1376500000000000000000000000000000 : ℝ)*base67 + (70671039455046901853/1376500000000000000000000000000000 : ℝ)*base70 + (5175157303001598147/1376500000000000000000000000000000 : ℝ)*base71 + (32127292962977/13765000000000000000000000000 : ℝ)*base73 + (5115720204550901853/1376500000000000000000000000000000 : ℝ)*base76 + (12445606548797098147/1376500000000000000000000000000000 : ℝ)*base77 + (10707427226858401853/1376500000000000000000000000000000 : ℝ)*base80 + (27379913147823/13765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1002909/500000000000000000000 : ℝ)*base89 + (1002909/500000000000000000000 : ℝ)*base91 + (1002909/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1069_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1069_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1069_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1069_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1069_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
