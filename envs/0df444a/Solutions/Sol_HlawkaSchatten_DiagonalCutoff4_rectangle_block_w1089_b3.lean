-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1089_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:56:26.975633+00:00
-- url     : https://prove2.me/submissions/edf821c1-754c-44e5-8250-6919a3cbed6e

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
theorem support_rectangle_w1089_s9_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438499121/2000000000 : ℝ)*x 0 + (1348481543/2500000000 : ℝ)*x 1 + (658111671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438499121/2000000000 : ℝ)^4141 ≤ (133175168631/1000000000000 : ℝ)^3117 := by
    have hnat : (438499121 : ℕ)^4141*1000000000000^3117 ≤ 133175168631^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438499121 2000000000 133175168631 1000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348481543/2500000000 : ℝ)^4141 ≤ (44038260484583/100000000000000 : ℝ)^3117 := by
    have hnat : (1348481543 : ℕ)^4141*100000000000000^3117 ≤ 44038260484583^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348481543 2500000000 44038260484583 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658111671/1250000000 : ℝ)^4141 ≤ (21322111312609/50000000000000 : ℝ)^3117 := by
    have hnat : (658111671 : ℕ)^4141*50000000000000^3117 ≤ 21322111312609^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658111671 1250000000 21322111312609 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438499121/2000000000 : ℝ), (1348481543/2500000000 : ℝ), (658111671/1250000000 : ℝ)] ![(133175168631/1000000000000 : ℝ), (44038260484583/100000000000000 : ℝ), (21322111312609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438499121/2000000000 : ℝ)|^4141 ≤ (133175168631/1000000000000 : ℝ)^3117
        have hw : |(-438499121/2000000000 : ℝ)|=(438499121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348481543/2500000000 : ℝ)|^4141 ≤ (44038260484583/100000000000000 : ℝ)^3117
        have hw : |(1348481543/2500000000 : ℝ)|=(1348481543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658111671/1250000000 : ℝ)|^4141 ≤ (21322111312609/50000000000000 : ℝ)^3117
        have hw : |(658111671/1250000000 : ℝ)|=(658111671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s9_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672457189/5000000000 : ℝ)*x 0 + (-1128978143/5000000000 : ℝ)*x 1 + (658111671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672457189/5000000000 : ℝ)^4141 ≤ (43507444282661/100000000000000 : ℝ)^3117 := by
    have hnat : (2672457189 : ℕ)^4141*100000000000000^3117 ≤ 43507444282661^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672457189 5000000000 43507444282661 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128978143/5000000000 : ℝ)^4141 ≤ (1731041633899/12500000000000 : ℝ)^3117 := by
    have hnat : (1128978143 : ℕ)^4141*12500000000000^3117 ≤ 1731041633899^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128978143 5000000000 1731041633899 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658111671/1250000000 : ℝ)^4141 ≤ (21322111312609/50000000000000 : ℝ)^3117 := by
    have hnat : (658111671 : ℕ)^4141*50000000000000^3117 ≤ 21322111312609^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658111671 1250000000 21322111312609 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672457189/5000000000 : ℝ), (-1128978143/5000000000 : ℝ), (658111671/1250000000 : ℝ)] ![(43507444282661/100000000000000 : ℝ), (1731041633899/12500000000000 : ℝ), (21322111312609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672457189/5000000000 : ℝ)|^4141 ≤ (43507444282661/100000000000000 : ℝ)^3117
        have hw : |(2672457189/5000000000 : ℝ)|=(2672457189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128978143/5000000000 : ℝ)|^4141 ≤ (1731041633899/12500000000000 : ℝ)^3117
        have hw : |(-1128978143/5000000000 : ℝ)|=(1128978143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658111671/1250000000 : ℝ)|^4141 ≤ (21322111312609/50000000000000 : ℝ)^3117
        have hw : |(658111671/1250000000 : ℝ)|=(658111671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s9_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672457189/5000000000 : ℝ)*x 0 + (658111671/1250000000 : ℝ)*x 1 + (-1128978143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672457189/5000000000 : ℝ)^4141 ≤ (43507444282661/100000000000000 : ℝ)^3117 := by
    have hnat : (2672457189 : ℕ)^4141*100000000000000^3117 ≤ 43507444282661^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672457189 5000000000 43507444282661 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658111671/1250000000 : ℝ)^4141 ≤ (21322111312609/50000000000000 : ℝ)^3117 := by
    have hnat : (658111671 : ℕ)^4141*50000000000000^3117 ≤ 21322111312609^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658111671 1250000000 21322111312609 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128978143/5000000000 : ℝ)^4141 ≤ (1731041633899/12500000000000 : ℝ)^3117 := by
    have hnat : (1128978143 : ℕ)^4141*12500000000000^3117 ≤ 1731041633899^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128978143 5000000000 1731041633899 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672457189/5000000000 : ℝ), (658111671/1250000000 : ℝ), (-1128978143/5000000000 : ℝ)] ![(43507444282661/100000000000000 : ℝ), (21322111312609/50000000000000 : ℝ), (1731041633899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672457189/5000000000 : ℝ)|^4141 ≤ (43507444282661/100000000000000 : ℝ)^3117
        have hw : |(2672457189/5000000000 : ℝ)|=(2672457189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658111671/1250000000 : ℝ)|^4141 ≤ (21322111312609/50000000000000 : ℝ)^3117
        have hw : |(658111671/1250000000 : ℝ)|=(658111671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1128978143/5000000000 : ℝ)|^4141 ≤ (1731041633899/12500000000000 : ℝ)^3117
        have hw : |(-1128978143/5000000000 : ℝ)|=(1128978143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s9_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546524517/1250000000 : ℝ)*x 0 + (849406897/2000000000 : ℝ)*x 1 + (2250538001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546524517/1250000000 : ℝ)^4141 ≤ (16658347623393/50000000000000 : ℝ)^3117 := by
    have hnat : (546524517 : ℕ)^4141*50000000000000^3117 ≤ 16658347623393^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546524517 1250000000 16658347623393 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849406897/2000000000 : ℝ)^4141 ≤ (16027808968547/50000000000000 : ℝ)^3117 := by
    have hnat : (849406897 : ℕ)^4141*50000000000000^3117 ≤ 16027808968547^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849406897 2000000000 16027808968547 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250538001/5000000000 : ℝ)^4141 ≤ (6925537360209/20000000000000 : ℝ)^3117 := by
    have hnat : (2250538001 : ℕ)^4141*20000000000000^3117 ≤ 6925537360209^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250538001 5000000000 6925537360209 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546524517/1250000000 : ℝ), (849406897/2000000000 : ℝ), (2250538001/5000000000 : ℝ)] ![(16658347623393/50000000000000 : ℝ), (16027808968547/50000000000000 : ℝ), (6925537360209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546524517/1250000000 : ℝ)|^4141 ≤ (16658347623393/50000000000000 : ℝ)^3117
        have hw : |(546524517/1250000000 : ℝ)|=(546524517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849406897/2000000000 : ℝ)|^4141 ≤ (16027808968547/50000000000000 : ℝ)^3117
        have hw : |(849406897/2000000000 : ℝ)|=(849406897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250538001/5000000000 : ℝ)|^4141 ≤ (6925537360209/20000000000000 : ℝ)^3117
        have hw : |(2250538001/5000000000 : ℝ)|=(2250538001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s9_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096250253/5000000000 : ℝ)*x 0 + (5265216797/10000000000 : ℝ)*x 1 + (2696800827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096250253/5000000000 : ℝ)^4141 ≤ (1331755641231/10000000000000 : ℝ)^3117 := by
    have hnat : (1096250253 : ℕ)^4141*10000000000000^3117 ≤ 1331755641231^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096250253 5000000000 1331755641231 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265216797/10000000000 : ℝ)^4141 ≤ (42647702970971/100000000000000 : ℝ)^3117 := by
    have hnat : (5265216797 : ℕ)^4141*100000000000000^3117 ≤ 42647702970971^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265216797 10000000000 42647702970971 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696800827/5000000000 : ℝ)^4141 ≤ (2201737030137/5000000000000 : ℝ)^3117 := by
    have hnat : (2696800827 : ℕ)^4141*5000000000000^3117 ≤ 2201737030137^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696800827 5000000000 2201737030137 5000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096250253/5000000000 : ℝ), (5265216797/10000000000 : ℝ), (2696800827/5000000000 : ℝ)] ![(1331755641231/10000000000000 : ℝ), (42647702970971/100000000000000 : ℝ), (2201737030137/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096250253/5000000000 : ℝ)|^4141 ≤ (1331755641231/10000000000000 : ℝ)^3117
        have hw : |(-1096250253/5000000000 : ℝ)|=(1096250253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265216797/10000000000 : ℝ)|^4141 ≤ (42647702970971/100000000000000 : ℝ)^3117
        have hw : |(5265216797/10000000000 : ℝ)|=(5265216797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696800827/5000000000 : ℝ)|^4141 ≤ (2201737030137/5000000000000 : ℝ)^3117
        have hw : |(2696800827/5000000000 : ℝ)|=(2696800827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s9_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2186102963/5000000000 : ℝ)*x 0 + (4500439457/10000000000 : ℝ)*x 1 + (4247673381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186102963/5000000000 : ℝ)^4141 ≤ (8329198588973/25000000000000 : ℝ)^3117 := by
    have hnat : (2186102963 : ℕ)^4141*25000000000000^3117 ≤ 8329198588973^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186102963 5000000000 8329198588973 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500439457/10000000000 : ℝ)^4141 ≤ (8655295273193/25000000000000 : ℝ)^3117 := by
    have hnat : (4500439457 : ℕ)^4141*25000000000000^3117 ≤ 8655295273193^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500439457 10000000000 8655295273193 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247673381/10000000000 : ℝ)^4141 ≤ (6412404907669/20000000000000 : ℝ)^3117 := by
    have hnat : (4247673381 : ℕ)^4141*20000000000000^3117 ≤ 6412404907669^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247673381 10000000000 6412404907669 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186102963/5000000000 : ℝ), (4500439457/10000000000 : ℝ), (4247673381/10000000000 : ℝ)] ![(8329198588973/25000000000000 : ℝ), (8655295273193/25000000000000 : ℝ), (6412404907669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186102963/5000000000 : ℝ)|^4141 ≤ (8329198588973/25000000000000 : ℝ)^3117
        have hw : |(2186102963/5000000000 : ℝ)|=(2186102963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500439457/10000000000 : ℝ)|^4141 ≤ (8655295273193/25000000000000 : ℝ)^3117
        have hw : |(4500439457/10000000000 : ℝ)|=(4500439457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247673381/10000000000 : ℝ)|^4141 ≤ (6412404907669/20000000000000 : ℝ)^3117
        have hw : |(4247673381/10000000000 : ℝ)|=(4247673381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2821/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14017/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11283/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (7370374279936779/50000000000000000000 : ℝ) := by
    have hpowers : (11283/100000 : ℝ)^8281 ≤ (7370374279936779/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11283 : ℕ)^8281*50000000000000000000^2048 ≤ 7370374279936779^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11283 100000 7370374279936779 50000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11283/100000 : ℝ)) (X := (7370374279936779/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14017/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (35443488155322993/100000000000000000000 : ℝ) := by
    have hpowers : (14017/100000 : ℝ)^8281 ≤ (35443488155322993/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14017 : ℕ)^8281*100000000000000000000^2048 ≤ 35443488155322993^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14017 100000 35443488155322993 100000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14017/100000 : ℝ)) (X := (35443488155322993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007370374279936779/25000000000000000000 : ℝ) ≤ (10000729035239737/10000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (25007370374279936779/25000000000000000000 : ℝ)^2048 ≤ (10000729035239737/10000000000000000 : ℝ)^8281 := by
      have hnat : (25007370374279936779 : ℕ)^2048*10000000000000000^8281 ≤ 10000729035239737^8281*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007370374279936779 25000000000000000000 10000729035239737 10000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000729035239737/10000000000000000 : ℝ)) (X := (25007370374279936779/25000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050184236715196551/100000000000000000000 : ℝ) ≤ (500062044385603/500000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (100050184236715196551/100000000000000000000 : ℝ)^2048 ≤ (500062044385603/500000000000000 : ℝ)^8281 := by
      have hnat : (100050184236715196551 : ℕ)^2048*500000000000000^8281 ≤ 500062044385603^8281*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050184236715196551 100000000000000000000 500062044385603 500000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500062044385603/500000000000000 : ℝ)) (X := (100050184236715196551/100000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035443488155322993/50000000000000000000 : ℝ) ≤ (10001752740184383/10000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (50035443488155322993/50000000000000000000 : ℝ)^2048 ≤ (10001752740184383/10000000000000000 : ℝ)^8281 := by
      have hnat : (50035443488155322993 : ℕ)^2048*10000000000000000^8281 ≤ 10001752740184383^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035443488155322993 50000000000000000000 10001752740184383 10000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001752740184383/10000000000000000 : ℝ)) (X := (50035443488155322993/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7370374279936779/50000000000000000000 : ℝ) ≤ ((1366522135972750007/1367000000000000000 : ℝ)+2*(511852472323/273400000000000 : ℝ)*(11283/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1366522135972750007/1367000000000000000 : ℝ)+2*(511852472323/273400000000000 : ℝ)*(11283/100000 : ℝ)=(10000729035239737/10000000000000000 : ℝ) by norm_num, show 1+2*(7370374279936779/50000000000000000000 : ℝ)=(25007370374279936779/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35443488155322993/100000000000000000000 : ℝ)+(7370374279936779/50000000000000000000 : ℝ) ≤ ((1366522135972750007/1367000000000000000 : ℝ)+(511852472323/273400000000000 : ℝ)*((14017/100000 : ℝ)+(11283/100000 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (1366522135972750007/1367000000000000000 : ℝ)+(511852472323/273400000000000 : ℝ)*((14017/100000 : ℝ)+(11283/100000 : ℝ))=(500062044385603/500000000000000 : ℝ) by norm_num, show 1+(35443488155322993/100000000000000000000 : ℝ)+(7370374279936779/50000000000000000000 : ℝ)=(100050184236715196551/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35443488155322993/100000000000000000000 : ℝ) ≤ ((1366522135972750007/1367000000000000000 : ℝ)+2*(511852472323/273400000000000 : ℝ)*(14017/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1366522135972750007/1367000000000000000 : ℝ)+2*(511852472323/273400000000000 : ℝ)*(14017/100000 : ℝ)=(10001752740184383/10000000000000000 : ℝ) by norm_num, show 1+2*(35443488155322993/100000000000000000000 : ℝ)=(50035443488155322993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1366522135972750007/1367000000000000000 : ℝ)*(X 1 0+X 2 0)+(511852472323/273400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (1366522135972750007/1367000000000000000 : ℝ)) (alpha := (511852472323/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1366522135972750007/1367000000000000000 : ℝ)*(X 0 1+X 2 1)+(511852472323/273400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (1366522135972750007/1367000000000000000 : ℝ)) (alpha := (511852472323/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1366522135972750007/1367000000000000000 : ℝ)*(X 0 2+X 1 2)+(511852472323/273400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (1366522135972750007/1367000000000000000 : ℝ)) (alpha := (511852472323/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-438499121/2000000000 : ℝ)*X 0 0+(1348481543/2500000000 : ℝ)*X 0 1+(658111671/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672457189/5000000000 : ℝ)*X 1 0+(-1128978143/5000000000 : ℝ)*X 1 1+(658111671/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672457189/5000000000 : ℝ)*X 2 0+(658111671/1250000000 : ℝ)*X 2 1+(-1128978143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546524517/1250000000 : ℝ)*X 0 0+(849406897/2000000000 : ℝ)*X 0 1+(2250538001/5000000000 : ℝ)*X 0 2+(546524517/1250000000 : ℝ)*X 1 0+(849406897/2000000000 : ℝ)*X 1 1+(2250538001/5000000000 : ℝ)*X 1 2+(546524517/1250000000 : ℝ)*X 2 0+(849406897/2000000000 : ℝ)*X 2 1+(2250538001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1096250253/5000000000 : ℝ)*X 0 0+(5265216797/10000000000 : ℝ)*X 0 1+(2696800827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2186102963/5000000000 : ℝ)*X 0 0+(4500439457/10000000000 : ℝ)*X 0 1+(4247673381/10000000000 : ℝ)*X 0 2+(2186102963/5000000000 : ℝ)*X 1 0+(4500439457/10000000000 : ℝ)*X 1 1+(4247673381/10000000000 : ℝ)*X 1 2+(2186102963/5000000000 : ℝ)*X 2 0+(4500439457/10000000000 : ℝ)*X 2 1+(4247673381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8022187967259832771552083/4271875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (382339469/100000000000000 : ℝ)*(base19) + (355416593/100000000000000 : ℝ)*(base23) + (449689/3125000000000 : ℝ)*(lower2) + (12205713/25000000000000 : ℝ)*(upper3) + (3601823/12500000000000 : ℝ)*(upper5) + (182599430214437/3125000000000 : ℝ)*(major0) + (182599430214437/3125000000000 : ℝ)*(major1) + (182599430214437/3125000000000 : ℝ)*(major2) + (3874988996856657/50000000000000 : ℝ)*(sp0) + (7749987884136277/100000000000000 : ℝ)*(sp1) + (3874993955529577/50000000000000 : ℝ)*(sp2) + (1968184773083499/50000000000000 : ℝ)*(sp3) + (10272762433/100000000000000 : ℝ)*(sp4) + (5658484283/100000000000000 : ℝ)*(sp5) + (3936375204651281/100000000000000 : ℝ)*(f.failure) + (3874994133237873/50000000000000 : ℝ)*(f.sum) + (6680312843443/3417500000000000000000000000 : ℝ)*base65 + (72899584165650191/4271875000000000000000000000000 : ℝ)*base68 + (697651361862213/133496093750000000000000000000 : ℝ)*base70 + (65814038790881441/4271875000000000000000000000000 : ℝ)*base72 + (1253892170649/6835000000000000000000000000 : ℝ)*base74 + (21227478692807717/2135937500000000000000000000000 : ℝ)*base75 + (33238537749325191/4271875000000000000000000000000 : ℝ)*base78 + (1487634852112213/133496093750000000000000000000 : ℝ)*base80 + (12236226787291/6835000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (72649551/10000000000000000000000 : ℝ)*base89 + (72649551/10000000000000000000000 : ℝ)*base91 + (72649551/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1089_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1089_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1089_box_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-257977649/1250000000 : ℝ)*x 0 + (1344263429/2500000000 : ℝ)*x 1 + (2688526859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257977649/1250000000 : ℝ)^4141 ≤ (12289308329757/100000000000000 : ℝ)^3117 := by
    have hnat : (257977649 : ℕ)^4141*100000000000000^3117 ≤ 12289308329757^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257977649 1250000000 12289308329757 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344263429/2500000000 : ℝ)^4141 ≤ (43855345817953/100000000000000 : ℝ)^3117 := by
    have hnat : (1344263429 : ℕ)^4141*100000000000000^3117 ≤ 43855345817953^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344263429 2500000000 43855345817953 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688526859/5000000000 : ℝ)^4141 ≤ (5481918229953/12500000000000 : ℝ)^3117 := by
    have hnat : (2688526859 : ℕ)^4141*12500000000000^3117 ≤ 5481918229953^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688526859 5000000000 5481918229953 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257977649/1250000000 : ℝ), (1344263429/2500000000 : ℝ), (2688526859/5000000000 : ℝ)] ![(12289308329757/100000000000000 : ℝ), (43855345817953/100000000000000 : ℝ), (5481918229953/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257977649/1250000000 : ℝ)|^4141 ≤ (12289308329757/100000000000000 : ℝ)^3117
        have hw : |(-257977649/1250000000 : ℝ)|=(257977649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344263429/2500000000 : ℝ)|^4141 ≤ (43855345817953/100000000000000 : ℝ)^3117
        have hw : |(1344263429/2500000000 : ℝ)|=(1344263429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688526859/5000000000 : ℝ)|^4141 ≤ (5481918229953/12500000000000 : ℝ)^3117
        have hw : |(2688526859/5000000000 : ℝ)|=(2688526859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059091401/2000000000 : ℝ)*x 0 + (-1087171601/5000000000 : ℝ)*x 1 + (53770537/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059091401/2000000000 : ℝ)^4141 ≤ (8594684168739/20000000000000 : ℝ)^3117 := by
    have hnat : (1059091401 : ℕ)^4141*20000000000000^3117 ≤ 8594684168739^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059091401 2000000000 8594684168739 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087171601/5000000000 : ℝ)^4141 ≤ (2634246699171/20000000000000 : ℝ)^3117 := by
    have hnat : (1087171601 : ℕ)^4141*20000000000000^3117 ≤ 2634246699171^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087171601 5000000000 2634246699171 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53770537/100000000 : ℝ)^4141 ≤ (21927672822293/50000000000000 : ℝ)^3117 := by
    have hnat : (53770537 : ℕ)^4141*50000000000000^3117 ≤ 21927672822293^3117*100000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53770537 100000000 21927672822293 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059091401/2000000000 : ℝ), (-1087171601/5000000000 : ℝ), (53770537/100000000 : ℝ)] ![(8594684168739/20000000000000 : ℝ), (2634246699171/20000000000000 : ℝ), (21927672822293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059091401/2000000000 : ℝ)|^4141 ≤ (8594684168739/20000000000000 : ℝ)^3117
        have hw : |(1059091401/2000000000 : ℝ)|=(1059091401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087171601/5000000000 : ℝ)|^4141 ≤ (2634246699171/20000000000000 : ℝ)^3117
        have hw : |(-1087171601/5000000000 : ℝ)|=(1087171601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53770537/100000000 : ℝ)|^4141 ≤ (21927672822293/50000000000000 : ℝ)^3117
        have hw : |(53770537/100000000 : ℝ)|=(53770537/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295456483/10000000000 : ℝ)*x 0 + (1075410851/2000000000 : ℝ)*x 1 + (-2174343153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295456483/10000000000 : ℝ)^4141 ≤ (42973415215937/100000000000000 : ℝ)^3117 := by
    have hnat : (5295456483 : ℕ)^4141*100000000000000^3117 ≤ 42973415215937^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295456483 10000000000 42973415215937 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075410851/2000000000 : ℝ)^4141 ≤ (2740959478641/6250000000000 : ℝ)^3117 := by
    have hnat : (1075410851 : ℕ)^4141*6250000000000^3117 ≤ 2740959478641^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075410851 2000000000 2740959478641 6250000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174343153/10000000000 : ℝ)^4141 ≤ (6585616550761/50000000000000 : ℝ)^3117 := by
    have hnat : (2174343153 : ℕ)^4141*50000000000000^3117 ≤ 6585616550761^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174343153 10000000000 6585616550761 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295456483/10000000000 : ℝ), (1075410851/2000000000 : ℝ), (-2174343153/10000000000 : ℝ)] ![(42973415215937/100000000000000 : ℝ), (2740959478641/6250000000000 : ℝ), (6585616550761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295456483/10000000000 : ℝ)|^4141 ≤ (42973415215937/100000000000000 : ℝ)^3117
        have hw : |(5295456483/10000000000 : ℝ)|=(5295456483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075410851/2000000000 : ℝ)|^4141 ≤ (2740959478641/6250000000000 : ℝ)^3117
        have hw : |(1075410851/2000000000 : ℝ)|=(1075410851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174343153/10000000000 : ℝ)|^4141 ≤ (6585616550761/50000000000000 : ℝ)^3117
        have hw : |(-2174343153/10000000000 : ℝ)|=(2174343153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2240160511/5000000000 : ℝ)*x 0 + (540034913/1250000000 : ℝ)*x 1 + (4320278729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240160511/5000000000 : ℝ)^4141 ≤ (2100568829/6103515625 : ℝ)^3117 := by
    have hnat : (2240160511 : ℕ)^4141*6103515625^3117 ≤ 2100568829^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240160511 5000000000 2100568829 6103515625 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540034913/1250000000 : ℝ)^4141 ≤ (655842860889/2000000000000 : ℝ)^3117 := by
    have hnat : (540034913 : ℕ)^4141*2000000000000^3117 ≤ 655842860889^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540034913 1250000000 655842860889 2000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4320278729/10000000000 : ℝ)^4141 ≤ (8198034311559/25000000000000 : ℝ)^3117 := by
    have hnat : (4320278729 : ℕ)^4141*25000000000000^3117 ≤ 8198034311559^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320278729 10000000000 8198034311559 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240160511/5000000000 : ℝ), (540034913/1250000000 : ℝ), (4320278729/10000000000 : ℝ)] ![(2100568829/6103515625 : ℝ), (655842860889/2000000000000 : ℝ), (8198034311559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240160511/5000000000 : ℝ)|^4141 ≤ (2100568829/6103515625 : ℝ)^3117
        have hw : |(2240160511/5000000000 : ℝ)|=(2240160511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540034913/1250000000 : ℝ)|^4141 ≤ (655842860889/2000000000000 : ℝ)^3117
        have hw : |(540034913/1250000000 : ℝ)|=(540034913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4320278729/10000000000 : ℝ)|^4141 ≤ (8198034311559/25000000000000 : ℝ)^3117
        have hw : |(4320278729/10000000000 : ℝ)|=(4320278729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464509821/2000000000 : ℝ)*x 0 + (5280426899/10000000000 : ℝ)*x 1 + (5280426769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464509821/2000000000 : ℝ)^4141 ≤ (7188546014661/50000000000000 : ℝ)^3117 := by
    have hnat : (464509821 : ℕ)^4141*50000000000000^3117 ≤ 7188546014661^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464509821 2000000000 7188546014661 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280426899/10000000000 : ℝ)^4141 ≤ (10702863669717/25000000000000 : ℝ)^3117 := by
    have hnat : (5280426899 : ℕ)^4141*25000000000000^3117 ≤ 10702863669717^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280426899 10000000000 10702863669717 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280426769/10000000000 : ℝ)^4141 ≤ (42811453278627/100000000000000 : ℝ)^3117 := by
    have hnat : (5280426769 : ℕ)^4141*100000000000000^3117 ≤ 42811453278627^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280426769 10000000000 42811453278627 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464509821/2000000000 : ℝ), (5280426899/10000000000 : ℝ), (5280426769/10000000000 : ℝ)] ![(7188546014661/50000000000000 : ℝ), (10702863669717/25000000000000 : ℝ), (42811453278627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464509821/2000000000 : ℝ)|^4141 ≤ (7188546014661/50000000000000 : ℝ)^3117
        have hw : |(-464509821/2000000000 : ℝ)|=(464509821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280426899/10000000000 : ℝ)|^4141 ≤ (10702863669717/25000000000000 : ℝ)^3117
        have hw : |(5280426899/10000000000 : ℝ)|=(5280426899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280426769/10000000000 : ℝ)|^4141 ≤ (42811453278627/100000000000000 : ℝ)^3117
        have hw : |(5280426769/10000000000 : ℝ)|=(5280426769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340951389/2500000000 : ℝ)*x 0 + (-553047941/2500000000 : ℝ)*x 1 + (330026679/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340951389/2500000000 : ℝ)^4141 ≤ (43711854289547/100000000000000 : ℝ)^3117 := by
    have hnat : (1340951389 : ℕ)^4141*100000000000000^3117 ≤ 43711854289547^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340951389 2500000000 43711854289547 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553047941/2500000000 : ℝ)^4141 ≤ (3369172850011/25000000000000 : ℝ)^3117 := by
    have hnat : (553047941 : ℕ)^4141*25000000000000^3117 ≤ 3369172850011^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553047941 2500000000 3369172850011 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330026679/625000000 : ℝ)^4141 ≤ (1070286357547/2500000000000 : ℝ)^3117 := by
    have hnat : (330026679 : ℕ)^4141*2500000000000^3117 ≤ 1070286357547^3117*625000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330026679 625000000 1070286357547 2500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340951389/2500000000 : ℝ), (-553047941/2500000000 : ℝ), (330026679/625000000 : ℝ)] ![(43711854289547/100000000000000 : ℝ), (3369172850011/25000000000000 : ℝ), (1070286357547/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340951389/2500000000 : ℝ)|^4141 ≤ (43711854289547/100000000000000 : ℝ)^3117
        have hw : |(1340951389/2500000000 : ℝ)|=(1340951389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553047941/2500000000 : ℝ)|^4141 ≤ (3369172850011/25000000000000 : ℝ)^3117
        have hw : |(-553047941/2500000000 : ℝ)|=(553047941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330026679/625000000 : ℝ)|^4141 ≤ (1070286357547/2500000000000 : ℝ)^3117
        have hw : |(330026679/625000000 : ℝ)|=(330026679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_6 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681902771/5000000000 : ℝ)*x 0 + (5280426971/10000000000 : ℝ)*x 1 + (-55304791/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681902771/5000000000 : ℝ)^4141 ≤ (21855927068987/50000000000000 : ℝ)^3117 := by
    have hnat : (2681902771 : ℕ)^4141*50000000000000^3117 ≤ 21855927068987^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681902771 5000000000 21855927068987 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280426971/10000000000 : ℝ)^4141 ≤ (21405727727193/50000000000000 : ℝ)^3117 := by
    have hnat : (5280426971 : ℕ)^4141*50000000000000^3117 ≤ 21405727727193^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280426971 10000000000 21405727727193 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55304791/250000000 : ℝ)^4141 ≤ (3369172599117/25000000000000 : ℝ)^3117 := by
    have hnat : (55304791 : ℕ)^4141*25000000000000^3117 ≤ 3369172599117^3117*250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55304791 250000000 3369172599117 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681902771/5000000000 : ℝ), (5280426971/10000000000 : ℝ), (-55304791/250000000 : ℝ)] ![(21855927068987/50000000000000 : ℝ), (21405727727193/50000000000000 : ℝ), (3369172599117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681902771/5000000000 : ℝ)|^4141 ≤ (21855927068987/50000000000000 : ℝ)^3117
        have hw : |(2681902771/5000000000 : ℝ)|=(2681902771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280426971/10000000000 : ℝ)|^4141 ≤ (21405727727193/50000000000000 : ℝ)^3117
        have hw : |(5280426971/10000000000 : ℝ)|=(5280426971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55304791/250000000 : ℝ)|^4141 ≤ (3369172599117/25000000000000 : ℝ)^3117
        have hw : |(-55304791/250000000 : ℝ)|=(55304791/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_7 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065933091/2500000000 : ℝ)*x 0 + (553569/1250000 : ℝ)*x 1 + (27678451/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065933091/2500000000 : ℝ)^4141 ≤ (8055790422687/25000000000000 : ℝ)^3117 := by
    have hnat : (1065933091 : ℕ)^4141*25000000000000^3117 ≤ 8055790422687^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065933091 2500000000 8055790422687 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553569/1250000 : ℝ)^4141 ≤ (16944209164751/50000000000000 : ℝ)^3117 := by
    have hnat : (553569 : ℕ)^4141*50000000000000^3117 ≤ 16944209164751^3117*1250000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553569 1250000 16944209164751 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27678451/62500000 : ℝ)^4141 ≤ (33888419956091/100000000000000 : ℝ)^3117 := by
    have hnat : (27678451 : ℕ)^4141*100000000000000^3117 ≤ 33888419956091^3117*62500000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27678451 62500000 33888419956091 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065933091/2500000000 : ℝ), (553569/1250000 : ℝ), (27678451/62500000 : ℝ)] ![(8055790422687/25000000000000 : ℝ), (16944209164751/50000000000000 : ℝ), (33888419956091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065933091/2500000000 : ℝ)|^4141 ≤ (8055790422687/25000000000000 : ℝ)^3117
        have hw : |(1065933091/2500000000 : ℝ)|=(1065933091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553569/1250000 : ℝ)|^4141 ≤ (16944209164751/50000000000000 : ℝ)^3117
        have hw : |(553569/1250000 : ℝ)|=(553569/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27678451/62500000 : ℝ)|^4141 ≤ (33888419956091/100000000000000 : ℝ)^3117
        have hw : |(27678451/62500000 : ℝ)|=(27678451/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_8 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283563593/1250000000 : ℝ)*x 0 + (5214814779/10000000000 : ℝ)*x 1 + (5386657/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283563593/1250000000 : ℝ)^4141 ≤ (13934380311793/100000000000000 : ℝ)^3117 := by
    have hnat : (283563593 : ℕ)^4141*100000000000000^3117 ≤ 13934380311793^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283563593 1250000000 13934380311793 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214814779/10000000000 : ℝ)^4141 ≤ (4210618753127/10000000000000 : ℝ)^3117 := by
    have hnat : (5214814779 : ℕ)^4141*10000000000000^3117 ≤ 4210618753127^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214814779 10000000000 4210618753127 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386657/10000000 : ℝ)^4141 ≤ (8791886429929/20000000000000 : ℝ)^3117 := by
    have hnat : (5386657 : ℕ)^4141*20000000000000^3117 ≤ 8791886429929^3117*10000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386657 10000000 8791886429929 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283563593/1250000000 : ℝ), (5214814779/10000000000 : ℝ), (5386657/10000000 : ℝ)] ![(13934380311793/100000000000000 : ℝ), (4210618753127/10000000000000 : ℝ), (8791886429929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283563593/1250000000 : ℝ)|^4141 ≤ (13934380311793/100000000000000 : ℝ)^3117
        have hw : |(-283563593/1250000000 : ℝ)|=(283563593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214814779/10000000000 : ℝ)|^4141 ≤ (4210618753127/10000000000000 : ℝ)^3117
        have hw : |(5214814779/10000000000 : ℝ)|=(5214814779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386657/10000000 : ℝ)|^4141 ≤ (8791886429929/20000000000000 : ℝ)^3117
        have hw : |(5386657/10000000 : ℝ)|=(5386657/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_9 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288660489/10000000000 : ℝ)*x 0 + (-2170510501/10000000000 : ℝ)*x 1 + (1346664421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288660489/10000000000 : ℝ)^4141 ≤ (42900162067857/100000000000000 : ℝ)^3117 := by
    have hnat : (5288660489 : ℕ)^4141*100000000000000^3117 ≤ 42900162067857^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288660489 10000000000 42900162067857 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170510501/10000000000 : ℝ)^4141 ≤ (13140398357013/100000000000000 : ℝ)^3117 := by
    have hnat : (2170510501 : ℕ)^4141*100000000000000^3117 ≤ 13140398357013^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170510501 10000000000 13140398357013 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346664421/2500000000 : ℝ)^4141 ≤ (43959439565433/100000000000000 : ℝ)^3117 := by
    have hnat : (1346664421 : ℕ)^4141*100000000000000^3117 ≤ 43959439565433^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346664421 2500000000 43959439565433 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288660489/10000000000 : ℝ), (-2170510501/10000000000 : ℝ), (1346664421/2500000000 : ℝ)] ![(42900162067857/100000000000000 : ℝ), (13140398357013/100000000000000 : ℝ), (43959439565433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288660489/10000000000 : ℝ)|^4141 ≤ (42900162067857/100000000000000 : ℝ)^3117
        have hw : |(5288660489/10000000000 : ℝ)|=(5288660489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170510501/10000000000 : ℝ)|^4141 ≤ (13140398357013/100000000000000 : ℝ)^3117
        have hw : |(-2170510501/10000000000 : ℝ)|=(2170510501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346664421/2500000000 : ℝ)|^4141 ≤ (43959439565433/100000000000000 : ℝ)^3117
        have hw : |(1346664421/2500000000 : ℝ)|=(1346664421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_10 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644330161/5000000000 : ℝ)*x 0 + (538665691/1000000000 : ℝ)*x 1 + (-271313971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644330161/5000000000 : ℝ)^4141 ≤ (8580032053633/20000000000000 : ℝ)^3117 := by
    have hnat : (2644330161 : ℕ)^4141*20000000000000^3117 ≤ 8580032053633^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644330161 5000000000 8580032053633 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538665691/1000000000 : ℝ)^4141 ≤ (43959431173883/100000000000000 : ℝ)^3117 := by
    have hnat : (538665691 : ℕ)^4141*100000000000000^3117 ≤ 43959431173883^3117*1000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538665691 1000000000 43959431173883 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271313971/1250000000 : ℝ)^4141 ≤ (525616341897/4000000000000 : ℝ)^3117 := by
    have hnat : (271313971 : ℕ)^4141*4000000000000^3117 ≤ 525616341897^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271313971 1250000000 525616341897 4000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644330161/5000000000 : ℝ), (538665691/1000000000 : ℝ), (-271313971/1250000000 : ℝ)] ![(8580032053633/20000000000000 : ℝ), (43959431173883/100000000000000 : ℝ), (525616341897/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644330161/5000000000 : ℝ)|^4141 ≤ (8580032053633/20000000000000 : ℝ)^3117
        have hw : |(2644330161/5000000000 : ℝ)|=(2644330161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538665691/1000000000 : ℝ)|^4141 ≤ (43959431173883/100000000000000 : ℝ)^3117
        have hw : |(538665691/1000000000 : ℝ)|=(538665691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271313971/1250000000 : ℝ)|^4141 ≤ (525616341897/4000000000000 : ℝ)^3117
        have hw : |(-271313971/1250000000 : ℝ)|=(271313971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_11 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4501574239/10000000000 : ℝ)*x 0 + (4309511813/10000000000 : ℝ)*x 1 + (538688993/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4501574239/10000000000 : ℝ)^4141 ≤ (6926555832999/20000000000000 : ℝ)^3117 := by
    have hnat : (4501574239 : ℕ)^4141*20000000000000^3117 ≤ 6926555832999^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501574239 10000000000 6926555832999 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4309511813/10000000000 : ℝ)^4141 ≤ (32683609749029/100000000000000 : ℝ)^3117 := by
    have hnat : (4309511813 : ℕ)^4141*100000000000000^3117 ≤ 32683609749029^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309511813 10000000000 32683609749029 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538688993/1250000000 : ℝ)^4141 ≤ (32683611068931/100000000000000 : ℝ)^3117 := by
    have hnat : (538688993 : ℕ)^4141*100000000000000^3117 ≤ 32683611068931^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538688993 1250000000 32683611068931 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4501574239/10000000000 : ℝ), (4309511813/10000000000 : ℝ), (538688993/1250000000 : ℝ)] ![(6926555832999/20000000000000 : ℝ), (32683609749029/100000000000000 : ℝ), (32683611068931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4501574239/10000000000 : ℝ)|^4141 ≤ (6926555832999/20000000000000 : ℝ)^3117
        have hw : |(4501574239/10000000000 : ℝ)|=(4501574239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4309511813/10000000000 : ℝ)|^4141 ≤ (32683609749029/100000000000000 : ℝ)^3117
        have hw : |(4309511813/10000000000 : ℝ)|=(4309511813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538688993/1250000000 : ℝ)|^4141 ≤ (32683611068931/100000000000000 : ℝ)^3117
        have hw : |(538688993/1250000000 : ℝ)|=(538688993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_12 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-264776763/1250000000 : ℝ)*x 0 + (1088269683/2000000000 : ℝ)*x 1 + (659051801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264776763/1250000000 : ℝ)^4141 ≤ (12721455087557/100000000000000 : ℝ)^3117 := by
    have hnat : (264776763 : ℕ)^4141*100000000000000^3117 ≤ 12721455087557^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264776763 1250000000 12721455087557 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088269683/2000000000 : ℝ)^4141 ≤ (11138342976951/25000000000000 : ℝ)^3117 := by
    have hnat : (1088269683 : ℕ)^4141*25000000000000^3117 ≤ 11138342976951^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088269683 2000000000 11138342976951 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659051801/1250000000 : ℝ)^4141 ≤ (42725172990317/100000000000000 : ℝ)^3117 := by
    have hnat : (659051801 : ℕ)^4141*100000000000000^3117 ≤ 42725172990317^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659051801 1250000000 42725172990317 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264776763/1250000000 : ℝ), (1088269683/2000000000 : ℝ), (659051801/1250000000 : ℝ)] ![(12721455087557/100000000000000 : ℝ), (11138342976951/25000000000000 : ℝ), (42725172990317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264776763/1250000000 : ℝ)|^4141 ≤ (12721455087557/100000000000000 : ℝ)^3117
        have hw : |(-264776763/1250000000 : ℝ)|=(264776763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088269683/2000000000 : ℝ)|^4141 ≤ (11138342976951/25000000000000 : ℝ)^3117
        have hw : |(1088269683/2000000000 : ℝ)|=(1088269683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659051801/1250000000 : ℝ)|^4141 ≤ (42725172990317/100000000000000 : ℝ)^3117
        have hw : |(659051801/1250000000 : ℝ)|=(659051801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_13 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369470291/10000000000 : ℝ)*x 0 + (-110763589/500000000 : ℝ)*x 1 + (5272415069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369470291/10000000000 : ℝ)^4141 ≤ (43773195105111/100000000000000 : ℝ)^3117 := by
    have hnat : (5369470291 : ℕ)^4141*100000000000000^3117 ≤ 43773195105111^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369470291 10000000000 43773195105111 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110763589/500000000 : ℝ)^4141 ≤ (6750812391101/50000000000000 : ℝ)^3117 := by
    have hnat : (110763589 : ℕ)^4141*50000000000000^3117 ≤ 6750812391101^3117*500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110763589 500000000 6750812391101 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272415069/10000000000 : ℝ)^4141 ≤ (42725180106453/100000000000000 : ℝ)^3117 := by
    have hnat : (5272415069 : ℕ)^4141*100000000000000^3117 ≤ 42725180106453^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272415069 10000000000 42725180106453 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369470291/10000000000 : ℝ), (-110763589/500000000 : ℝ), (5272415069/10000000000 : ℝ)] ![(43773195105111/100000000000000 : ℝ), (6750812391101/50000000000000 : ℝ), (42725180106453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369470291/10000000000 : ℝ)|^4141 ≤ (43773195105111/100000000000000 : ℝ)^3117
        have hw : |(5369470291/10000000000 : ℝ)|=(5369470291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110763589/500000000 : ℝ)|^4141 ≤ (6750812391101/50000000000000 : ℝ)^3117
        have hw : |(-110763589/500000000 : ℝ)|=(110763589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272415069/10000000000 : ℝ)|^4141 ≤ (42725180106453/100000000000000 : ℝ)^3117
        have hw : |(5272415069/10000000000 : ℝ)|=(5272415069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_14 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369470877/10000000000 : ℝ)*x 0 + (2636207251/5000000000 : ℝ)*x 1 + (-2215271749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369470877/10000000000 : ℝ)^4141 ≤ (5471650181467/12500000000000 : ℝ)^3117 := by
    have hnat : (5369470877 : ℕ)^4141*12500000000000^3117 ≤ 5471650181467^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369470877 10000000000 5471650181467 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636207251/5000000000 : ℝ)^4141 ≤ (21362587001147/50000000000000 : ℝ)^3117 := by
    have hnat : (2636207251 : ℕ)^4141*50000000000000^3117 ≤ 21362587001147^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636207251 5000000000 21362587001147 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215271749/10000000000 : ℝ)^4141 ≤ (13501624531193/100000000000000 : ℝ)^3117 := by
    have hnat : (2215271749 : ℕ)^4141*100000000000000^3117 ≤ 13501624531193^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215271749 10000000000 13501624531193 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369470877/10000000000 : ℝ), (2636207251/5000000000 : ℝ), (-2215271749/10000000000 : ℝ)] ![(5471650181467/12500000000000 : ℝ), (21362587001147/50000000000000 : ℝ), (13501624531193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369470877/10000000000 : ℝ)|^4141 ≤ (5471650181467/12500000000000 : ℝ)^3117
        have hw : |(5369470877/10000000000 : ℝ)|=(5369470877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636207251/5000000000 : ℝ)|^4141 ≤ (21362587001147/50000000000000 : ℝ)^3117
        have hw : |(2636207251/5000000000 : ℝ)|=(2636207251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2215271749/10000000000 : ℝ)|^4141 ≤ (13501624531193/100000000000000 : ℝ)^3117
        have hw : |(-2215271749/10000000000 : ℝ)|=(2215271749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_box_15 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212276983/500000000 : ℝ)*x 0 + (887505227/2000000000 : ℝ)*x 1 + (1109381719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212276983/500000000 : ℝ)^4141 ≤ (8010157412223/25000000000000 : ℝ)^3117 := by
    have hnat : (212276983 : ℕ)^4141*25000000000000^3117 ≤ 8010157412223^3117*500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212276983 500000000 8010157412223 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887505227/2000000000 : ℝ)^4141 ≤ (16989840697047/50000000000000 : ℝ)^3117 := by
    have hnat : (887505227 : ℕ)^4141*50000000000000^3117 ≤ 16989840697047^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887505227 2000000000 16989840697047 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109381719/2500000000 : ℝ)^4141 ≤ (4247461116531/12500000000000 : ℝ)^3117 := by
    have hnat : (1109381719 : ℕ)^4141*12500000000000^3117 ≤ 4247461116531^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109381719 2500000000 4247461116531 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212276983/500000000 : ℝ), (887505227/2000000000 : ℝ), (1109381719/2500000000 : ℝ)] ![(8010157412223/25000000000000 : ℝ), (16989840697047/50000000000000 : ℝ), (4247461116531/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212276983/500000000 : ℝ)|^4141 ≤ (8010157412223/25000000000000 : ℝ)^3117
        have hw : |(212276983/500000000 : ℝ)|=(212276983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(887505227/2000000000 : ℝ)|^4141 ≤ (16989840697047/50000000000000 : ℝ)^3117
        have hw : |(887505227/2000000000 : ℝ)|=(887505227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1109381719/2500000000 : ℝ)|^4141 ≤ (4247461116531/12500000000000 : ℝ)^3117
        have hw : |(1109381719/2500000000 : ℝ)|=(1109381719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31113/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29629/50000 : ℝ) ∧ (19911/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16601/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2821/25000 : ℝ) ^ (8281/2048 : ℝ) ≤ (7373015936525439/50000000000000000000 : ℝ) := by
    have hpowers : (2821/25000 : ℝ)^8281 ≤ (7373015936525439/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2821 : ℕ)^8281*50000000000000000000^2048 ≤ 7373015936525439^2048*25000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 25000 7373015936525439 50000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/25000 : ℝ)) (X := (7373015936525439/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14017/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (35443488155322993/100000000000000000000 : ℝ) := by
    have hpowers : (14017/100000 : ℝ)^8281 ≤ (35443488155322993/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14017 : ℕ)^8281*100000000000000000000^2048 ≤ 35443488155322993^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14017 100000 35443488155322993 100000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14017/100000 : ℝ)) (X := (35443488155322993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007373015936525439/25000000000000000000 : ℝ) ≤ (2500182324127073/2500000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (25007373015936525439/25000000000000000000 : ℝ)^2048 ≤ (2500182324127073/2500000000000000 : ℝ)^8281 := by
      have hnat : (25007373015936525439 : ℕ)^2048*2500000000000000^8281 ≤ 2500182324127073^8281*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007373015936525439 25000000000000000000 2500182324127073 2500000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500182324127073/2500000000000000 : ℝ)) (X := (25007373015936525439/25000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050189520028373871/100000000000000000000 : ℝ) ≤ (10001241018325993/10000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (100050189520028373871/100000000000000000000 : ℝ)^2048 ≤ (10001241018325993/10000000000000000 : ℝ)^8281 := by
      have hnat : (100050189520028373871 : ℕ)^2048*10000000000000000^8281 ≤ 10001241018325993^8281*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050189520028373871 100000000000000000000 10001241018325993 10000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001241018325993/10000000000000000 : ℝ)) (X := (100050189520028373871/100000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035443488155322993/50000000000000000000 : ℝ) ≤ (5000876370071847/5000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (50035443488155322993/50000000000000000000 : ℝ)^2048 ≤ (5000876370071847/5000000000000000 : ℝ)^8281 := by
      have hnat : (50035443488155322993 : ℕ)^2048*5000000000000000^8281 ≤ 5000876370071847^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035443488155322993 50000000000000000000 5000876370071847 5000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000876370071847/5000000000000000 : ℝ)) (X := (50035443488155322993/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7373015936525439/50000000000000000000 : ℝ) ≤ ((6830111157343821467/6832500000000000000 : ℝ)+2*(511721817701/273300000000000 : ℝ)*(2821/25000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (6830111157343821467/6832500000000000000 : ℝ)+2*(511721817701/273300000000000 : ℝ)*(2821/25000 : ℝ)=(2500182324127073/2500000000000000 : ℝ) by norm_num, show 1+2*(7373015936525439/50000000000000000000 : ℝ)=(25007373015936525439/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35443488155322993/100000000000000000000 : ℝ)+(7373015936525439/50000000000000000000 : ℝ) ≤ ((6830111157343821467/6832500000000000000 : ℝ)+(511721817701/273300000000000 : ℝ)*((14017/100000 : ℝ)+(2821/25000 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (6830111157343821467/6832500000000000000 : ℝ)+(511721817701/273300000000000 : ℝ)*((14017/100000 : ℝ)+(2821/25000 : ℝ))=(10001241018325993/10000000000000000 : ℝ) by norm_num, show 1+(35443488155322993/100000000000000000000 : ℝ)+(7373015936525439/50000000000000000000 : ℝ)=(100050189520028373871/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35443488155322993/100000000000000000000 : ℝ) ≤ ((6830111157343821467/6832500000000000000 : ℝ)+2*(511721817701/273300000000000 : ℝ)*(14017/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (6830111157343821467/6832500000000000000 : ℝ)+2*(511721817701/273300000000000 : ℝ)*(14017/100000 : ℝ)=(5000876370071847/5000000000000000 : ℝ) by norm_num, show 1+2*(35443488155322993/100000000000000000000 : ℝ)=(50035443488155322993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6830111157343821467/6832500000000000000 : ℝ)*(X 1 0+X 2 0)+(511721817701/273300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (6830111157343821467/6832500000000000000 : ℝ)) (alpha := (511721817701/273300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6830111157343821467/6832500000000000000 : ℝ)*(X 0 1+X 2 1)+(511721817701/273300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (6830111157343821467/6832500000000000000 : ℝ)) (alpha := (511721817701/273300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6830111157343821467/6832500000000000000 : ℝ)*(X 0 2+X 1 2)+(511721817701/273300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (6830111157343821467/6832500000000000000 : ℝ)) (alpha := (511721817701/273300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-257977649/1250000000 : ℝ)*X 0 0+(1344263429/2500000000 : ℝ)*X 0 1+(2688526859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059091401/2000000000 : ℝ)*X 1 0+(-1087171601/5000000000 : ℝ)*X 1 1+(53770537/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295456483/10000000000 : ℝ)*X 2 0+(1075410851/2000000000 : ℝ)*X 2 1+(-2174343153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2240160511/5000000000 : ℝ)*X 0 0+(540034913/1250000000 : ℝ)*X 0 1+(4320278729/10000000000 : ℝ)*X 0 2+(2240160511/5000000000 : ℝ)*X 1 0+(540034913/1250000000 : ℝ)*X 1 1+(4320278729/10000000000 : ℝ)*X 1 2+(2240160511/5000000000 : ℝ)*X 2 0+(540034913/1250000000 : ℝ)*X 2 1+(4320278729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-464509821/2000000000 : ℝ)*X 0 0+(5280426899/10000000000 : ℝ)*X 0 1+(5280426769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340951389/2500000000 : ℝ)*X 1 0+(-553047941/2500000000 : ℝ)*X 1 1+(330026679/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681902771/5000000000 : ℝ)*X 2 0+(5280426971/10000000000 : ℝ)*X 2 1+(-55304791/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065933091/2500000000 : ℝ)*X 0 0+(553569/1250000 : ℝ)*X 0 1+(27678451/62500000 : ℝ)*X 0 2+(1065933091/2500000000 : ℝ)*X 1 0+(553569/1250000 : ℝ)*X 1 1+(27678451/62500000 : ℝ)*X 1 2+(1065933091/2500000000 : ℝ)*X 2 0+(553569/1250000 : ℝ)*X 2 1+(27678451/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-283563593/1250000000 : ℝ)*X 0 0+(5214814779/10000000000 : ℝ)*X 0 1+(5386657/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288660489/10000000000 : ℝ)*X 1 0+(-2170510501/10000000000 : ℝ)*X 1 1+(1346664421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644330161/5000000000 : ℝ)*X 2 0+(538665691/1000000000 : ℝ)*X 2 1+(-271313971/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4501574239/10000000000 : ℝ)*X 0 0+(4309511813/10000000000 : ℝ)*X 0 1+(538688993/1250000000 : ℝ)*X 0 2+(4501574239/10000000000 : ℝ)*X 1 0+(4309511813/10000000000 : ℝ)*X 1 1+(538688993/1250000000 : ℝ)*X 1 2+(4501574239/10000000000 : ℝ)*X 2 0+(4309511813/10000000000 : ℝ)*X 2 1+(538688993/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-264776763/1250000000 : ℝ)*X 0 0+(1088269683/2000000000 : ℝ)*X 0 1+(659051801/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369470291/10000000000 : ℝ)*X 1 0+(-110763589/500000000 : ℝ)*X 1 1+(5272415069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369470877/10000000000 : ℝ)*X 2 0+(2636207251/5000000000 : ℝ)*X 2 1+(-2215271749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((212276983/500000000 : ℝ)*X 0 0+(887505227/2000000000 : ℝ)*X 0 1+(1109381719/2500000000 : ℝ)*X 0 2+(212276983/500000000 : ℝ)*X 1 0+(887505227/2000000000 : ℝ)*X 1 1+(1109381719/2500000000 : ℝ)*X 1 2+(212276983/500000000 : ℝ)*X 2 0+(887505227/2000000000 : ℝ)*X 2 1+(1109381719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31113/50000 : ℝ) ≤ (-17714247633135287745487580190093/28468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3955203/50000000000000 : ℝ)*(upper0) + (5217659/50000000000000 : ℝ)*(upper1) + (5673109/50000000000000 : ℝ)*(upper4) + (19604673/20000000000000 : ℝ)*(upper5) + (969012454749643/25000000000000 : ℝ)*(major0) + (969012454749643/25000000000000 : ℝ)*(major1) + (969012454749643/25000000000000 : ℝ)*(major2) + (679332149/25000000000000 : ℝ)*(sp1) + (4278097479/100000000000000 : ℝ)*(sp3) + (516165494786307/10000000000000 : ℝ)*(sp4) + (2580830150267551/50000000000000 : ℝ)*(sp5) + (5161663017863699/100000000000000 : ℝ)*(sp6) + (1305586751410591/50000000000000 : ℝ)*(sp7) + (8070000629/100000000000000 : ℝ)*(sp8) + (1305588890459331/50000000000000 : ℝ)*(f.failure) + (5161663017863699/100000000000000 : ℝ)*(f.sum) + (11992125251509/1708125000000000000000000000 : ℝ)*base65 + (1122934280791248781/170812500000000000000000000000000 : ℝ)*base67 + (2081056335870498781/170812500000000000000000000000000 : ℝ)*base69 + (4334222101806686281/170812500000000000000000000000000 : ℝ)*base71 + (24009363917033/3416250000000000000000000000 : ℝ)*base73 + (2929719196868373781/170812500000000000000000000000000 : ℝ)*base75 + (1730838356326811281/170812500000000000000000000000000 : ℝ)*base77 + (1642851692962248781/170812500000000000000000000000000 : ℝ)*base79 + (59030358327557/13665000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8148899/5000000000000000000000 : ℝ)*base90 + (8148899/5000000000000000000000 : ℝ)*base92 + (8148899/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29629/50000 : ℝ) ≤ (16870717427419783227047110762909/28468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118165437/100000000000000 : ℝ)*(lower0) + (12151371/20000000000000 : ℝ)*(upper2) + (85910833/100000000000000 : ℝ)*(upper3) + (40512239/100000000000000 : ℝ)*(lower5) + (1969667620972573/50000000000000 : ℝ)*(major0) + (1969667620972573/50000000000000 : ℝ)*(major1) + (1969667620972573/50000000000000 : ℝ)*(major2) + (1041021146150971/20000000000000 : ℝ)*(sp0) + (5205006521900981/100000000000000 : ℝ)*(sp1) + (5205084732337309/100000000000000 : ℝ)*(sp2) + (331725993872577/12500000000000 : ℝ)*(sp3) + (10499208773/50000000000000 : ℝ)*(sp6) + (1654687403/50000000000000 : ℝ)*(sp7) + (49604426937/50000000000000 : ℝ)*(sp9) + (2653811260355423/100000000000000 : ℝ)*(f.failure) + (1041021146150971/20000000000000 : ℝ)*(f.sum) + (5102220684847/6832500000000000000000000000 : ℝ)*base66 + (1996390891950949591/341625000000000000000000000000000 : ℝ)*base67 + (2712155232387199591/341625000000000000000000000000000 : ℝ)*base69 + (757773843708574591/341625000000000000000000000000000 : ℝ)*base71 + (190286594249363/6832500000000000000000000000 : ℝ)*base73 + (1425144421220050409/341625000000000000000000000000000 : ℝ)*base76 + (415992417720574591/341625000000000000000000000000000 : ℝ)*base77 + (18015548656016824591/341625000000000000000000000000000 : ℝ)*base79 + (86351853779191/13665000000000000000000000000 : ℝ)*base81 + (88608833/10000000000000000000000 : ℝ)*base89 + (88608833/10000000000000000000000 : ℝ)*base91 + (88608833/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19911/25000 : ℝ) ≤ (90697848001231758528679981746603/113875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115109039/50000000000000 : ℝ)*(upper0) + (7110701/50000000000000 : ℝ)*(lower1) + (185087033/50000000000000 : ℝ)*(upper2) + (157781673/20000000000000 : ℝ)*(lower5) + (4407489422644791/100000000000000 : ℝ)*(major0) + (4407489422644791/100000000000000 : ℝ)*(major1) + (4407489422644791/100000000000000 : ℝ)*(major2) + (2025100569/100000000000000 : ℝ)*(sp0) + (401665799737/100000000000000 : ℝ)*(sp1) + (10222754439/5000000000000 : ℝ)*(sp3) + (1454808817064927/25000000000000 : ℝ)*(sp8) + (290941781378027/5000000000000 : ℝ)*(sp9) + (5819237293360277/100000000000000 : ℝ)*(sp10) + (2968988147553653/100000000000000 : ℝ)*(sp11) + (1449801075509/48828125000 : ℝ)*(f.failure) + (5819237293360277/100000000000000 : ℝ)*(f.sum) + (1287580987439/569375000000000000000000000 : ℝ)*base65 + (833724004157482201/227750000000000000000000000000000 : ℝ)*base68 + (2225142734967232201/227750000000000000000000000000000 : ℝ)*base70 + (1438312494943267799/227750000000000000000000000000000 : ℝ)*base71 + (1505247146659/569375000000000000000000000 : ℝ)*base73 + (854140955508267799/227750000000000000000000000000000 : ℝ)*base75 + (2020551395933517799/227750000000000000000000000000000 : ℝ)*base77 + (6336352709074017799/227750000000000000000000000000000 : ℝ)*base79 + (24414228449117/4555000000000000000000000000 : ℝ)*base81 + (472063/39062500000000000000 : ℝ)*base90 + (472063/39062500000000000000 : ℝ)*base92 + (472063/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-16601/20000 : ℝ) ≤ (-9451898713996975443266109749053/11387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25704549/20000000000000 : ℝ)*(lower1) + (1884317/2500000000000 : ℝ)*(lower2) + (259158637/100000000000000 : ℝ)*(upper5) + (444224334528353/10000000000000 : ℝ)*(major0) + (444224334528353/10000000000000 : ℝ)*(major1) + (444224334528353/10000000000000 : ℝ)*(major2) + (21022577521/50000000000000 : ℝ)*(sp4) + (119813252221/25000000000000 : ℝ)*(sp6) + (61215337/9765625000 : ℝ)*(sp7) + (39162711/195312500000 : ℝ)*(sp8) + (1479871697639559/25000000000000 : ℝ)*(sp12) + (591954888702131/10000000000000 : ℝ)*(sp13) + (5919069634012427/100000000000000 : ℝ)*(sp14) + (2991978426373371/100000000000000 : ℝ)*(sp15) + (748151317856063/25000000000000 : ℝ)*(f.failure) + (591954888702131/10000000000000 : ℝ)*(f.sum) + (711080753657/170812500000000000000000000 : ℝ)*base65 + (1394795505463803851/68325000000000000000000000000000 : ℝ)*base67 + (487067771617728851/68325000000000000000000000000000 : ℝ)*base69 + (1154387933971128851/68325000000000000000000000000000 : ℝ)*base71 + (11883075067001/2733000000000000000000000000 : ℝ)*base73 + (401148209284428851/68325000000000000000000000000000 : ℝ)*base75 + (602450221196103851/68325000000000000000000000000000 : ℝ)*base77 + (564089832102903851/68325000000000000000000000000000 : ℝ)*base79 + (11002755174223/2733000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (23138273/2500000000000000000000 : ℝ)*base89 + (23138273/2500000000000000000000 : ℝ)*base91 + (23138273/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1089_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29629/50000 : ℝ) else (19911/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16601/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1089_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1089_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29629/50000 : ℝ) else (19911/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16601/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1089_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1089_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29629/50000 : ℝ) else (19911/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16601/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1089_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
