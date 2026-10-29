-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1581_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:39.724865+00:00
-- url     : https://prove2.me/submissions/e86475f1-6420-454b-9e06-113cb6f6f58b

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
theorem support_rectangle_w1581_box_0 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1568635377/10000000000 : ℝ)*x 0 + (5395416887/10000000000 : ℝ)*x 1 + (5395416397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1568635377/10000000000 : ℝ)^4659 ≤ (72725388111/781250000000 : ℝ)^3635 := by
    have hnat : (1568635377 : ℕ)^4659*781250000000^3635 ≤ 72725388111^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568635377 10000000000 72725388111 781250000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395416887/10000000000 : ℝ)^4659 ≤ (45345577794349/100000000000000 : ℝ)^3635 := by
    have hnat : (5395416887 : ℕ)^4659*100000000000000^3635 ≤ 45345577794349^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395416887 10000000000 45345577794349 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395416397/10000000000 : ℝ)^4659 ≤ (22672786258023/50000000000000 : ℝ)^3635 := by
    have hnat : (5395416397 : ℕ)^4659*50000000000000^3635 ≤ 22672786258023^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395416397 10000000000 22672786258023 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1568635377/10000000000 : ℝ), (5395416887/10000000000 : ℝ), (5395416397/10000000000 : ℝ)] ![(72725388111/781250000000 : ℝ), (45345577794349/100000000000000 : ℝ), (22672786258023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1568635377/10000000000 : ℝ)|^4659 ≤ (72725388111/781250000000 : ℝ)^3635
        have hw : |(-1568635377/10000000000 : ℝ)|=(1568635377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395416887/10000000000 : ℝ)|^4659 ≤ (45345577794349/100000000000000 : ℝ)^3635
        have hw : |(5395416887/10000000000 : ℝ)|=(5395416887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395416397/10000000000 : ℝ)|^4659 ≤ (22672786258023/50000000000000 : ℝ)^3635
        have hw : |(5395416397/10000000000 : ℝ)|=(5395416397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_1 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054226587/2000000000 : ℝ)*x 0 + (-1741461647/10000000000 : ℝ)*x 1 + (2697708391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054226587/2000000000 : ℝ)^4659 ≤ (11002788311171/25000000000000 : ℝ)^3635 := by
    have hnat : (1054226587 : ℕ)^4659*25000000000000^3635 ≤ 11002788311171^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054226587 2000000000 11002788311171 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741461647/10000000000 : ℝ)^4659 ≤ (5321635041497/50000000000000 : ℝ)^3635 := by
    have hnat : (1741461647 : ℕ)^4659*50000000000000^3635 ≤ 5321635041497^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741461647 10000000000 5321635041497 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697708391/5000000000 : ℝ)^4659 ≤ (11336394165821/25000000000000 : ℝ)^3635 := by
    have hnat : (2697708391 : ℕ)^4659*25000000000000^3635 ≤ 11336394165821^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697708391 5000000000 11336394165821 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054226587/2000000000 : ℝ), (-1741461647/10000000000 : ℝ), (2697708391/5000000000 : ℝ)] ![(11002788311171/25000000000000 : ℝ), (5321635041497/50000000000000 : ℝ), (11336394165821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054226587/2000000000 : ℝ)|^4659 ≤ (11002788311171/25000000000000 : ℝ)^3635
        have hw : |(1054226587/2000000000 : ℝ)|=(1054226587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1741461647/10000000000 : ℝ)|^4659 ≤ (5321635041497/50000000000000 : ℝ)^3635
        have hw : |(-1741461647/10000000000 : ℝ)|=(1741461647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697708391/5000000000 : ℝ)|^4659 ≤ (11336394165821/25000000000000 : ℝ)^3635
        have hw : |(2697708391/5000000000 : ℝ)|=(2697708391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_2 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5147591/9765625 : ℝ)*x 0 + (1348854189/2500000000 : ℝ)*x 1 + (-1741461341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5147591/9765625 : ℝ)^4659 ≤ (11002788977343/25000000000000 : ℝ)^3635 := by
    have hnat : (5147591 : ℕ)^4659*25000000000000^3635 ≤ 11002788977343^3635*9765625^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147591 9765625 11002788977343 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348854189/2500000000 : ℝ)^4659 ≤ (45345576383211/100000000000000 : ℝ)^3635 := by
    have hnat : (1348854189 : ℕ)^4659*100000000000000^3635 ≤ 45345576383211^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348854189 2500000000 45345576383211 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1741461341/10000000000 : ℝ)^4659 ≤ (5321633842989/50000000000000 : ℝ)^3635 := by
    have hnat : (1741461341 : ℕ)^4659*50000000000000^3635 ≤ 5321633842989^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741461341 10000000000 5321633842989 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5147591/9765625 : ℝ), (1348854189/2500000000 : ℝ), (-1741461341/10000000000 : ℝ)] ![(11002788977343/25000000000000 : ℝ), (45345576383211/100000000000000 : ℝ), (5321633842989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5147591/9765625 : ℝ)|^4659 ≤ (11002788977343/25000000000000 : ℝ)^3635
        have hw : |(5147591/9765625 : ℝ)|=(5147591/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348854189/2500000000 : ℝ)|^4659 ≤ (45345576383211/100000000000000 : ℝ)^3635
        have hw : |(1348854189/2500000000 : ℝ)|=(1348854189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1741461341/10000000000 : ℝ)|^4659 ≤ (5321633842989/50000000000000 : ℝ)^3635
        have hw : |(-1741461341/10000000000 : ℝ)|=(1741461341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_3 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4438978329/10000000000 : ℝ)*x 0 + (4145115999/10000000000 : ℝ)*x 1 + (4145116197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4438978329/10000000000 : ℝ)^4659 ≤ (17655932834863/50000000000000 : ℝ)^3635 := by
    have hnat : (4438978329 : ℕ)^4659*50000000000000^3635 ≤ 17655932834863^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438978329 10000000000 17655932834863 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145115999/10000000000 : ℝ)^4659 ≤ (16172033084327/50000000000000 : ℝ)^3635 := by
    have hnat : (4145115999 : ℕ)^4659*50000000000000^3635 ≤ 16172033084327^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145115999 10000000000 16172033084327 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145116197/10000000000 : ℝ)^4659 ≤ (252688032413/781250000000 : ℝ)^3635 := by
    have hnat : (4145116197 : ℕ)^4659*781250000000^3635 ≤ 252688032413^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145116197 10000000000 252688032413 781250000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4438978329/10000000000 : ℝ), (4145115999/10000000000 : ℝ), (4145116197/10000000000 : ℝ)] ![(17655932834863/50000000000000 : ℝ), (16172033084327/50000000000000 : ℝ), (252688032413/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4438978329/10000000000 : ℝ)|^4659 ≤ (17655932834863/50000000000000 : ℝ)^3635
        have hw : |(4438978329/10000000000 : ℝ)|=(4438978329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145115999/10000000000 : ℝ)|^4659 ≤ (16172033084327/50000000000000 : ℝ)^3635
        have hw : |(4145115999/10000000000 : ℝ)|=(4145115999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145116197/10000000000 : ℝ)|^4659 ≤ (252688032413/781250000000 : ℝ)^3635
        have hw : |(4145116197/10000000000 : ℝ)|=(4145116197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_4 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-989069773/5000000000 : ℝ)*x 0 + (5245232501/10000000000 : ℝ)*x 1 + (5245232641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989069773/5000000000 : ℝ)^4659 ≤ (1253165794653/10000000000000 : ℝ)^3635 := by
    have hnat : (989069773 : ℕ)^4659*10000000000000^3635 ≤ 1253165794653^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989069773 5000000000 1253165794653 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245232501/10000000000 : ℝ)^4659 ≤ (43734170265197/100000000000000 : ℝ)^3635 := by
    have hnat : (5245232501 : ℕ)^4659*100000000000000^3635 ≤ 43734170265197^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245232501 10000000000 43734170265197 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245232641/10000000000 : ℝ)^4659 ≤ (21867085880669/50000000000000 : ℝ)^3635 := by
    have hnat : (5245232641 : ℕ)^4659*50000000000000^3635 ≤ 21867085880669^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245232641 10000000000 21867085880669 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989069773/5000000000 : ℝ), (5245232501/10000000000 : ℝ), (5245232641/10000000000 : ℝ)] ![(1253165794653/10000000000000 : ℝ), (43734170265197/100000000000000 : ℝ), (21867085880669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989069773/5000000000 : ℝ)|^4659 ≤ (1253165794653/10000000000000 : ℝ)^3635
        have hw : |(-989069773/5000000000 : ℝ)|=(989069773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245232501/10000000000 : ℝ)|^4659 ≤ (43734170265197/100000000000000 : ℝ)^3635
        have hw : |(5245232501/10000000000 : ℝ)|=(5245232501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245232641/10000000000 : ℝ)|^4659 ≤ (21867085880669/50000000000000 : ℝ)^3635
        have hw : |(5245232641/10000000000 : ℝ)|=(5245232641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_5 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375153411/10000000000 : ℝ)*x 0 + (-1804354497/10000000000 : ℝ)*x 1 + (81956753/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375153411/10000000000 : ℝ)^4659 ≤ (9025482851493/20000000000000 : ℝ)^3635 := by
    have hnat : (5375153411 : ℕ)^4659*20000000000000^3635 ≤ 9025482851493^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375153411 10000000000 9025482851493 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804354497/10000000000 : ℝ)^4659 ≤ (11138418770977/100000000000000 : ℝ)^3635 := by
    have hnat : (1804354497 : ℕ)^4659*100000000000000^3635 ≤ 11138418770977^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804354497 10000000000 11138418770977 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81956753/156250000 : ℝ)^4659 ≤ (43734166963001/100000000000000 : ℝ)^3635 := by
    have hnat : (81956753 : ℕ)^4659*100000000000000^3635 ≤ 43734166963001^3635*156250000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81956753 156250000 43734166963001 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375153411/10000000000 : ℝ), (-1804354497/10000000000 : ℝ), (81956753/156250000 : ℝ)] ![(9025482851493/20000000000000 : ℝ), (11138418770977/100000000000000 : ℝ), (43734166963001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375153411/10000000000 : ℝ)|^4659 ≤ (9025482851493/20000000000000 : ℝ)^3635
        have hw : |(5375153411/10000000000 : ℝ)|=(5375153411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1804354497/10000000000 : ℝ)|^4659 ≤ (11138418770977/100000000000000 : ℝ)^3635
        have hw : |(-1804354497/10000000000 : ℝ)|=(1804354497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81956753/156250000 : ℝ)|^4659 ≤ (43734166963001/100000000000000 : ℝ)^3635
        have hw : |(81956753/156250000 : ℝ)|=(81956753/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_6 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375153039/10000000000 : ℝ)*x 0 + (5245232643/10000000000 : ℝ)*x 1 + (-225544299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375153039/10000000000 : ℝ)^4659 ≤ (45127410254509/100000000000000 : ℝ)^3635 := by
    have hnat : (5375153039 : ℕ)^4659*100000000000000^3635 ≤ 45127410254509^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375153039 10000000000 45127410254509 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245232643/10000000000 : ℝ)^4659 ≤ (5466771472839/12500000000000 : ℝ)^3635 := by
    have hnat : (5245232643 : ℕ)^4659*12500000000000^3635 ≤ 5466771472839^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245232643 10000000000 5466771472839 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225544299/1250000000 : ℝ)^4659 ≤ (1113841794021/10000000000000 : ℝ)^3635 := by
    have hnat : (225544299 : ℕ)^4659*10000000000000^3635 ≤ 1113841794021^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225544299 1250000000 1113841794021 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375153039/10000000000 : ℝ), (5245232643/10000000000 : ℝ), (-225544299/1250000000 : ℝ)] ![(45127410254509/100000000000000 : ℝ), (5466771472839/12500000000000 : ℝ), (1113841794021/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375153039/10000000000 : ℝ)|^4659 ≤ (45127410254509/100000000000000 : ℝ)^3635
        have hw : |(5375153039/10000000000 : ℝ)|=(5375153039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245232643/10000000000 : ℝ)|^4659 ≤ (5466771472839/12500000000000 : ℝ)^3635
        have hw : |(5245232643/10000000000 : ℝ)|=(5245232643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225544299/1250000000 : ℝ)|^4659 ≤ (1113841794021/10000000000000 : ℝ)^3635
        have hw : |(-225544299/1250000000 : ℝ)|=(225544299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_7 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4035656081/10000000000 : ℝ)*x 0 + (4346650883/10000000000 : ℝ)*x 1 + (869330203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4035656081/10000000000 : ℝ)^4659 ≤ (1953340519423/6250000000000 : ℝ)^3635 := by
    have hnat : (4035656081 : ℕ)^4659*6250000000000^3635 ≤ 1953340519423^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035656081 10000000000 1953340519423 6250000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4346650883/10000000000 : ℝ)^4659 ≤ (687465503453/2000000000000 : ℝ)^3635 := by
    have hnat : (4346650883 : ℕ)^4659*2000000000000^3635 ≤ 687465503453^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346650883 10000000000 687465503453 2000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (869330203/2000000000 : ℝ)^4659 ≤ (8593319127641/25000000000000 : ℝ)^3635 := by
    have hnat : (869330203 : ℕ)^4659*25000000000000^3635 ≤ 8593319127641^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869330203 2000000000 8593319127641 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4035656081/10000000000 : ℝ), (4346650883/10000000000 : ℝ), (869330203/2000000000 : ℝ)] ![(1953340519423/6250000000000 : ℝ), (687465503453/2000000000000 : ℝ), (8593319127641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4035656081/10000000000 : ℝ)|^4659 ≤ (1953340519423/6250000000000 : ℝ)^3635
        have hw : |(4035656081/10000000000 : ℝ)|=(4035656081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4346650883/10000000000 : ℝ)|^4659 ≤ (687465503453/2000000000000 : ℝ)^3635
        have hw : |(4346650883/10000000000 : ℝ)|=(4346650883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(869330203/2000000000 : ℝ)|^4659 ≤ (8593319127641/25000000000000 : ℝ)^3635
        have hw : |(869330203/2000000000 : ℝ)|=(869330203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_8 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1891294299/10000000000 : ℝ)*x 0 + (2569654779/5000000000 : ℝ)*x 1 + (676956369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1891294299/10000000000 : ℝ)^4659 ≤ (2957726998053/25000000000000 : ℝ)^3635 := by
    have hnat : (1891294299 : ℕ)^4659*25000000000000^3635 ≤ 2957726998053^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891294299 10000000000 2957726998053 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569654779/5000000000 : ℝ)^4659 ≤ (21302718438751/50000000000000 : ℝ)^3635 := by
    have hnat : (2569654779 : ℕ)^4659*50000000000000^3635 ≤ 21302718438751^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569654779 5000000000 21302718438751 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676956369/1250000000 : ℝ)^4659 ≤ (1423864222471/3125000000000 : ℝ)^3635 := by
    have hnat : (676956369 : ℕ)^4659*3125000000000^3635 ≤ 1423864222471^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676956369 1250000000 1423864222471 3125000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1891294299/10000000000 : ℝ), (2569654779/5000000000 : ℝ), (676956369/1250000000 : ℝ)] ![(2957726998053/25000000000000 : ℝ), (21302718438751/50000000000000 : ℝ), (1423864222471/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1891294299/10000000000 : ℝ)|^4659 ≤ (2957726998053/25000000000000 : ℝ)^3635
        have hw : |(-1891294299/10000000000 : ℝ)|=(1891294299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569654779/5000000000 : ℝ)|^4659 ≤ (21302718438751/50000000000000 : ℝ)^3635
        have hw : |(2569654779/5000000000 : ℝ)|=(2569654779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676956369/1250000000 : ℝ)|^4659 ≤ (1423864222471/3125000000000 : ℝ)^3635
        have hw : |(676956369/1250000000 : ℝ)|=(676956369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_9 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314278853/2500000000 : ℝ)*x 0 + (-1732758627/10000000000 : ℝ)*x 1 + (270782551/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314278853/2500000000 : ℝ)^4659 ≤ (4386120011151/10000000000000 : ℝ)^3635 := by
    have hnat : (1314278853 : ℕ)^4659*10000000000000^3635 ≤ 4386120011151^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314278853 2500000000 4386120011151 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1732758627/10000000000 : ℝ)^4659 ≤ (10575144024417/100000000000000 : ℝ)^3635 := by
    have hnat : (1732758627 : ℕ)^4659*100000000000000^3635 ≤ 10575144024417^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732758627 10000000000 10575144024417 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270782551/500000000 : ℝ)^4659 ≤ (5695456981543/12500000000000 : ℝ)^3635 := by
    have hnat : (270782551 : ℕ)^4659*12500000000000^3635 ≤ 5695456981543^3635*500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270782551 500000000 5695456981543 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314278853/2500000000 : ℝ), (-1732758627/10000000000 : ℝ), (270782551/500000000 : ℝ)] ![(4386120011151/10000000000000 : ℝ), (10575144024417/100000000000000 : ℝ), (5695456981543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314278853/2500000000 : ℝ)|^4659 ≤ (4386120011151/10000000000000 : ℝ)^3635
        have hw : |(1314278853/2500000000 : ℝ)|=(1314278853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1732758627/10000000000 : ℝ)|^4659 ≤ (10575144024417/100000000000000 : ℝ)^3635
        have hw : |(-1732758627/10000000000 : ℝ)|=(1732758627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270782551/500000000 : ℝ)|^4659 ≤ (5695456981543/12500000000000 : ℝ)^3635
        have hw : |(270782551/500000000 : ℝ)|=(270782551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_10 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210284613/400000000 : ℝ)*x 0 + (1353912797/2500000000 : ℝ)*x 1 + (-1732758513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210284613/400000000 : ℝ)^4659 ≤ (43861199181173/100000000000000 : ℝ)^3635 := by
    have hnat : (210284613 : ℕ)^4659*100000000000000^3635 ≤ 43861199181173^3635*400000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210284613 400000000 43861199181173 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353912797/2500000000 : ℝ)^4659 ≤ (22781828831979/50000000000000 : ℝ)^3635 := by
    have hnat : (1353912797 : ℕ)^4659*50000000000000^3635 ≤ 22781828831979^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353912797 2500000000 22781828831979 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732758513/10000000000 : ℝ)^4659 ≤ (10575143132671/100000000000000 : ℝ)^3635 := by
    have hnat : (1732758513 : ℕ)^4659*100000000000000^3635 ≤ 10575143132671^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732758513 10000000000 10575143132671 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210284613/400000000 : ℝ), (1353912797/2500000000 : ℝ), (-1732758513/10000000000 : ℝ)] ![(43861199181173/100000000000000 : ℝ), (22781828831979/50000000000000 : ℝ), (10575143132671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210284613/400000000 : ℝ)|^4659 ≤ (43861199181173/100000000000000 : ℝ)^3635
        have hw : |(210284613/400000000 : ℝ)|=(210284613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353912797/2500000000 : ℝ)|^4659 ≤ (22781828831979/50000000000000 : ℝ)^3635
        have hw : |(1353912797/2500000000 : ℝ)|=(1353912797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1732758513/10000000000 : ℝ)|^4659 ≤ (10575143132671/100000000000000 : ℝ)^3635
        have hw : |(-1732758513/10000000000 : ℝ)|=(1732758513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_11 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2246087437/5000000000 : ℝ)*x 0 + (1029482197/2500000000 : ℝ)*x 1 + (1029482219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246087437/5000000000 : ℝ)^4659 ≤ (35855165703241/100000000000000 : ℝ)^3635 := by
    have hnat : (2246087437 : ℕ)^4659*100000000000000^3635 ≤ 35855165703241^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246087437 5000000000 35855165703241 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029482197/2500000000 : ℝ)^4659 ≤ (32072416707587/100000000000000 : ℝ)^3635 := by
    have hnat : (1029482197 : ℕ)^4659*100000000000000^3635 ≤ 32072416707587^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029482197 2500000000 32072416707587 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029482219/2500000000 : ℝ)^4659 ≤ (32072417586051/100000000000000 : ℝ)^3635 := by
    have hnat : (1029482219 : ℕ)^4659*100000000000000^3635 ≤ 32072417586051^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029482219 2500000000 32072417586051 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246087437/5000000000 : ℝ), (1029482197/2500000000 : ℝ), (1029482219/2500000000 : ℝ)] ![(35855165703241/100000000000000 : ℝ), (32072416707587/100000000000000 : ℝ), (32072417586051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246087437/5000000000 : ℝ)|^4659 ≤ (35855165703241/100000000000000 : ℝ)^3635
        have hw : |(2246087437/5000000000 : ℝ)|=(2246087437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029482197/2500000000 : ℝ)|^4659 ≤ (32072416707587/100000000000000 : ℝ)^3635
        have hw : |(1029482197/2500000000 : ℝ)|=(1029482197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029482219/2500000000 : ℝ)|^4659 ≤ (32072417586051/100000000000000 : ℝ)^3635
        have hw : |(1029482219/2500000000 : ℝ)|=(1029482219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_12 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1655092999/10000000000 : ℝ)*x 0 + (1374535601/2500000000 : ℝ)*x 1 + (1307545837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655092999/10000000000 : ℝ)^4659 ≤ (9971494788829/100000000000000 : ℝ)^3635 := by
    have hnat : (1655092999 : ℕ)^4659*100000000000000^3635 ≤ 9971494788829^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655092999 10000000000 9971494788829 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374535601/2500000000 : ℝ)^4659 ≤ (46455095976813/100000000000000 : ℝ)^3635 := by
    have hnat : (1374535601 : ℕ)^4659*100000000000000^3635 ≤ 46455095976813^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374535601 2500000000 46455095976813 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307545837/2500000000 : ℝ)^4659 ≤ (21786704607189/50000000000000 : ℝ)^3635 := by
    have hnat : (1307545837 : ℕ)^4659*50000000000000^3635 ≤ 21786704607189^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307545837 2500000000 21786704607189 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1655092999/10000000000 : ℝ), (1374535601/2500000000 : ℝ), (1307545837/2500000000 : ℝ)] ![(9971494788829/100000000000000 : ℝ), (46455095976813/100000000000000 : ℝ), (21786704607189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1655092999/10000000000 : ℝ)|^4659 ≤ (9971494788829/100000000000000 : ℝ)^3635
        have hw : |(-1655092999/10000000000 : ℝ)|=(1655092999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374535601/2500000000 : ℝ)|^4659 ≤ (46455095976813/100000000000000 : ℝ)^3635
        have hw : |(1374535601/2500000000 : ℝ)|=(1374535601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307545837/2500000000 : ℝ)|^4659 ≤ (21786704607189/50000000000000 : ℝ)^3635
        have hw : |(1307545837/2500000000 : ℝ)|=(1307545837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_13 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692789353/5000000000 : ℝ)*x 0 + (-1810486707/10000000000 : ℝ)*x 1 + (5230183597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692789353/5000000000 : ℝ)^4659 ≤ (9047925535923/20000000000000 : ℝ)^3635 := by
    have hnat : (2692789353 : ℕ)^4659*20000000000000^3635 ≤ 9047925535923^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692789353 5000000000 9047925535923 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1810486707/10000000000 : ℝ)^4659 ≤ (2237392087153/20000000000000 : ℝ)^3635 := by
    have hnat : (1810486707 : ℕ)^4659*20000000000000^3635 ≤ 2237392087153^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810486707 10000000000 2237392087153 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230183597/10000000000 : ℝ)^4659 ≤ (21786705936609/50000000000000 : ℝ)^3635 := by
    have hnat : (5230183597 : ℕ)^4659*50000000000000^3635 ≤ 21786705936609^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230183597 10000000000 21786705936609 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692789353/5000000000 : ℝ), (-1810486707/10000000000 : ℝ), (5230183597/10000000000 : ℝ)] ![(9047925535923/20000000000000 : ℝ), (2237392087153/20000000000000 : ℝ), (21786705936609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692789353/5000000000 : ℝ)|^4659 ≤ (9047925535923/20000000000000 : ℝ)^3635
        have hw : |(2692789353/5000000000 : ℝ)|=(2692789353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1810486707/10000000000 : ℝ)|^4659 ≤ (2237392087153/20000000000000 : ℝ)^3635
        have hw : |(-1810486707/10000000000 : ℝ)|=(1810486707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230183597/10000000000 : ℝ)|^4659 ≤ (21786705936609/50000000000000 : ℝ)^3635
        have hw : |(5230183597/10000000000 : ℝ)|=(5230183597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_14 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385578317/10000000000 : ℝ)*x 0 + (5230182861/10000000000 : ℝ)*x 1 + (-1810488227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385578317/10000000000 : ℝ)^4659 ≤ (45239623491443/100000000000000 : ℝ)^3635 := by
    have hnat : (5385578317 : ℕ)^4659*100000000000000^3635 ≤ 45239623491443^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385578317 10000000000 45239623491443 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230182861/10000000000 : ℝ)^4659 ≤ (10893351003539/25000000000000 : ℝ)^3635 := by
    have hnat : (5230182861 : ℕ)^4659*25000000000000^3635 ≤ 10893351003539^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230182861 10000000000 10893351003539 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1810488227/10000000000 : ℝ)^4659 ≤ (11186972473609/100000000000000 : ℝ)^3635 := by
    have hnat : (1810488227 : ℕ)^4659*100000000000000^3635 ≤ 11186972473609^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810488227 10000000000 11186972473609 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385578317/10000000000 : ℝ), (5230182861/10000000000 : ℝ), (-1810488227/10000000000 : ℝ)] ![(45239623491443/100000000000000 : ℝ), (10893351003539/25000000000000 : ℝ), (11186972473609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385578317/10000000000 : ℝ)|^4659 ≤ (45239623491443/100000000000000 : ℝ)^3635
        have hw : |(5385578317/10000000000 : ℝ)|=(5385578317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230182861/10000000000 : ℝ)|^4659 ≤ (10893351003539/25000000000000 : ℝ)^3635
        have hw : |(5230182861/10000000000 : ℝ)|=(5230182861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1810488227/10000000000 : ℝ)|^4659 ≤ (11186972473609/100000000000000 : ℝ)^3635
        have hw : |(-1810488227/10000000000 : ℝ)|=(1810488227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_box_15 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3994376519/10000000000 : ℝ)*x 0 + (1091705263/2500000000 : ℝ)*x 1 + (4366821371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3994376519/10000000000 : ℝ)^4659 ≤ (3855537652241/12500000000000 : ℝ)^3635 := by
    have hnat : (3994376519 : ℕ)^4659*12500000000000^3635 ≤ 3855537652241^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3994376519 10000000000 3855537652241 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091705263/2500000000 : ℝ)^4659 ≤ (34577847761161/100000000000000 : ℝ)^3635 := by
    have hnat : (1091705263 : ℕ)^4659*100000000000000^3635 ≤ 34577847761161^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091705263 2500000000 34577847761161 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4366821371/10000000000 : ℝ)^4659 ≤ (17288925499337/50000000000000 : ℝ)^3635 := by
    have hnat : (4366821371 : ℕ)^4659*50000000000000^3635 ≤ 17288925499337^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366821371 10000000000 17288925499337 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3994376519/10000000000 : ℝ), (1091705263/2500000000 : ℝ), (4366821371/10000000000 : ℝ)] ![(3855537652241/12500000000000 : ℝ), (34577847761161/100000000000000 : ℝ), (17288925499337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3994376519/10000000000 : ℝ)|^4659 ≤ (3855537652241/12500000000000 : ℝ)^3635
        have hw : |(3994376519/10000000000 : ℝ)|=(3994376519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091705263/2500000000 : ℝ)|^4659 ≤ (34577847761161/100000000000000 : ℝ)^3635
        have hw : |(1091705263/2500000000 : ℝ)|=(1091705263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4366821371/10000000000 : ℝ)|^4659 ≤ (17288925499337/50000000000000 : ℝ)^3635
        have hw : |(4366821371/10000000000 : ℝ)|=(4366821371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1581_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7981/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11791/20000 : ℝ) ∧ (81029/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43217/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2789/25000 : ℝ) ^ (4657/1024 : ℝ) ≤ (232905676347653/5000000000000000000 : ℝ) := by
    have hpowers : (2789/25000 : ℝ)^4657 ≤ (232905676347653/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2789 : ℕ)^4657*5000000000000000000^1024 ≤ 232905676347653^1024*25000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2789 25000 232905676347653 5000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2789/25000 : ℝ)) (X := (232905676347653/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4657/1024 : ℝ) ≤ (20687541171520043/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4657 ≤ (20687541171520043/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4657*100000000000000000000^1024 ≤ 20687541171520043^1024*25000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 20687541171520043 100000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (20687541171520043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500232905676347653/2500000000000000000 : ℝ) ≤ (1250025605190729/1250000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (2500232905676347653/2500000000000000000 : ℝ)^1024 ≤ (1250025605190729/1250000000000000 : ℝ)^4657 := by
      have hnat : (2500232905676347653 : ℕ)^1024*1250000000000000^4657 ≤ 1250025605190729^4657*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500232905676347653 2500000000000000000 1250025605190729 1250000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250025605190729/1250000000000000 : ℝ)) (X := (2500232905676347653/2500000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025345654698473103/100000000000000000000 : ℝ) ≤ (10000557255420189/10000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (100025345654698473103/100000000000000000000 : ℝ)^1024 ≤ (10000557255420189/10000000000000000 : ℝ)^4657 := by
      have hnat : (100025345654698473103 : ℕ)^1024*10000000000000000^4657 ≤ 10000557255420189^4657*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025345654698473103 100000000000000000000 10000557255420189 10000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000557255420189/10000000000000000 : ℝ)) (X := (100025345654698473103/100000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020687541171520043/50000000000000000000 : ℝ) ≤ (5000454834657273/5000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (50020687541171520043/50000000000000000000 : ℝ)^1024 ≤ (5000454834657273/5000000000000000 : ℝ)^4657 := by
      have hnat : (50020687541171520043 : ℕ)^1024*5000000000000000^4657 ≤ 5000454834657273^4657*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020687541171520043 50000000000000000000 5000454834657273 5000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000454834657273/5000000000000000 : ℝ)) (X := (50020687541171520043/50000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(232905676347653/5000000000000000000 : ℝ) ≤ ((5409127936914113439/5410000000000000000 : ℝ)+2*(352413894357/432800000000000 : ℝ)*(2789/25000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (5409127936914113439/5410000000000000000 : ℝ)+2*(352413894357/432800000000000 : ℝ)*(2789/25000 : ℝ)=(1250025605190729/1250000000000000 : ℝ) by norm_num, show 1+2*(232905676347653/5000000000000000000 : ℝ)=(2500232905676347653/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20687541171520043/100000000000000000000 : ℝ)+(232905676347653/5000000000000000000 : ℝ) ≤ ((5409127936914113439/5410000000000000000 : ℝ)+(352413894357/432800000000000 : ℝ)*((3871/25000 : ℝ)+(2789/25000 : ℝ)))^(4657/1024 : ℝ) := by
    rw [show (5409127936914113439/5410000000000000000 : ℝ)+(352413894357/432800000000000 : ℝ)*((3871/25000 : ℝ)+(2789/25000 : ℝ))=(10000557255420189/10000000000000000 : ℝ) by norm_num, show 1+(20687541171520043/100000000000000000000 : ℝ)+(232905676347653/5000000000000000000 : ℝ)=(100025345654698473103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20687541171520043/100000000000000000000 : ℝ) ≤ ((5409127936914113439/5410000000000000000 : ℝ)+2*(352413894357/432800000000000 : ℝ)*(3871/25000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (5409127936914113439/5410000000000000000 : ℝ)+2*(352413894357/432800000000000 : ℝ)*(3871/25000 : ℝ)=(5000454834657273/5000000000000000 : ℝ) by norm_num, show 1+2*(20687541171520043/100000000000000000000 : ℝ)=(50020687541171520043/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5409127936914113439/5410000000000000000 : ℝ)*(X 1 0+X 2 0)+(352413894357/432800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5409127936914113439/5410000000000000000 : ℝ)) (alpha := (352413894357/432800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5409127936914113439/5410000000000000000 : ℝ)*(X 0 1+X 2 1)+(352413894357/432800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5409127936914113439/5410000000000000000 : ℝ)) (alpha := (352413894357/432800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5409127936914113439/5410000000000000000 : ℝ)*(X 0 2+X 1 2)+(352413894357/432800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5409127936914113439/5410000000000000000 : ℝ)) (alpha := (352413894357/432800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1568635377/10000000000 : ℝ)*X 0 0+(5395416887/10000000000 : ℝ)*X 0 1+(5395416397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054226587/2000000000 : ℝ)*X 1 0+(-1741461647/10000000000 : ℝ)*X 1 1+(2697708391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5147591/9765625 : ℝ)*X 2 0+(1348854189/2500000000 : ℝ)*X 2 1+(-1741461341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4438978329/10000000000 : ℝ)*X 0 0+(4145115999/10000000000 : ℝ)*X 0 1+(4145116197/10000000000 : ℝ)*X 0 2+(4438978329/10000000000 : ℝ)*X 1 0+(4145115999/10000000000 : ℝ)*X 1 1+(4145116197/10000000000 : ℝ)*X 1 2+(4438978329/10000000000 : ℝ)*X 2 0+(4145115999/10000000000 : ℝ)*X 2 1+(4145116197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-989069773/5000000000 : ℝ)*X 0 0+(5245232501/10000000000 : ℝ)*X 0 1+(5245232641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5375153411/10000000000 : ℝ)*X 1 0+(-1804354497/10000000000 : ℝ)*X 1 1+(81956753/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375153039/10000000000 : ℝ)*X 2 0+(5245232643/10000000000 : ℝ)*X 2 1+(-225544299/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4035656081/10000000000 : ℝ)*X 0 0+(4346650883/10000000000 : ℝ)*X 0 1+(869330203/2000000000 : ℝ)*X 0 2+(4035656081/10000000000 : ℝ)*X 1 0+(4346650883/10000000000 : ℝ)*X 1 1+(869330203/2000000000 : ℝ)*X 1 2+(4035656081/10000000000 : ℝ)*X 2 0+(4346650883/10000000000 : ℝ)*X 2 1+(869330203/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1891294299/10000000000 : ℝ)*X 0 0+(2569654779/5000000000 : ℝ)*X 0 1+(676956369/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314278853/2500000000 : ℝ)*X 1 0+(-1732758627/10000000000 : ℝ)*X 1 1+(270782551/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((210284613/400000000 : ℝ)*X 2 0+(1353912797/2500000000 : ℝ)*X 2 1+(-1732758513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2246087437/5000000000 : ℝ)*X 0 0+(1029482197/2500000000 : ℝ)*X 0 1+(1029482219/2500000000 : ℝ)*X 0 2+(2246087437/5000000000 : ℝ)*X 1 0+(1029482197/2500000000 : ℝ)*X 1 1+(1029482219/2500000000 : ℝ)*X 1 2+(2246087437/5000000000 : ℝ)*X 2 0+(1029482197/2500000000 : ℝ)*X 2 1+(1029482219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1655092999/10000000000 : ℝ)*X 0 0+(1374535601/2500000000 : ℝ)*X 0 1+(1307545837/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2692789353/5000000000 : ℝ)*X 1 0+(-1810486707/10000000000 : ℝ)*X 1 1+(5230183597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5385578317/10000000000 : ℝ)*X 2 0+(5230182861/10000000000 : ℝ)*X 2 1+(-1810488227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3994376519/10000000000 : ℝ)*X 0 0+(1091705263/2500000000 : ℝ)*X 0 1+(4366821371/10000000000 : ℝ)*X 0 2+(3994376519/10000000000 : ℝ)*X 1 0+(1091705263/2500000000 : ℝ)*X 1 1+(4366821371/10000000000 : ℝ)*X 1 2+(3994376519/10000000000 : ℝ)*X 2 0+(1091705263/2500000000 : ℝ)*X 2 1+(4366821371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7981/12500 : ℝ) ≤ (-69081347724312829476928377/108200000000000000000000000 : ℝ) := by norm_num
    linear_combination (3890707/10000000000000 : ℝ)*(lower0) + (53626969/100000000000000 : ℝ)*(lower3) + (59620763/100000000000000 : ℝ)*(lower4) + (58086419806169/2500000000000 : ℝ)*(major0) + (58086419806169/2500000000000 : ℝ)*(major1) + (58086419806169/2500000000000 : ℝ)*(major2) + (778867461/12500000000000 : ℝ)*(sp1) + (187299691/100000000000000 : ℝ)*(sp2) + (65853220649243/2000000000000 : ℝ)*(sp4) + (329265522308231/10000000000000 : ℝ)*(sp5) + (823165316680577/25000000000000 : ℝ)*(sp6) + (343882542896331/25000000000000 : ℝ)*(sp7) + (421559849/100000000000000 : ℝ)*(sp12) + (790281509/20000000000000 : ℝ)*(sp15) + (1375534122992869/100000000000000 : ℝ)*(f.failure) + (1646330727010999/50000000000000 : ℝ)*(f.sum) + (386662069527/108200000000000000000000000 : ℝ)*base66 + (70932563655282309/13525000000000000000000000000000 : ℝ)*base68 + (4576588423757309/13525000000000000000000000000000 : ℝ)*base70 + (35583273440942691/13525000000000000000000000000000 : ℝ)*base71 + (1600310877933/541000000000000000000000000 : ℝ)*base74 + (104427676593892691/13525000000000000000000000000000 : ℝ)*base75 + (34871094738292691/13525000000000000000000000000000 : ℝ)*base77 + (123813261831632309/13525000000000000000000000000000 : ℝ)*base80 + (3619083271/4328000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (16037991/10000000000000000000000 : ℝ)*base90 + (16037991/10000000000000000000000 : ℝ)*base92 + (16037991/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11791/20000 : ℝ) ≤ (9967505310581491823078275134069/16906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14469359/100000000000000 : ℝ)*(upper0) + (16494617/20000000000000 : ℝ)*(lower1) + (140429197/100000000000000 : ℝ)*(upper4) + (300556495598193/12500000000000 : ℝ)*(major0) + (300556495598193/12500000000000 : ℝ)*(major1) + (300556495598193/12500000000000 : ℝ)*(major2) + (841440190180397/25000000000000 : ℝ)*(sp0) + (3365764131651961/100000000000000 : ℝ)*(sp1) + (3365758688291301/100000000000000 : ℝ)*(sp2) + (711741616992153/50000000000000 : ℝ)*(sp3) + (472810699/20000000000000 : ℝ)*(sp5) + (1951853539/25000000000000 : ℝ)*(sp6) + (211753967/12500000000000 : ℝ)*(sp7) + (5734983867/100000000000000 : ℝ)*(sp8) + (711742464008021/50000000000000 : ℝ)*(f.failure) + (210360405981591/6250000000000 : ℝ)*(f.sum) + (598717684537/338125000000000000000000000 : ℝ)*base65 + (747741835416178227/67625000000000000000000000000000 : ℝ)*base67 + (820303851423928227/67625000000000000000000000000000 : ℝ)*base69 + (927180962517928227/67625000000000000000000000000000 : ℝ)*base71 + (62259849352099/2705000000000000000000000000 : ℝ)*base74 + (490533871348678227/67625000000000000000000000000000 : ℝ)*base75 + (163390705141928227/67625000000000000000000000000000 : ℝ)*base77 + (607894376884071773/67625000000000000000000000000000 : ℝ)*base80 + (1309456081489/676250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (44337719/5000000000000000000000 : ℝ)*base90 + (44337719/5000000000000000000000 : ℝ)*base92 + (44337719/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81029/100000 : ℝ) ≤ (219190557326526164199283771719069/270500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2314921/10000000000000 : ℝ)*(upper0) + (9262563/25000000000000 : ℝ)*(upper2) + (56457823/100000000000000 : ℝ)*(upper4) + (1294665019825139/50000000000000 : ℝ)*(major0) + (1294665019825139/50000000000000 : ℝ)*(major1) + (2589330039650279/100000000000000 : ℝ)*(major2) + (215384921/20000000000000 : ℝ)*(sp0) + (13238134981/100000000000000 : ℝ)*(sp1) + (6192721251/12500000000000 : ℝ)*(sp2) + (3911146913/20000000000000 : ℝ)*(sp3) + (361871191527189/10000000000000 : ℝ)*(sp8) + (3618699754061513/100000000000000 : ℝ)*(sp9) + (1809331725213243/50000000000000 : ℝ)*(sp10) + (1532916988260857/100000000000000 : ℝ)*(sp11) + (766468271997711/50000000000000 : ℝ)*(f.failure) + (1809356496098247/50000000000000 : ℝ)*(f.sum) + (300132672854609/43280000000000000000000000000 : ℝ)*base65 + (4351878377285538229/270500000000000000000000000000000 : ℝ)*base68 + (3485439596672425519/541000000000000000000000000000000 : ℝ)*base70 + (14324943009289538229/270500000000000000000000000000000 : ℝ)*base72 + (149330892552191/43280000000000000000000000000 : ℝ)*base74 + (414051099589425519/541000000000000000000000000000000 : ℝ)*base76 + (634694726585230521/270500000000000000000000000000000 : ℝ)*base77 + (1861556052675769479/270500000000000000000000000000000 : ℝ)*base80 + (20324789461997/10820000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (50003371/5000000000000000000000 : ℝ)*base89 + (50003371/5000000000000000000000 : ℝ)*base91 + (3371/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-43217/50000 : ℝ) ≤ (-116898097586055753361163284831323/135250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373328747/100000000000000 : ℝ)*(lower0) + (59329121/50000000000000 : ℝ)*(lower1) + (592005739/100000000000000 : ℝ)*(lower4) + (1315045171527831/50000000000000 : ℝ)*(major0) + (1315045171527831/50000000000000 : ℝ)*(major1) + (2630090343055663/100000000000000 : ℝ)*(major2) + (2915897027/50000000000000 : ℝ)*(sp0) + (40566530161/50000000000000 : ℝ)*(sp5) + (127434855973/25000000000000 : ℝ)*(sp6) + (48881289817/50000000000000 : ℝ)*(sp7) + (373191774912427/10000000000000 : ℝ)*(sp12) + (1865921223929001/50000000000000 : ℝ)*(sp13) + (116606682546701/3125000000000 : ℝ)*(sp14) + (194621214733203/12500000000000 : ℝ)*(sp15) + (778533740222629/50000000000000 : ℝ)*(f.failure) + (932980895229581/25000000000000 : ℝ)*(f.sum) + (42927429634573/8656000000000000000000000000 : ℝ)*base65 + (563671665893810441/270500000000000000000000000000000 : ℝ)*base68 + (1413828472723030057/541000000000000000000000000000000 : ℝ)*base69 + (276086734428189559/270500000000000000000000000000000 : ℝ)*base71 + (26519265783373/8656000000000000000000000000 : ℝ)*base73 + (1216794641696969943/541000000000000000000000000000000 : ℝ)*base76 + (672453333960541691/270500000000000000000000000000000 : ℝ)*base78 + (23657416598541691/270500000000000000000000000000000 : ℝ)*base80 + (42410766004853/10820000000000000000000000000 : ℝ)*base82 + (14142631/5000000000000000000000 : ℝ)*base90 + (14142631/5000000000000000000000 : ℝ)*base92 + (64142631/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1581_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7981/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11791/20000 : ℝ) else (81029/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43217/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1581_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1581_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7981/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11791/20000 : ℝ) else (81029/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43217/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1581_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7981/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11791/20000 : ℝ) else (81029/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43217/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1581_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
