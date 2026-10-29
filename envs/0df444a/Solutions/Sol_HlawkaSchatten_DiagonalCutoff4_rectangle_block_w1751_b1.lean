-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1751_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:33.134713+00:00
-- url     : https://prove2.me/submissions/f0798ac9-c475-4959-b2b9-454b1250d366

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
theorem support_rectangle_w1751_s3_0 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1216607093/10000000000 : ℝ)*x 0 + (5495663713/10000000000 : ℝ)*x 1 + (2540710287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1216607093/10000000000 : ℝ)^5791 ≤ (7738046754391/100000000000000 : ℝ)^4767 := by
    have hnat : (1216607093 : ℕ)^5791*100000000000000^4767 ≤ 7738046754391^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216607093 10000000000 7738046754391 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495663713/10000000000 : ℝ)^5791 ≤ (4832521983833/10000000000000 : ℝ)^4767 := by
    have hnat : (5495663713 : ℕ)^5791*10000000000000^4767 ≤ 4832521983833^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495663713 10000000000 4832521983833 10000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540710287/5000000000 : ℝ)^5791 ≤ (5492091674609/12500000000000 : ℝ)^4767 := by
    have hnat : (2540710287 : ℕ)^5791*12500000000000^4767 ≤ 5492091674609^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540710287 5000000000 5492091674609 12500000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1216607093/10000000000 : ℝ), (5495663713/10000000000 : ℝ), (2540710287/5000000000 : ℝ)] ![(7738046754391/100000000000000 : ℝ), (4832521983833/10000000000000 : ℝ), (5492091674609/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1216607093/10000000000 : ℝ)|^5791 ≤ (7738046754391/100000000000000 : ℝ)^4767
        have hw : |(-1216607093/10000000000 : ℝ)|=(1216607093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495663713/10000000000 : ℝ)|^5791 ≤ (4832521983833/10000000000000 : ℝ)^4767
        have hw : |(5495663713/10000000000 : ℝ)|=(5495663713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540710287/5000000000 : ℝ)|^5791 ≤ (5492091674609/12500000000000 : ℝ)^4767
        have hw : |(2540710287/5000000000 : ℝ)|=(2540710287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s3_1 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2667790489/5000000000 : ℝ)*x 0 + (-89578927/625000000 : ℝ)*x 1 + (2540710263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2667790489/5000000000 : ℝ)^5791 ≤ (23310284949223/50000000000000 : ℝ)^4767 := by
    have hnat : (2667790489 : ℕ)^5791*50000000000000^4767 ≤ 23310284949223^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667790489 5000000000 23310284949223 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89578927/625000000 : ℝ)^5791 ≤ (2360674297693/25000000000000 : ℝ)^4767 := by
    have hnat : (89578927 : ℕ)^5791*25000000000000^4767 ≤ 2360674297693^4767*625000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89578927 625000000 2360674297693 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540710263/5000000000 : ℝ)^5791 ≤ (10984183223171/25000000000000 : ℝ)^4767 := by
    have hnat : (2540710263 : ℕ)^5791*25000000000000^4767 ≤ 10984183223171^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540710263 5000000000 10984183223171 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2667790489/5000000000 : ℝ), (-89578927/625000000 : ℝ), (2540710263/5000000000 : ℝ)] ![(23310284949223/50000000000000 : ℝ), (2360674297693/25000000000000 : ℝ), (10984183223171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2667790489/5000000000 : ℝ)|^5791 ≤ (23310284949223/50000000000000 : ℝ)^4767
        have hw : |(2667790489/5000000000 : ℝ)|=(2667790489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89578927/625000000 : ℝ)|^5791 ≤ (2360674297693/25000000000000 : ℝ)^4767
        have hw : |(-89578927/625000000 : ℝ)|=(89578927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540710263/5000000000 : ℝ)|^5791 ≤ (10984183223171/25000000000000 : ℝ)^4767
        have hw : |(2540710263/5000000000 : ℝ)|=(2540710263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s3_2 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2667790301/5000000000 : ℝ)*x 0 + (15879441/31250000 : ℝ)*x 1 + (-179157819/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2667790301/5000000000 : ℝ)^5791 ≤ (932411318147/2000000000000 : ℝ)^4767 := by
    have hnat : (2667790301 : ℕ)^5791*2000000000000^4767 ≤ 932411318147^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667790301 5000000000 932411318147 2000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15879441/31250000 : ℝ)^5791 ≤ (43936739132007/100000000000000 : ℝ)^4767 := by
    have hnat : (15879441 : ℕ)^5791*100000000000000^4767 ≤ 43936739132007^4767*31250000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15879441 31250000 43936739132007 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179157819/1250000000 : ℝ)^5791 ≤ (9442694949799/100000000000000 : ℝ)^4767 := by
    have hnat : (179157819 : ℕ)^5791*100000000000000^4767 ≤ 9442694949799^4767*1250000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179157819 1250000000 9442694949799 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2667790301/5000000000 : ℝ), (15879441/31250000 : ℝ), (-179157819/1250000000 : ℝ)] ![(932411318147/2000000000000 : ℝ), (43936739132007/100000000000000 : ℝ), (9442694949799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2667790301/5000000000 : ℝ)|^5791 ≤ (932411318147/2000000000000 : ℝ)^4767
        have hw : |(2667790301/5000000000 : ℝ)|=(2667790301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15879441/31250000 : ℝ)|^5791 ≤ (43936739132007/100000000000000 : ℝ)^4767
        have hw : |(15879441/31250000 : ℝ)|=(15879441/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179157819/1250000000 : ℝ)|^5791 ≤ (9442694949799/100000000000000 : ℝ)^4767
        have hw : |(-179157819/1250000000 : ℝ)|=(179157819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s3_3 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4018795361/10000000000 : ℝ)*x 0 + (1683477469/5000000000 : ℝ)*x 1 + (1183384759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4018795361/10000000000 : ℝ)^5791 ≤ (33040884914889/100000000000000 : ℝ)^4767 := by
    have hnat : (4018795361 : ℕ)^5791*100000000000000^4767 ≤ 33040884914889^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018795361 10000000000 33040884914889 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1683477469/5000000000 : ℝ)^5791 ≤ (26649132544261/100000000000000 : ℝ)^4767 := by
    have hnat : (1683477469 : ℕ)^5791*100000000000000^4767 ≤ 26649132544261^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683477469 5000000000 26649132544261 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183384759/2500000000 : ℝ)^5791 ≤ (403099825287/1000000000000 : ℝ)^4767 := by
    have hnat : (1183384759 : ℕ)^5791*1000000000000^4767 ≤ 403099825287^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183384759 2500000000 403099825287 1000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4018795361/10000000000 : ℝ), (1683477469/5000000000 : ℝ), (1183384759/2500000000 : ℝ)] ![(33040884914889/100000000000000 : ℝ), (26649132544261/100000000000000 : ℝ), (403099825287/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4018795361/10000000000 : ℝ)|^5791 ≤ (33040884914889/100000000000000 : ℝ)^4767
        have hw : |(4018795361/10000000000 : ℝ)|=(4018795361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1683477469/5000000000 : ℝ)|^5791 ≤ (26649132544261/100000000000000 : ℝ)^4767
        have hw : |(1683477469/5000000000 : ℝ)|=(1683477469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1183384759/2500000000 : ℝ)|^5791 ≤ (403099825287/1000000000000 : ℝ)^4767
        have hw : |(1183384759/2500000000 : ℝ)|=(1183384759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s3_4 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1216955739/10000000000 : ℝ)*x 0 + (636021141/1250000000 : ℝ)*x 1 + (5488773753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1216955739/10000000000 : ℝ)^5791 ≤ (1548148138323/20000000000000 : ℝ)^4767 := by
    have hnat : (1216955739 : ℕ)^5791*20000000000000^4767 ≤ 1548148138323^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216955739 10000000000 1548148138323 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636021141/1250000000 : ℝ)^5791 ≤ (44007629715857/100000000000000 : ℝ)^4767 := by
    have hnat : (636021141 : ℕ)^5791*100000000000000^4767 ≤ 44007629715857^4767*1250000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636021141 1250000000 44007629715857 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488773753/10000000000 : ℝ)^5791 ≤ (2412581479239/5000000000000 : ℝ)^4767 := by
    have hnat : (5488773753 : ℕ)^5791*5000000000000^4767 ≤ 2412581479239^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488773753 10000000000 2412581479239 5000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1216955739/10000000000 : ℝ), (636021141/1250000000 : ℝ), (5488773753/10000000000 : ℝ)] ![(1548148138323/20000000000000 : ℝ), (44007629715857/100000000000000 : ℝ), (2412581479239/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1216955739/10000000000 : ℝ)|^5791 ≤ (1548148138323/20000000000000 : ℝ)^4767
        have hw : |(-1216955739/10000000000 : ℝ)|=(1216955739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636021141/1250000000 : ℝ)|^5791 ≤ (44007629715857/100000000000000 : ℝ)^4767
        have hw : |(636021141/1250000000 : ℝ)|=(636021141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488773753/10000000000 : ℝ)|^5791 ≤ (2412581479239/5000000000000 : ℝ)^4767
        have hw : |(5488773753/10000000000 : ℝ)|=(5488773753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s3_5 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306449783/2500000000 : ℝ)*x 0 + (-64119363/625000000 : ℝ)*x 1 + (2744386883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306449783/2500000000 : ℝ)^5791 ≤ (22728933486591/50000000000000 : ℝ)^4767 := by
    have hnat : (1306449783 : ℕ)^5791*50000000000000^4767 ≤ 22728933486591^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306449783 2500000000 22728933486591 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64119363/625000000 : ℝ)^5791 ≤ (3145251644297/50000000000000 : ℝ)^4767 := by
    have hnat : (64119363 : ℕ)^5791*50000000000000^4767 ≤ 3145251644297^4767*625000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64119363 625000000 3145251644297 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744386883/5000000000 : ℝ)^5791 ≤ (12062907430903/25000000000000 : ℝ)^4767 := by
    have hnat : (2744386883 : ℕ)^5791*25000000000000^4767 ≤ 12062907430903^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744386883 5000000000 12062907430903 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306449783/2500000000 : ℝ), (-64119363/625000000 : ℝ), (2744386883/5000000000 : ℝ)] ![(22728933486591/50000000000000 : ℝ), (3145251644297/50000000000000 : ℝ), (12062907430903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306449783/2500000000 : ℝ)|^5791 ≤ (22728933486591/50000000000000 : ℝ)^4767
        have hw : |(1306449783/2500000000 : ℝ)|=(1306449783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64119363/625000000 : ℝ)|^5791 ≤ (3145251644297/50000000000000 : ℝ)^4767
        have hw : |(-64119363/625000000 : ℝ)|=(64119363/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744386883/5000000000 : ℝ)|^5791 ≤ (12062907430903/25000000000000 : ℝ)^4767
        have hw : |(2744386883/5000000000 : ℝ)|=(2744386883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s3_6 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306449783/2500000000 : ℝ)*x 0 + (1097754751/2000000000 : ℝ)*x 1 + (-1025909823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306449783/2500000000 : ℝ)^5791 ≤ (22728933486591/50000000000000 : ℝ)^4767 := by
    have hnat : (1306449783 : ℕ)^5791*50000000000000^4767 ≤ 22728933486591^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306449783 2500000000 22728933486591 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097754751/2000000000 : ℝ)^5791 ≤ (48251629606139/100000000000000 : ℝ)^4767 := by
    have hnat : (1097754751 : ℕ)^5791*100000000000000^4767 ≤ 48251629606139^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097754751 2000000000 48251629606139 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025909823/10000000000 : ℝ)^5791 ≤ (3145251700163/50000000000000 : ℝ)^4767 := by
    have hnat : (1025909823 : ℕ)^5791*50000000000000^4767 ≤ 3145251700163^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025909823 10000000000 3145251700163 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306449783/2500000000 : ℝ), (1097754751/2000000000 : ℝ), (-1025909823/10000000000 : ℝ)] ![(22728933486591/50000000000000 : ℝ), (48251629606139/100000000000000 : ℝ), (3145251700163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306449783/2500000000 : ℝ)|^5791 ≤ (22728933486591/50000000000000 : ℝ)^4767
        have hw : |(1306449783/2500000000 : ℝ)|=(1306449783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097754751/2000000000 : ℝ)|^5791 ≤ (48251629606139/100000000000000 : ℝ)^4767
        have hw : |(1097754751/2000000000 : ℝ)|=(1097754751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025909823/10000000000 : ℝ)|^5791 ≤ (3145251700163/50000000000000 : ℝ)^4767
        have hw : |(-1025909823/10000000000 : ℝ)|=(1025909823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s3_7 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1004986079/2500000000 : ℝ)*x 0 + (1177819203/2500000000 : ℝ)*x 1 + (3389685281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004986079/2500000000 : ℝ)^5791 ≤ (33052360650789/100000000000000 : ℝ)^4767 := by
    have hnat : (1004986079 : ℕ)^5791*100000000000000^4767 ≤ 33052360650789^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004986079 2500000000 33052360650789 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177819203/2500000000 : ℝ)^5791 ≤ (40079793879309/100000000000000 : ℝ)^4767 := by
    have hnat : (1177819203 : ℕ)^5791*100000000000000^4767 ≤ 40079793879309^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177819203 2500000000 40079793879309 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3389685281/10000000000 : ℝ)^5791 ≤ (26867845449959/100000000000000 : ℝ)^4767 := by
    have hnat : (3389685281 : ℕ)^5791*100000000000000^4767 ≤ 26867845449959^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389685281 10000000000 26867845449959 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1004986079/2500000000 : ℝ), (1177819203/2500000000 : ℝ), (3389685281/10000000000 : ℝ)] ![(33052360650789/100000000000000 : ℝ), (40079793879309/100000000000000 : ℝ), (26867845449959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1004986079/2500000000 : ℝ)|^5791 ≤ (33052360650789/100000000000000 : ℝ)^4767
        have hw : |(1004986079/2500000000 : ℝ)|=(1004986079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1177819203/2500000000 : ℝ)|^5791 ≤ (40079793879309/100000000000000 : ℝ)^4767
        have hw : |(1177819203/2500000000 : ℝ)|=(1177819203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3389685281/10000000000 : ℝ)|^5791 ≤ (26867845449959/100000000000000 : ℝ)^4767
        have hw : |(3389685281/10000000000 : ℝ)|=(3389685281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1751_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9053/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4489/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2263/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2263/25000 : ℝ) ^ (5775/1024 : ℝ) ≤ (261478509411/200000000000000000 : ℝ) := by
    have hpowers : (2263/25000 : ℝ)^5775 ≤ (261478509411/200000000000000000 : ℝ)^1024 := by
      have hnat : (2263 : ℕ)^5775*200000000000000000^1024 ≤ 261478509411^1024*25000^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 25000 261478509411 200000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/25000 : ℝ)) (X := (261478509411/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17957/100000 : ℝ) ^ (5775/1024 : ℝ) ≤ (12158241249471/195312500000000000 : ℝ) := by
    have hpowers : (17957/100000 : ℝ)^5775 ≤ (12158241249471/195312500000000000 : ℝ)^1024 := by
      have hnat : (17957 : ℕ)^5775*195312500000000000^1024 ≤ 12158241249471^1024*100000^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17957 100000 12158241249471 195312500000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17957/100000 : ℝ)) (X := (12158241249471/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (100000261478509411/100000000000000000 : ℝ) ≤ (2500001159106951/2500000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (100000261478509411/100000000000000000 : ℝ)^1024 ≤ (2500001159106951/2500000000000000 : ℝ)^5775 := by
      have hnat : (100000261478509411 : ℕ)^1024*2500000000000000^5775 ≤ 2500001159106951^5775*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000261478509411 100000000000000000 2500001159106951 2500000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001159106951/2500000000000000 : ℝ)) (X := (100000261478509411/100000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25001588939693608663/25000000000000000000 : ℝ) ≤ (2000022538967409/2000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (25001588939693608663/25000000000000000000 : ℝ)^1024 ≤ (2000022538967409/2000000000000000 : ℝ)^5775 := by
      have hnat : (25001588939693608663 : ℕ)^1024*2000000000000000^5775 ≤ 2000022538967409^5775*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001588939693608663 25000000000000000000 2000022538967409 2000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000022538967409/2000000000000000 : ℝ)) (X := (25001588939693608663/25000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (97668408241249471/97656250000000000 : ℝ) ≤ (5000110376623143/5000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (97668408241249471/97656250000000000 : ℝ)^1024 ≤ (5000110376623143/5000000000000000 : ℝ)^5775 := by
      have hnat : (97668408241249471 : ℕ)^1024*5000000000000000^5775 ≤ 5000110376623143^5775*97656250000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97668408241249471 97656250000000000 5000110376623143 5000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000110376623143/5000000000000000 : ℝ)) (X := (97668408241249471/97656250000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(261478509411/200000000000000000 : ℝ) ≤ ((22262021249487173889/22262500000000000000 : ℝ)+2*(108058409241/890500000000000 : ℝ)*(2263/25000 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (22262021249487173889/22262500000000000000 : ℝ)+2*(108058409241/890500000000000 : ℝ)*(2263/25000 : ℝ)=(2500001159106951/2500000000000000 : ℝ) by norm_num, show 1+2*(261478509411/200000000000000000 : ℝ)=(100000261478509411/100000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12158241249471/195312500000000000 : ℝ)+(261478509411/200000000000000000 : ℝ) ≤ ((22262021249487173889/22262500000000000000 : ℝ)+(108058409241/890500000000000 : ℝ)*((17957/100000 : ℝ)+(2263/25000 : ℝ)))^(5775/1024 : ℝ) := by
    rw [show (22262021249487173889/22262500000000000000 : ℝ)+(108058409241/890500000000000 : ℝ)*((17957/100000 : ℝ)+(2263/25000 : ℝ))=(2000022538967409/2000000000000000 : ℝ) by norm_num, show 1+(12158241249471/195312500000000000 : ℝ)+(261478509411/200000000000000000 : ℝ)=(25001588939693608663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12158241249471/195312500000000000 : ℝ) ≤ ((22262021249487173889/22262500000000000000 : ℝ)+2*(108058409241/890500000000000 : ℝ)*(17957/100000 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (22262021249487173889/22262500000000000000 : ℝ)+2*(108058409241/890500000000000 : ℝ)*(17957/100000 : ℝ)=(5000110376623143/5000000000000000 : ℝ) by norm_num, show 1+2*(12158241249471/195312500000000000 : ℝ)=(97668408241249471/97656250000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22262021249487173889/22262500000000000000 : ℝ)*(X 1 0+X 2 0)+(108058409241/890500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (2263/25000 : ℝ)) (hi := (17957/100000 : ℝ)) (c := (22262021249487173889/22262500000000000000 : ℝ)) (alpha := (108058409241/890500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22262021249487173889/22262500000000000000 : ℝ)*(X 0 1+X 2 1)+(108058409241/890500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (2263/25000 : ℝ)) (hi := (17957/100000 : ℝ)) (c := (22262021249487173889/22262500000000000000 : ℝ)) (alpha := (108058409241/890500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22262021249487173889/22262500000000000000 : ℝ)*(X 0 2+X 1 2)+(108058409241/890500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (2263/25000 : ℝ)) (hi := (17957/100000 : ℝ)) (c := (22262021249487173889/22262500000000000000 : ℝ)) (alpha := (108058409241/890500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1216607093/10000000000 : ℝ)*X 0 0+(5495663713/10000000000 : ℝ)*X 0 1+(2540710287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2667790489/5000000000 : ℝ)*X 1 0+(-89578927/625000000 : ℝ)*X 1 1+(2540710263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2667790301/5000000000 : ℝ)*X 2 0+(15879441/31250000 : ℝ)*X 2 1+(-179157819/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4018795361/10000000000 : ℝ)*X 0 0+(1683477469/5000000000 : ℝ)*X 0 1+(1183384759/2500000000 : ℝ)*X 0 2+(4018795361/10000000000 : ℝ)*X 1 0+(1683477469/5000000000 : ℝ)*X 1 1+(1183384759/2500000000 : ℝ)*X 1 2+(4018795361/10000000000 : ℝ)*X 2 0+(1683477469/5000000000 : ℝ)*X 2 1+(1183384759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1216955739/10000000000 : ℝ)*X 0 0+(636021141/1250000000 : ℝ)*X 0 1+(5488773753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1306449783/2500000000 : ℝ)*X 1 0+(-64119363/625000000 : ℝ)*X 1 1+(2744386883/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1306449783/2500000000 : ℝ)*X 2 0+(1097754751/2000000000 : ℝ)*X 2 1+(-1025909823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1004986079/2500000000 : ℝ)*X 0 0+(1177819203/2500000000 : ℝ)*X 0 1+(3389685281/10000000000 : ℝ)*X 0 2+(1004986079/2500000000 : ℝ)*X 1 0+(1177819203/2500000000 : ℝ)*X 1 1+(3389685281/10000000000 : ℝ)*X 1 2+(1004986079/2500000000 : ℝ)*X 2 0+(1177819203/2500000000 : ℝ)*X 2 1+(3389685281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (654128617195519849968744861/85625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11741293/800000000000 : ℝ)*(base19) + (1063431337/100000000000000 : ℝ)*(base23) + (124911607/100000000000000 : ℝ)*(lower2) + (247947237/100000000000000 : ℝ)*(upper3) + (102969587/50000000000000 : ℝ)*(upper5) + (1572910638211807/100000000000000 : ℝ)*(major0) + (1572910638211807/100000000000000 : ℝ)*(major1) + (1572910638211807/100000000000000 : ℝ)*(major2) + (75439120056669/3125000000000 : ℝ)*(sp0) + (301757715520309/12500000000000 : ℝ)*(sp1) + (60351553209819/2500000000000 : ℝ)*(sp2) + (731754433354497/100000000000000 : ℝ)*(sp3) + (11350010689/100000000000000 : ℝ)*(sp4) + (3396596399/100000000000000 : ℝ)*(sp7) + (45734864371931/6250000000000 : ℝ)*(f.failure) + (2414063191824097/100000000000000 : ℝ)*(f.sum) + (112727501196837/44525000000000000000000000000 : ℝ)*base65 + (14765030251396582423/2226250000000000000000000000000000 : ℝ)*base67 + (11299158056709082423/2226250000000000000000000000000000 : ℝ)*base69 + (21632933923262832423/2226250000000000000000000000000000 : ℝ)*base71 + (104258575306737/44525000000000000000000000000 : ℝ)*base73 + (1399473423705332423/2226250000000000000000000000000000 : ℝ)*base75 + (10259949006982832423/2226250000000000000000000000000000 : ℝ)*base77 + (15618088947366582423/2226250000000000000000000000000000 : ℝ)*base79 + (13898282955839/5565625000000000000000000000 : ℝ)*base81 + (1698687/125000000000000000000 : ℝ)*base90 + (1698687/125000000000000000000 : ℝ)*base92 + (1698687/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6876786648864644660073430203/556562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (788576647/50000000000000 : ℝ)*(base19) + (1697191133/100000000000000 : ℝ)*(base23) + (451436587/100000000000000 : ℝ)*(lower1) + (263298027/100000000000000 : ℝ)*(upper3) + (27264151/50000000000000 : ℝ)*(lower4) + (32025399/12500000000000 : ℝ)*(upper5) + (1626437578168109/100000000000000 : ℝ)*(major0) + (1626437578168109/100000000000000 : ℝ)*(major1) + (1626437578168109/100000000000000 : ℝ)*(major2) + (373517491/50000000000000 : ℝ)*(sp2) + (249621482760703/10000000000000 : ℝ)*(sp4) + (312026656306717/12500000000000 : ℝ)*(sp5) + (624053095845229/25000000000000 : ℝ)*(sp6) + (189164979217119/25000000000000 : ℝ)*(sp7) + (189164979217119/25000000000000 : ℝ)*(f.failure) + (249621482760703/10000000000000 : ℝ)*(f.sum) + (119860003782881/44525000000000000000000000000 : ℝ)*base66 + (58876830176100969099/2226250000000000000000000000000000 : ℝ)*base68 + (5798437408993469099/2226250000000000000000000000000000 : ℝ)*base70 + (35841133995720969099/2226250000000000000000000000000000 : ℝ)*base72 + (57498225468331/44525000000000000000000000000 : ℝ)*base74 + (66129014819424030901/2226250000000000000000000000000000 : ℝ)*base75 + (10991346185275969099/2226250000000000000000000000000000 : ℝ)*base78 + (20274789628575969099/2226250000000000000000000000000000 : ℝ)*base80 + (36875450681669/44525000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1091837/500000000000000000000 : ℝ)*base89 + (1091837/500000000000000000000 : ℝ)*base91 + (1091837/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1751_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9053/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4489/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1751_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1751_box_0 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8315511/100000000 : ℝ)*x 0 + (1084843593/2000000000 : ℝ)*x 1 + (5424217497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8315511/100000000 : ℝ)^5791 ≤ (4873827125403/100000000000000 : ℝ)^4767 := by
    have hnat : (8315511 : ℕ)^5791*100000000000000^4767 ≤ 4873827125403^4767*100000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8315511 100000000 4873827125403 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084843593/2000000000 : ℝ)^5791 ≤ (951261778479/2000000000000 : ℝ)^4767 := by
    have hnat : (1084843593 : ℕ)^5791*2000000000000^4767 ≤ 951261778479^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084843593 2000000000 951261778479 2000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424217497/10000000000 : ℝ)^5791 ≤ (47563083938697/100000000000000 : ℝ)^4767 := by
    have hnat : (5424217497 : ℕ)^5791*100000000000000^4767 ≤ 47563083938697^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424217497 10000000000 47563083938697 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8315511/100000000 : ℝ), (1084843593/2000000000 : ℝ), (5424217497/10000000000 : ℝ)] ![(4873827125403/100000000000000 : ℝ), (951261778479/2000000000000 : ℝ), (47563083938697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8315511/100000000 : ℝ)|^5791 ≤ (4873827125403/100000000000000 : ℝ)^4767
        have hw : |(-8315511/100000000 : ℝ)|=(8315511/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084843593/2000000000 : ℝ)|^5791 ≤ (951261778479/2000000000000 : ℝ)^4767
        have hw : |(1084843593/2000000000 : ℝ)|=(1084843593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424217497/10000000000 : ℝ)|^5791 ≤ (47563083938697/100000000000000 : ℝ)^4767
        have hw : |(5424217497/10000000000 : ℝ)|=(5424217497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_1 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194313887/10000000000 : ℝ)*x 0 + (-580566359/5000000000 : ℝ)*x 1 + (135605451/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194313887/10000000000 : ℝ)^5791 ≤ (45125368038279/100000000000000 : ℝ)^4767 := by
    have hnat : (5194313887 : ℕ)^5791*100000000000000^4767 ≤ 45125368038279^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194313887 10000000000 45125368038279 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580566359/5000000000 : ℝ)^5791 ≤ (731154222343/10000000000000 : ℝ)^4767 := by
    have hnat : (580566359 : ℕ)^5791*10000000000000^4767 ≤ 731154222343^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580566359 5000000000 731154222343 10000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135605451/250000000 : ℝ)^5791 ≤ (47563089722869/100000000000000 : ℝ)^4767 := by
    have hnat : (135605451 : ℕ)^5791*100000000000000^4767 ≤ 47563089722869^4767*250000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135605451 250000000 47563089722869 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194313887/10000000000 : ℝ), (-580566359/5000000000 : ℝ), (135605451/250000000 : ℝ)] ![(45125368038279/100000000000000 : ℝ), (731154222343/10000000000000 : ℝ), (47563089722869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194313887/10000000000 : ℝ)|^5791 ≤ (45125368038279/100000000000000 : ℝ)^4767
        have hw : |(5194313887/10000000000 : ℝ)|=(5194313887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-580566359/5000000000 : ℝ)|^5791 ≤ (731154222343/10000000000000 : ℝ)^4767
        have hw : |(-580566359/5000000000 : ℝ)|=(580566359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135605451/250000000 : ℝ)|^5791 ≤ (47563089722869/100000000000000 : ℝ)^4767
        have hw : |(135605451/250000000 : ℝ)|=(135605451/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_2 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259715727/500000000 : ℝ)*x 0 + (5424217563/10000000000 : ℝ)*x 1 + (-1161132481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259715727/500000000 : ℝ)^5791 ≤ (9025074985957/20000000000000 : ℝ)^4767 := by
    have hnat : (259715727 : ℕ)^5791*20000000000000^4767 ≤ 9025074985957^4767*500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259715727 500000000 9025074985957 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424217563/10000000000 : ℝ)^5791 ≤ (23781542320873/50000000000000 : ℝ)^4767 := by
    have hnat : (5424217563 : ℕ)^5791*50000000000000^4767 ≤ 23781542320873^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424217563 10000000000 23781542320873 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161132481/10000000000 : ℝ)^5791 ≤ (913942551311/12500000000000 : ℝ)^4767 := by
    have hnat : (1161132481 : ℕ)^5791*12500000000000^4767 ≤ 913942551311^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161132481 10000000000 913942551311 12500000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259715727/500000000 : ℝ), (5424217563/10000000000 : ℝ), (-1161132481/10000000000 : ℝ)] ![(9025074985957/20000000000000 : ℝ), (23781542320873/50000000000000 : ℝ), (913942551311/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259715727/500000000 : ℝ)|^5791 ≤ (9025074985957/20000000000000 : ℝ)^4767
        have hw : |(259715727/500000000 : ℝ)|=(259715727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424217563/10000000000 : ℝ)|^5791 ≤ (23781542320873/50000000000000 : ℝ)^4767
        have hw : |(5424217563/10000000000 : ℝ)|=(5424217563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1161132481/10000000000 : ℝ)|^5791 ≤ (913942551311/12500000000000 : ℝ)^4767
        have hw : |(-1161132481/10000000000 : ℝ)|=(1161132481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_3 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4544988967/10000000000 : ℝ)*x 0 + (948669339/2500000000 : ℝ)*x 1 + (1897338781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4544988967/10000000000 : ℝ)^5791 ≤ (19183922581383/50000000000000 : ℝ)^4767 := by
    have hnat : (4544988967 : ℕ)^5791*50000000000000^4767 ≤ 19183922581383^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544988967 10000000000 19183922581383 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948669339/2500000000 : ℝ)^5791 ≤ (30816076392319/100000000000000 : ℝ)^4767 := by
    have hnat : (948669339 : ℕ)^5791*100000000000000^4767 ≤ 30816076392319^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948669339 2500000000 30816076392319 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1897338781/5000000000 : ℝ)^5791 ≤ (15408039212287/50000000000000 : ℝ)^4767 := by
    have hnat : (1897338781 : ℕ)^5791*50000000000000^4767 ≤ 15408039212287^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897338781 5000000000 15408039212287 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4544988967/10000000000 : ℝ), (948669339/2500000000 : ℝ), (1897338781/5000000000 : ℝ)] ![(19183922581383/50000000000000 : ℝ), (30816076392319/100000000000000 : ℝ), (15408039212287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4544988967/10000000000 : ℝ)|^5791 ≤ (19183922581383/50000000000000 : ℝ)^4767
        have hw : |(4544988967/10000000000 : ℝ)|=(4544988967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(948669339/2500000000 : ℝ)|^5791 ≤ (30816076392319/100000000000000 : ℝ)^4767
        have hw : |(948669339/2500000000 : ℝ)|=(948669339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1897338781/5000000000 : ℝ)|^5791 ≤ (15408039212287/50000000000000 : ℝ)^4767
        have hw : |(1897338781/5000000000 : ℝ)|=(1897338781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_4 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1641338129/10000000000 : ℝ)*x 0 + (5128665079/10000000000 : ℝ)*x 1 + (2564331503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1641338129/10000000000 : ℝ)^5791 ≤ (11133062142563/100000000000000 : ℝ)^4767 := by
    have hnat : (1641338129 : ℕ)^5791*100000000000000^4767 ≤ 11133062142563^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641338129 10000000000 11133062142563 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128665079/10000000000 : ℝ)^5791 ≤ (22216739915867/50000000000000 : ℝ)^4767 := by
    have hnat : (5128665079 : ℕ)^5791*50000000000000^4767 ≤ 22216739915867^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128665079 10000000000 22216739915867 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564331503/5000000000 : ℝ)^5791 ≤ (44433458013797/100000000000000 : ℝ)^4767 := by
    have hnat : (2564331503 : ℕ)^5791*100000000000000^4767 ≤ 44433458013797^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564331503 5000000000 44433458013797 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1641338129/10000000000 : ℝ), (5128665079/10000000000 : ℝ), (2564331503/5000000000 : ℝ)] ![(11133062142563/100000000000000 : ℝ), (22216739915867/50000000000000 : ℝ), (44433458013797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1641338129/10000000000 : ℝ)|^5791 ≤ (11133062142563/100000000000000 : ℝ)^4767
        have hw : |(-1641338129/10000000000 : ℝ)|=(1641338129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128665079/10000000000 : ℝ)|^5791 ≤ (22216739915867/50000000000000 : ℝ)^4767
        have hw : |(5128665079/10000000000 : ℝ)|=(5128665079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564331503/5000000000 : ℝ)|^5791 ≤ (44433458013797/100000000000000 : ℝ)^4767
        have hw : |(2564331503/5000000000 : ℝ)|=(2564331503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_5 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392077487/10000000000 : ℝ)*x 0 + (-647352583/5000000000 : ℝ)*x 1 + (20033851/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392077487/10000000000 : ℝ)^5791 ≤ (47220938758847/100000000000000 : ℝ)^4767 := by
    have hnat : (5392077487 : ℕ)^5791*100000000000000^4767 ≤ 47220938758847^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392077487 10000000000 47220938758847 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647352583/5000000000 : ℝ)^5791 ≤ (2086393305317/25000000000000 : ℝ)^4767 := by
    have hnat : (647352583 : ℕ)^5791*25000000000000^4767 ≤ 2086393305317^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647352583 5000000000 2086393305317 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20033851/39062500 : ℝ)^5791 ≤ (22216744004757/50000000000000 : ℝ)^4767 := by
    have hnat : (20033851 : ℕ)^5791*50000000000000^4767 ≤ 22216744004757^4767*39062500^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20033851 39062500 22216744004757 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392077487/10000000000 : ℝ), (-647352583/5000000000 : ℝ), (20033851/39062500 : ℝ)] ![(47220938758847/100000000000000 : ℝ), (2086393305317/25000000000000 : ℝ), (22216744004757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392077487/10000000000 : ℝ)|^5791 ≤ (47220938758847/100000000000000 : ℝ)^4767
        have hw : |(5392077487/10000000000 : ℝ)|=(5392077487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-647352583/5000000000 : ℝ)|^5791 ≤ (2086393305317/25000000000000 : ℝ)^4767
        have hw : |(-647352583/5000000000 : ℝ)|=(647352583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20033851/39062500 : ℝ)|^5791 ≤ (22216744004757/50000000000000 : ℝ)^4767
        have hw : |(20033851/39062500 : ℝ)|=(20033851/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_6 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392079107/10000000000 : ℝ)*x 0 + (641083001/1250000000 : ℝ)*x 1 + (-1294705449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392079107/10000000000 : ℝ)^5791 ≤ (11805238998369/25000000000000 : ℝ)^4767 := by
    have hnat : (5392079107 : ℕ)^5791*25000000000000^4767 ≤ 11805238998369^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392079107 10000000000 11805238998369 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641083001/1250000000 : ℝ)^5791 ≤ (44433468559659/100000000000000 : ℝ)^4767 := by
    have hnat : (641083001 : ℕ)^5791*100000000000000^4767 ≤ 44433468559659^4767*1250000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641083001 1250000000 44433468559659 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294705449/10000000000 : ℝ)^5791 ≤ (8345575437321/100000000000000 : ℝ)^4767 := by
    have hnat : (1294705449 : ℕ)^5791*100000000000000^4767 ≤ 8345575437321^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294705449 10000000000 8345575437321 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392079107/10000000000 : ℝ), (641083001/1250000000 : ℝ), (-1294705449/10000000000 : ℝ)] ![(11805238998369/25000000000000 : ℝ), (44433468559659/100000000000000 : ℝ), (8345575437321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392079107/10000000000 : ℝ)|^5791 ≤ (11805238998369/25000000000000 : ℝ)^4767
        have hw : |(5392079107/10000000000 : ℝ)|=(5392079107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641083001/1250000000 : ℝ)|^5791 ≤ (44433468559659/100000000000000 : ℝ)^4767
        have hw : |(641083001/1250000000 : ℝ)|=(641083001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1294705449/10000000000 : ℝ)|^5791 ≤ (8345575437321/100000000000000 : ℝ)^4767
        have hw : |(-1294705449/10000000000 : ℝ)|=(1294705449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_7 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (345580003/1000000000 : ℝ)*x 0 + (867431711/2000000000 : ℝ)*x 1 + (2168579263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345580003/1000000000 : ℝ)^5791 ≤ (6876448071709/25000000000000 : ℝ)^4767 := by
    have hnat : (345580003 : ℕ)^5791*25000000000000^4767 ≤ 6876448071709^4767*1000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345580003 1000000000 6876448071709 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (867431711/2000000000 : ℝ)^5791 ≤ (36247103995691/100000000000000 : ℝ)^4767 := by
    have hnat : (867431711 : ℕ)^5791*100000000000000^4767 ≤ 36247103995691^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867431711 2000000000 36247103995691 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168579263/5000000000 : ℝ)^5791 ≤ (18123551850633/50000000000000 : ℝ)^4767 := by
    have hnat : (2168579263 : ℕ)^5791*50000000000000^4767 ≤ 18123551850633^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168579263 5000000000 18123551850633 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(345580003/1000000000 : ℝ), (867431711/2000000000 : ℝ), (2168579263/5000000000 : ℝ)] ![(6876448071709/25000000000000 : ℝ), (36247103995691/100000000000000 : ℝ), (18123551850633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(345580003/1000000000 : ℝ)|^5791 ≤ (6876448071709/25000000000000 : ℝ)^4767
        have hw : |(345580003/1000000000 : ℝ)|=(345580003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(867431711/2000000000 : ℝ)|^5791 ≤ (36247103995691/100000000000000 : ℝ)^4767
        have hw : |(867431711/2000000000 : ℝ)|=(867431711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2168579263/5000000000 : ℝ)|^5791 ≤ (18123551850633/50000000000000 : ℝ)^4767
        have hw : |(2168579263/5000000000 : ℝ)|=(2168579263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_8 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1465201351/10000000000 : ℝ)*x 0 + (4903519977/10000000000 : ℝ)*x 1 + (1097272909/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1465201351/10000000000 : ℝ)^5791 ≤ (2424731154729/25000000000000 : ℝ)^4767 := by
    have hnat : (1465201351 : ℕ)^5791*25000000000000^4767 ≤ 2424731154729^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465201351 10000000000 2424731154729 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4903519977/10000000000 : ℝ)^5791 ≤ (42075173363051/100000000000000 : ℝ)^4767 := by
    have hnat : (4903519977 : ℕ)^5791*100000000000000^4767 ≤ 42075173363051^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4903519977 10000000000 42075173363051 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097272909/2000000000 : ℝ)^5791 ≤ (48225902007691/100000000000000 : ℝ)^4767 := by
    have hnat : (1097272909 : ℕ)^5791*100000000000000^4767 ≤ 48225902007691^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097272909 2000000000 48225902007691 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1465201351/10000000000 : ℝ), (4903519977/10000000000 : ℝ), (1097272909/2000000000 : ℝ)] ![(2424731154729/25000000000000 : ℝ), (42075173363051/100000000000000 : ℝ), (48225902007691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1465201351/10000000000 : ℝ)|^5791 ≤ (2424731154729/25000000000000 : ℝ)^4767
        have hw : |(-1465201351/10000000000 : ℝ)|=(1465201351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4903519977/10000000000 : ℝ)|^5791 ≤ (42075173363051/100000000000000 : ℝ)^4767
        have hw : |(4903519977/10000000000 : ℝ)|=(4903519977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097272909/2000000000 : ℝ)|^5791 ≤ (48225902007691/100000000000000 : ℝ)^4767
        have hw : |(1097272909/2000000000 : ℝ)|=(1097272909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_9 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152795587/10000000000 : ℝ)*x 0 + (-113163147/1000000000 : ℝ)*x 1 + (5486367333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152795587/10000000000 : ℝ)^5791 ≤ (11171894276819/25000000000000 : ℝ)^4767 := by
    have hnat : (5152795587 : ℕ)^5791*25000000000000^4767 ≤ 11171894276819^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152795587 10000000000 11171894276819 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113163147/1000000000 : ℝ)^5791 ≤ (7086491101069/100000000000000 : ℝ)^4767 := by
    have hnat : (113163147 : ℕ)^5791*100000000000000^4767 ≤ 7086491101069^4767*1000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113163147 1000000000 7086491101069 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486367333/10000000000 : ℝ)^5791 ≤ (4822593177893/10000000000000 : ℝ)^4767 := by
    have hnat : (5486367333 : ℕ)^5791*10000000000000^4767 ≤ 4822593177893^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486367333 10000000000 4822593177893 10000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152795587/10000000000 : ℝ), (-113163147/1000000000 : ℝ), (5486367333/10000000000 : ℝ)] ![(11171894276819/25000000000000 : ℝ), (7086491101069/100000000000000 : ℝ), (4822593177893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152795587/10000000000 : ℝ)|^5791 ≤ (11171894276819/25000000000000 : ℝ)^4767
        have hw : |(5152795587/10000000000 : ℝ)|=(5152795587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113163147/1000000000 : ℝ)|^5791 ≤ (7086491101069/100000000000000 : ℝ)^4767
        have hw : |(-113163147/1000000000 : ℝ)|=(113163147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486367333/10000000000 : ℝ)|^5791 ≤ (4822593177893/10000000000000 : ℝ)^4767
        have hw : |(5486367333/10000000000 : ℝ)|=(5486367333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_10 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576398211/5000000000 : ℝ)*x 0 + (5486366949/10000000000 : ℝ)*x 1 + (-282907713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576398211/5000000000 : ℝ)^5791 ≤ (44687585904361/100000000000000 : ℝ)^4767 := by
    have hnat : (2576398211 : ℕ)^5791*100000000000000^4767 ≤ 44687585904361^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576398211 5000000000 44687585904361 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486366949/10000000000 : ℝ)^5791 ≤ (48225927678443/100000000000000 : ℝ)^4767 := by
    have hnat : (5486366949 : ℕ)^5791*100000000000000^4767 ≤ 48225927678443^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486366949 10000000000 48225927678443 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282907713/2500000000 : ℝ)^5791 ≤ (3543243199857/50000000000000 : ℝ)^4767 := by
    have hnat : (282907713 : ℕ)^5791*50000000000000^4767 ≤ 3543243199857^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282907713 2500000000 3543243199857 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576398211/5000000000 : ℝ), (5486366949/10000000000 : ℝ), (-282907713/2500000000 : ℝ)] ![(44687585904361/100000000000000 : ℝ), (48225927678443/100000000000000 : ℝ), (3543243199857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576398211/5000000000 : ℝ)|^5791 ≤ (44687585904361/100000000000000 : ℝ)^4767
        have hw : |(2576398211/5000000000 : ℝ)|=(2576398211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486366949/10000000000 : ℝ)|^5791 ≤ (48225927678443/100000000000000 : ℝ)^4767
        have hw : |(5486366949/10000000000 : ℝ)|=(5486366949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282907713/2500000000 : ℝ)|^5791 ≤ (3543243199857/50000000000000 : ℝ)^4767
        have hw : |(-282907713/2500000000 : ℝ)|=(282907713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_11 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4763445589/10000000000 : ℝ)*x 0 + (920044999/2500000000 : ℝ)*x 1 + (368017933/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4763445589/10000000000 : ℝ)^5791 ≤ (40619578670833/100000000000000 : ℝ)^4767 := by
    have hnat : (4763445589 : ℕ)^5791*100000000000000^4767 ≤ 40619578670833^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4763445589 10000000000 40619578670833 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920044999/2500000000 : ℝ)^5791 ≤ (29690213919343/100000000000000 : ℝ)^4767 := by
    have hnat : (920044999 : ℕ)^5791*100000000000000^4767 ≤ 29690213919343^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920044999 2500000000 29690213919343 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368017933/1000000000 : ℝ)^5791 ≤ (29690207392143/100000000000000 : ℝ)^4767 := by
    have hnat : (368017933 : ℕ)^5791*100000000000000^4767 ≤ 29690207392143^4767*1000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368017933 1000000000 29690207392143 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4763445589/10000000000 : ℝ), (920044999/2500000000 : ℝ), (368017933/1000000000 : ℝ)] ![(40619578670833/100000000000000 : ℝ), (29690213919343/100000000000000 : ℝ), (29690207392143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4763445589/10000000000 : ℝ)|^5791 ≤ (40619578670833/100000000000000 : ℝ)^4767
        have hw : |(4763445589/10000000000 : ℝ)|=(4763445589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(920044999/2500000000 : ℝ)|^5791 ≤ (29690213919343/100000000000000 : ℝ)^4767
        have hw : |(920044999/2500000000 : ℝ)|=(920044999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368017933/1000000000 : ℝ)|^5791 ≤ (29690207392143/100000000000000 : ℝ)^4767
        have hw : |(368017933/1000000000 : ℝ)|=(368017933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_12 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-993914299/10000000000 : ℝ)*x 0 + (5636165891/10000000000 : ℝ)*x 1 + (1274639961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993914299/10000000000 : ℝ)^5791 ≤ (1513245249753/25000000000000 : ℝ)^4767 := by
    have hnat : (993914299 : ℕ)^5791*25000000000000^4767 ≤ 1513245249753^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993914299 10000000000 1513245249753 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5636165891/10000000000 : ℝ)^5791 ≤ (24915095525599/50000000000000 : ℝ)^4767 := by
    have hnat : (5636165891 : ℕ)^5791*50000000000000^4767 ≤ 24915095525599^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636165891 10000000000 24915095525599 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274639961/2500000000 : ℝ)^5791 ≤ (1764673117059/4000000000000 : ℝ)^4767 := by
    have hnat : (1274639961 : ℕ)^5791*4000000000000^4767 ≤ 1764673117059^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274639961 2500000000 1764673117059 4000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993914299/10000000000 : ℝ), (5636165891/10000000000 : ℝ), (1274639961/2500000000 : ℝ)] ![(1513245249753/25000000000000 : ℝ), (24915095525599/50000000000000 : ℝ), (1764673117059/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993914299/10000000000 : ℝ)|^5791 ≤ (1513245249753/25000000000000 : ℝ)^4767
        have hw : |(-993914299/10000000000 : ℝ)|=(993914299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5636165891/10000000000 : ℝ)|^5791 ≤ (24915095525599/50000000000000 : ℝ)^4767
        have hw : |(5636165891/10000000000 : ℝ)|=(5636165891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274639961/2500000000 : ℝ)|^5791 ≤ (1764673117059/4000000000000 : ℝ)^4767
        have hw : |(1274639961/2500000000 : ℝ)|=(1274639961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_13 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353074017/2500000000 : ℝ)*x 0 + (-1307650517/10000000000 : ℝ)*x 1 + (5098559541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353074017/2500000000 : ℝ)^5791 ≤ (47436123898521/100000000000000 : ℝ)^4767 := by
    have hnat : (1353074017 : ℕ)^5791*100000000000000^4767 ≤ 47436123898521^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353074017 2500000000 47436123898521 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307650517/10000000000 : ℝ)^5791 ≤ (8447051353073/100000000000000 : ℝ)^4767 := by
    have hnat : (1307650517 : ℕ)^5791*100000000000000^4767 ≤ 8447051353073^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307650517 10000000000 8447051353073 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098559541/10000000000 : ℝ)^5791 ≤ (44116824741487/100000000000000 : ℝ)^4767 := by
    have hnat : (5098559541 : ℕ)^5791*100000000000000^4767 ≤ 44116824741487^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098559541 10000000000 44116824741487 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353074017/2500000000 : ℝ), (-1307650517/10000000000 : ℝ), (5098559541/10000000000 : ℝ)] ![(47436123898521/100000000000000 : ℝ), (8447051353073/100000000000000 : ℝ), (44116824741487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353074017/2500000000 : ℝ)|^5791 ≤ (47436123898521/100000000000000 : ℝ)^4767
        have hw : |(1353074017/2500000000 : ℝ)|=(1353074017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307650517/10000000000 : ℝ)|^5791 ≤ (8447051353073/100000000000000 : ℝ)^4767
        have hw : |(-1307650517/10000000000 : ℝ)|=(1307650517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098559541/10000000000 : ℝ)|^5791 ≤ (44116824741487/100000000000000 : ℝ)^4767
        have hw : |(5098559541/10000000000 : ℝ)|=(5098559541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_14 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412295973/10000000000 : ℝ)*x 0 + (5098559933/10000000000 : ℝ)*x 1 + (-32691253/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412295973/10000000000 : ℝ)^5791 ≤ (9487224577407/20000000000000 : ℝ)^4767 := by
    have hnat : (5412295973 : ℕ)^5791*20000000000000^4767 ≤ 9487224577407^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412295973 10000000000 9487224577407 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5098559933/10000000000 : ℝ)^5791 ≤ (22058414431/50000000000 : ℝ)^4767 := by
    have hnat : (5098559933 : ℕ)^5791*50000000000^4767 ≤ 22058414431^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098559933 10000000000 22058414431 50000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32691253/250000000 : ℝ)^5791 ≤ (2111762059421/25000000000000 : ℝ)^4767 := by
    have hnat : (32691253 : ℕ)^5791*25000000000000^4767 ≤ 2111762059421^4767*250000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32691253 250000000 2111762059421 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412295973/10000000000 : ℝ), (5098559933/10000000000 : ℝ), (-32691253/250000000 : ℝ)] ![(9487224577407/20000000000000 : ℝ), (22058414431/50000000000 : ℝ), (2111762059421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412295973/10000000000 : ℝ)|^5791 ≤ (9487224577407/20000000000000 : ℝ)^4767
        have hw : |(5412295973/10000000000 : ℝ)|=(5412295973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5098559933/10000000000 : ℝ)|^5791 ≤ (22058414431/50000000000 : ℝ)^4767
        have hw : |(5098559933/10000000000 : ℝ)|=(5098559933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32691253/250000000 : ℝ)|^5791 ≤ (2111762059421/25000000000000 : ℝ)^4767
        have hw : |(-32691253/250000000 : ℝ)|=(32691253/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_box_15 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1669825981/5000000000 : ℝ)*x 0 + (4392190021/10000000000 : ℝ)*x 1 + (274511943/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1669825981/5000000000 : ℝ)^5791 ≤ (1649177537609/6250000000000 : ℝ)^4767 := by
    have hnat : (1669825981 : ℕ)^5791*6250000000000^4767 ≤ 1649177537609^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669825981 5000000000 1649177537609 6250000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392190021/10000000000 : ℝ)^5791 ≤ (36806574261137/100000000000000 : ℝ)^4767 := by
    have hnat : (4392190021 : ℕ)^5791*100000000000000^4767 ≤ 36806574261137^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392190021 10000000000 36806574261137 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274511943/625000000 : ℝ)^5791 ≤ (920164628083/2500000000000 : ℝ)^4767 := by
    have hnat : (274511943 : ℕ)^5791*2500000000000^4767 ≤ 920164628083^4767*625000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274511943 625000000 920164628083 2500000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1669825981/5000000000 : ℝ), (4392190021/10000000000 : ℝ), (274511943/625000000 : ℝ)] ![(1649177537609/6250000000000 : ℝ), (36806574261137/100000000000000 : ℝ), (920164628083/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1669825981/5000000000 : ℝ)|^5791 ≤ (1649177537609/6250000000000 : ℝ)^4767
        have hw : |(1669825981/5000000000 : ℝ)|=(1669825981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4392190021/10000000000 : ℝ)|^5791 ≤ (36806574261137/100000000000000 : ℝ)^4767
        have hw : |(4392190021/10000000000 : ℝ)|=(4392190021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274511943/625000000 : ℝ)|^5791 ≤ (920164628083/2500000000000 : ℝ)^4767
        have hw : |(274511943/625000000 : ℝ)|=(274511943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1751_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4489/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9053/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(17233/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58161/100000 : ℝ) ∧ (10203/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (46459/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4489/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9053/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4489/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9053/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4489/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9053/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4489/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9053/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4489/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9053/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4489/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9053/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9053/100000 : ℝ) ^ (5775/1024 : ℝ) ≤ (2616414595697/2000000000000000000 : ℝ) := by
    have hpowers : (9053/100000 : ℝ)^5775 ≤ (2616414595697/2000000000000000000 : ℝ)^1024 := by
      have hnat : (9053 : ℕ)^5775*2000000000000000000^1024 ≤ 2616414595697^1024*100000^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9053 100000 2616414595697 2000000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9053/100000 : ℝ)) (X := (2616414595697/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4489/25000 : ℝ) ^ (5775/1024 : ℝ) ≤ (388941544833651/6250000000000000000 : ℝ) := by
    have hpowers : (4489/25000 : ℝ)^5775 ≤ (388941544833651/6250000000000000000 : ℝ)^1024 := by
      have hnat : (4489 : ℕ)^5775*6250000000000000000^1024 ≤ 388941544833651^1024*25000^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4489 25000 388941544833651 6250000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4489/25000 : ℝ)) (X := (388941544833651/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000002616414595697/1000000000000000000 : ℝ) ≤ (2000000927863433/2000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (1000002616414595697/1000000000000000000 : ℝ)^1024 ≤ (2000000927863433/2000000000000000 : ℝ)^5775 := by
      have hnat : (1000002616414595697 : ℕ)^1024*2000000000000000^5775 ≤ 2000000927863433^5775*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000002616414595697 1000000000000000000 2000000927863433 2000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000927863433/2000000000000000 : ℝ)) (X := (1000002616414595697/1000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50003176942723561633/50000000000000000000 : ℝ) ≤ (10000112661621687/10000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (50003176942723561633/50000000000000000000 : ℝ)^1024 ≤ (10000112661621687/10000000000000000 : ℝ)^5775 := by
      have hnat : (50003176942723561633 : ℕ)^1024*10000000000000000^5775 ≤ 10000112661621687^5775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003176942723561633 50000000000000000000 10000112661621687 10000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000112661621687/10000000000000000 : ℝ)) (X := (50003176942723561633/50000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3125388941544833651/3125000000000000000 : ℝ) ≤ (10000220683926209/10000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (3125388941544833651/3125000000000000000 : ℝ)^1024 ≤ (10000220683926209/10000000000000000 : ℝ)^5775 := by
      have hnat : (3125388941544833651 : ℕ)^1024*10000000000000000^5775 ≤ 10000220683926209^5775*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125388941544833651 3125000000000000000 10000220683926209 10000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000220683926209/10000000000000000 : ℝ)) (X := (3125388941544833651/3125000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2616414595697/2000000000000000000 : ℝ) ≤ ((89028085451995044663/89030000000000000000 : ℝ)+2*(54011152261/445150000000000 : ℝ)*(9053/100000 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (89028085451995044663/89030000000000000000 : ℝ)+2*(54011152261/445150000000000 : ℝ)*(9053/100000 : ℝ)=(2000000927863433/2000000000000000 : ℝ) by norm_num, show 1+2*(2616414595697/2000000000000000000 : ℝ)=(1000002616414595697/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(388941544833651/6250000000000000000 : ℝ)+(2616414595697/2000000000000000000 : ℝ) ≤ ((89028085451995044663/89030000000000000000 : ℝ)+(54011152261/445150000000000 : ℝ)*((4489/25000 : ℝ)+(9053/100000 : ℝ)))^(5775/1024 : ℝ) := by
    rw [show (89028085451995044663/89030000000000000000 : ℝ)+(54011152261/445150000000000 : ℝ)*((4489/25000 : ℝ)+(9053/100000 : ℝ))=(10000112661621687/10000000000000000 : ℝ) by norm_num, show 1+(388941544833651/6250000000000000000 : ℝ)+(2616414595697/2000000000000000000 : ℝ)=(50003176942723561633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(388941544833651/6250000000000000000 : ℝ) ≤ ((89028085451995044663/89030000000000000000 : ℝ)+2*(54011152261/445150000000000 : ℝ)*(4489/25000 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (89028085451995044663/89030000000000000000 : ℝ)+2*(54011152261/445150000000000 : ℝ)*(4489/25000 : ℝ)=(10000220683926209/10000000000000000 : ℝ) by norm_num, show 1+2*(388941544833651/6250000000000000000 : ℝ)=(3125388941544833651/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89028085451995044663/89030000000000000000 : ℝ)*(X 1 0+X 2 0)+(54011152261/445150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (9053/100000 : ℝ)) (hi := (4489/25000 : ℝ)) (c := (89028085451995044663/89030000000000000000 : ℝ)) (alpha := (54011152261/445150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89028085451995044663/89030000000000000000 : ℝ)*(X 0 1+X 2 1)+(54011152261/445150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (9053/100000 : ℝ)) (hi := (4489/25000 : ℝ)) (c := (89028085451995044663/89030000000000000000 : ℝ)) (alpha := (54011152261/445150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89028085451995044663/89030000000000000000 : ℝ)*(X 0 2+X 1 2)+(54011152261/445150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (9053/100000 : ℝ)) (hi := (4489/25000 : ℝ)) (c := (89028085451995044663/89030000000000000000 : ℝ)) (alpha := (54011152261/445150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8315511/100000000 : ℝ)*X 0 0+(1084843593/2000000000 : ℝ)*X 0 1+(5424217497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5194313887/10000000000 : ℝ)*X 1 0+(-580566359/5000000000 : ℝ)*X 1 1+(135605451/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((259715727/500000000 : ℝ)*X 2 0+(5424217563/10000000000 : ℝ)*X 2 1+(-1161132481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4544988967/10000000000 : ℝ)*X 0 0+(948669339/2500000000 : ℝ)*X 0 1+(1897338781/5000000000 : ℝ)*X 0 2+(4544988967/10000000000 : ℝ)*X 1 0+(948669339/2500000000 : ℝ)*X 1 1+(1897338781/5000000000 : ℝ)*X 1 2+(4544988967/10000000000 : ℝ)*X 2 0+(948669339/2500000000 : ℝ)*X 2 1+(1897338781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1641338129/10000000000 : ℝ)*X 0 0+(5128665079/10000000000 : ℝ)*X 0 1+(2564331503/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5392077487/10000000000 : ℝ)*X 1 0+(-647352583/5000000000 : ℝ)*X 1 1+(20033851/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5392079107/10000000000 : ℝ)*X 2 0+(641083001/1250000000 : ℝ)*X 2 1+(-1294705449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((345580003/1000000000 : ℝ)*X 0 0+(867431711/2000000000 : ℝ)*X 0 1+(2168579263/5000000000 : ℝ)*X 0 2+(345580003/1000000000 : ℝ)*X 1 0+(867431711/2000000000 : ℝ)*X 1 1+(2168579263/5000000000 : ℝ)*X 1 2+(345580003/1000000000 : ℝ)*X 2 0+(867431711/2000000000 : ℝ)*X 2 1+(2168579263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1465201351/10000000000 : ℝ)*X 0 0+(4903519977/10000000000 : ℝ)*X 0 1+(1097272909/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152795587/10000000000 : ℝ)*X 1 0+(-113163147/1000000000 : ℝ)*X 1 1+(5486367333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2576398211/5000000000 : ℝ)*X 2 0+(5486366949/10000000000 : ℝ)*X 2 1+(-282907713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4763445589/10000000000 : ℝ)*X 0 0+(920044999/2500000000 : ℝ)*X 0 1+(368017933/1000000000 : ℝ)*X 0 2+(4763445589/10000000000 : ℝ)*X 1 0+(920044999/2500000000 : ℝ)*X 1 1+(368017933/1000000000 : ℝ)*X 1 2+(4763445589/10000000000 : ℝ)*X 2 0+(920044999/2500000000 : ℝ)*X 2 1+(368017933/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-993914299/10000000000 : ℝ)*X 0 0+(5636165891/10000000000 : ℝ)*X 0 1+(1274639961/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1353074017/2500000000 : ℝ)*X 1 0+(-1307650517/10000000000 : ℝ)*X 1 1+(5098559541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5412295973/10000000000 : ℝ)*X 2 0+(5098559933/10000000000 : ℝ)*X 2 1+(-32691253/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1669825981/5000000000 : ℝ)*X 0 0+(4392190021/10000000000 : ℝ)*X 0 1+(274511943/625000000 : ℝ)*X 0 2+(1669825981/5000000000 : ℝ)*X 1 0+(4392190021/10000000000 : ℝ)*X 1 1+(274511943/625000000 : ℝ)*X 1 2+(1669825981/5000000000 : ℝ)*X 2 0+(4392190021/10000000000 : ℝ)*X 2 1+(274511943/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-17233/25000 : ℝ) ≤ (-15341905891639009460448012327/22257500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1551993/6250000000000 : ℝ)*(upper3) + (40949609/50000000000000 : ℝ)*(upper4) + (97012841/100000000000000 : ℝ)*(upper5) + (1053082643830779/100000000000000 : ℝ)*(major0) + (1053082643830779/100000000000000 : ℝ)*(major1) + (1053082643830779/100000000000000 : ℝ)*(major2) + (3457617913/100000000000000 : ℝ)*(sp2) + (1154865703/100000000000000 : ℝ)*(sp3) + (1639213410627919/100000000000000 : ℝ)*(sp4) + (819581981916243/50000000000000 : ℝ)*(sp5) + (1639217520675469/100000000000000 : ℝ)*(sp6) + (244959769165299/50000000000000 : ℝ)*(sp7) + (7567665463/100000000000000 : ℝ)*(sp8) + (1781701903/3125000000000 : ℝ)*(sp13) + (4899206931963/1000000000000 : ℝ)*(f.failure) + (819610489146691/50000000000000 : ℝ)*(f.sum) + (245164665934017/44515000000000000000000000000 : ℝ)*base66 + (673482298452882477/8903000000000000000000000000000000 : ℝ)*base67 + (57988980899633882477/8903000000000000000000000000000000 : ℝ)*base69 + (10303331249170117523/8903000000000000000000000000000000 : ℝ)*base72 + (593771892361/5564375000000000000000000000 : ℝ)*base73 + (3736476864224882477/8903000000000000000000000000000000 : ℝ)*base75 + (6940504271649117523/8903000000000000000000000000000000 : ℝ)*base78 + (6766138883104117523/8903000000000000000000000000000000 : ℝ)*base80 + (9996263677069/22257500000000000000000000000 : ℝ)*base81 + (191151/20000000000000000000 : ℝ)*base90 + (191151/20000000000000000000 : ℝ)*base92 + (191151/20000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58161/100000 : ℝ) ≤ (25891648971378101498451491121/44515000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57562897/100000000000000 : ℝ)*(upper0) + (44057/1250000000000 : ℝ)*(lower1) + (206429/195312500000 : ℝ)*(upper4) + (1177207420110409/100000000000000 : ℝ)*(major0) + (1177207420110409/100000000000000 : ℝ)*(major1) + (1177207420110409/100000000000000 : ℝ)*(major2) + (1787358634673167/100000000000000 : ℝ)*(sp0) + (223419670860349/12500000000000 : ℝ)*(sp1) + (111709870267201/6250000000000 : ℝ)*(sp2) + (547665697471871/100000000000000 : ℝ)*(sp3) + (2835008653/100000000000000 : ℝ)*(sp5) + (2277616229/100000000000000 : ℝ)*(sp6) + (196502567/20000000000000 : ℝ)*(sp7) + (783609139/50000000000000 : ℝ)*(sp8) + (547666679984707/100000000000000 : ℝ)*(f.failure) + (357472040378289/20000000000000 : ℝ)*(f.sum) + (354247945103563/44515000000000000000000000000 : ℝ)*base65 + (1861448688290002833/8903000000000000000000000000000000 : ℝ)*base68 + (12661722138267002833/8903000000000000000000000000000000 : ℝ)*base70 + (31401329522029997167/8903000000000000000000000000000000 : ℝ)*base71 + (319380252168707/44515000000000000000000000000 : ℝ)*base74 + (21784298064784002833/8903000000000000000000000000000000 : ℝ)*base76 + (14422946810945997167/8903000000000000000000000000000000 : ℝ)*base77 + (2194582909572997167/8903000000000000000000000000000000 : ℝ)*base79 + (159400805937073/44515000000000000000000000000 : ℝ)*base81 + (15107561/2000000000000000000000 : ℝ)*base89 + (15107561/2000000000000000000000 : ℝ)*base91 + (15107561/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (10203/12500 : ℝ) ≤ (363361521533018284358979597591717/445150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39713423/50000000000000 : ℝ)*(lower3) + (144301779/100000000000000 : ℝ)*(upper4) + (4660643/50000000000000 : ℝ)*(lower5) + (113563356432753/10000000000000 : ℝ)*(major0) + (113563356432753/10000000000000 : ℝ)*(major1) + (113563356432753/10000000000000 : ℝ)*(major2) + (1772020153/25000000000000 : ℝ)*(sp0) + (19367025193/20000000000000 : ℝ)*(sp1) + (97085584667/100000000000000 : ℝ)*(sp2) + (26799012577/100000000000000 : ℝ)*(sp3) + (857862825166753/50000000000000 : ℝ)*(sp8) + (1715635903288153/100000000000000 : ℝ)*(sp9) + (428908913207363/25000000000000 : ℝ)*(sp10) + (528298671273811/100000000000000 : ℝ)*(sp11) + (132081367571597/25000000000000 : ℝ)*(f.failure) + (857866369207059/50000000000000 : ℝ)*(f.sum) + (10854195047541/2225750000000000000000000000 : ℝ)*base66 + (4564883863064647239/890300000000000000000000000000000 : ℝ)*base67 + (2938660344626247239/890300000000000000000000000000000 : ℝ)*base69 + (4081824847383552761/890300000000000000000000000000000 : ℝ)*base72 + (1545930371399/278218750000000000000000000 : ℝ)*base73 + (1005103003208252761/890300000000000000000000000000000 : ℝ)*base76 + (5577014394650952761/890300000000000000000000000000000 : ℝ)*base78 + (6376408599323452761/890300000000000000000000000000000 : ℝ)*base80 + (24120183552513/8903000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2017031/500000000000000000000 : ℝ)*base89 + (2017031/500000000000000000000 : ℝ)*base91 + (2017031/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-46459/50000 : ℝ) ≤ (-2068062245023225166360108779747509/2225750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30888177/50000000000000 : ℝ)*(lower1) + (19433401/50000000000000 : ℝ)*(lower2) + (12967933/100000000000000 : ℝ)*(lower3) + (2757737/12500000000000 : ℝ)*(upper5) + (595894189453227/50000000000000 : ℝ)*(major0) + (595894189453227/50000000000000 : ℝ)*(major1) + (595894189453227/50000000000000 : ℝ)*(major2) + (17466336061/50000000000000 : ℝ)*(sp5) + (3485003311/50000000000000 : ℝ)*(sp6) + (77575769/2000000000000 : ℝ)*(sp7) + (186009841283537/10000000000000 : ℝ)*(sp12) + (116253967510203/6250000000000 : ℝ)*(sp13) + (465022860707187/25000000000000 : ℝ)*(sp14) + (554446232185907/100000000000000 : ℝ)*(sp15) + (554450110974357/100000000000000 : ℝ)*(f.failure) + (186009841283537/10000000000000 : ℝ)*(f.sum) + (375571218241/5564375000000000000000000000 : ℝ)*base65 + (49143062619813377501/4451500000000000000000000000000000 : ℝ)*base67 + (31884974032769877501/4451500000000000000000000000000000 : ℝ)*base69 + (19471184973295877501/4451500000000000000000000000000000 : ℝ)*base71 + (211924819409553/44515000000000000000000000000 : ℝ)*base73 + (24729039458789877501/4451500000000000000000000000000000 : ℝ)*base75 + (11771638739175877501/4451500000000000000000000000000000 : ℝ)*base77 + (33500268199028377501/4451500000000000000000000000000000 : ℝ)*base79 + (155918341293409/22257500000000000000000000000 : ℝ)*base81 + (17595489/2000000000000000000000 : ℝ)*base90 + (17595489/2000000000000000000000 : ℝ)*base92 + (17595489/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1751_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4489/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9053/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17233/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58161/100000 : ℝ) else (10203/12500 : ℝ) ≤ X j i ∧ X j i ≤ (46459/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1751_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1751_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17233/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58161/100000 : ℝ) else (10203/12500 : ℝ) ≤ X j i ∧ X j i ≤ (46459/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1751_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1751_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17233/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58161/100000 : ℝ) else (10203/12500 : ℝ) ≤ X j i ∧ X j i ≤ (46459/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1751_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
