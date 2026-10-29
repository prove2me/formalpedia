-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1755_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:23:48.857477+00:00
-- url     : https://prove2.me/submissions/84d894fd-511e-4ef3-8702-95ff03935f68

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
theorem support_rectangle_w1755_s0_0 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1153623067/10000000000 : ℝ)*x 0 + (561527467/1000000000 : ℝ)*x 1 + (4985245623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1153623067/10000000000 : ℝ)^5855 ≤ (7298857394099/100000000000000 : ℝ)^4831 := by
    have hnat : (1153623067 : ℕ)^5855*100000000000000^4831 ≤ 7298857394099^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153623067 10000000000 7298857394099 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561527467/1000000000 : ℝ)^5855 ≤ (993748706593/2000000000000 : ℝ)^4831 := by
    have hnat : (561527467 : ℕ)^5855*2000000000000^4831 ≤ 993748706593^4831*1000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561527467 1000000000 993748706593 2000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4985245623/10000000000 : ℝ)^5855 ≤ (21506853633013/50000000000000 : ℝ)^4831 := by
    have hnat : (4985245623 : ℕ)^5855*50000000000000^4831 ≤ 21506853633013^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985245623 10000000000 21506853633013 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1153623067/10000000000 : ℝ), (561527467/1000000000 : ℝ), (4985245623/10000000000 : ℝ)] ![(7298857394099/100000000000000 : ℝ), (993748706593/2000000000000 : ℝ), (21506853633013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1153623067/10000000000 : ℝ)|^5855 ≤ (7298857394099/100000000000000 : ℝ)^4831
        have hw : |(-1153623067/10000000000 : ℝ)|=(1153623067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561527467/1000000000 : ℝ)|^5855 ≤ (993748706593/2000000000000 : ℝ)^4831
        have hw : |(561527467/1000000000 : ℝ)|=(561527467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4985245623/10000000000 : ℝ)|^5855 ≤ (21506853633013/50000000000000 : ℝ)^4831
        have hw : |(4985245623/10000000000 : ℝ)|=(4985245623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s0_1 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683017013/5000000000 : ℝ)*x 0 + (-1490810361/10000000000 : ℝ)*x 1 + (4985246201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683017013/5000000000 : ℝ)^5855 ≤ (23513624437021/50000000000000 : ℝ)^4831 := by
    have hnat : (2683017013 : ℕ)^5855*50000000000000^4831 ≤ 23513624437021^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683017013 5000000000 23513624437021 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1490810361/10000000000 : ℝ)^5855 ≤ (2489759449533/25000000000000 : ℝ)^4831 := by
    have hnat : (1490810361 : ℕ)^5855*25000000000000^4831 ≤ 2489759449533^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490810361 10000000000 2489759449533 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4985246201/10000000000 : ℝ)^5855 ≤ (8602742662043/20000000000000 : ℝ)^4831 := by
    have hnat : (4985246201 : ℕ)^5855*20000000000000^4831 ≤ 8602742662043^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985246201 10000000000 8602742662043 20000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683017013/5000000000 : ℝ), (-1490810361/10000000000 : ℝ), (4985246201/10000000000 : ℝ)] ![(23513624437021/50000000000000 : ℝ), (2489759449533/25000000000000 : ℝ), (8602742662043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683017013/5000000000 : ℝ)|^5855 ≤ (23513624437021/50000000000000 : ℝ)^4831
        have hw : |(2683017013/5000000000 : ℝ)|=(2683017013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1490810361/10000000000 : ℝ)|^5855 ≤ (2489759449533/25000000000000 : ℝ)^4831
        have hw : |(-1490810361/10000000000 : ℝ)|=(1490810361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4985246201/10000000000 : ℝ)|^5855 ≤ (8602742662043/20000000000000 : ℝ)^4831
        have hw : |(4985246201/10000000000 : ℝ)|=(4985246201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s0_2 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268301833/500000000 : ℝ)*x 0 + (2492622371/5000000000 : ℝ)*x 1 + (-1490808791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268301833/500000000 : ℝ)^5855 ≤ (11756819212771/25000000000000 : ℝ)^4831 := by
    have hnat : (268301833 : ℕ)^5855*25000000000000^4831 ≤ 11756819212771^4831*500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268301833 500000000 11756819212771 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2492622371/5000000000 : ℝ)^5855 ≤ (1344178064167/3125000000000 : ℝ)^4831 := by
    have hnat : (2492622371 : ℕ)^5855*3125000000000^4831 ≤ 1344178064167^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492622371 5000000000 1344178064167 3125000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1490808791/10000000000 : ℝ)^5855 ≤ (9959025086993/100000000000000 : ℝ)^4831 := by
    have hnat : (1490808791 : ℕ)^5855*100000000000000^4831 ≤ 9959025086993^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490808791 10000000000 9959025086993 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268301833/500000000 : ℝ), (2492622371/5000000000 : ℝ), (-1490808791/10000000000 : ℝ)] ![(11756819212771/25000000000000 : ℝ), (1344178064167/3125000000000 : ℝ), (9959025086993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268301833/500000000 : ℝ)|^5855 ≤ (11756819212771/25000000000000 : ℝ)^4831
        have hw : |(268301833/500000000 : ℝ)|=(268301833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2492622371/5000000000 : ℝ)|^5855 ≤ (1344178064167/3125000000000 : ℝ)^4831
        have hw : |(2492622371/5000000000 : ℝ)|=(2492622371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1490808791/10000000000 : ℝ)|^5855 ≤ (9959025086993/100000000000000 : ℝ)^4831
        have hw : |(-1490808791/10000000000 : ℝ)|=(1490808791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s0_3 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3970213367/10000000000 : ℝ)*x 0 + (597680569/2000000000 : ℝ)*x 1 + (5100702813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3970213367/10000000000 : ℝ)^5855 ≤ (4080249116611/12500000000000 : ℝ)^4831 := by
    have hnat : (3970213367 : ℕ)^5855*12500000000000^4831 ≤ 4080249116611^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3970213367 10000000000 4080249116611 12500000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597680569/2000000000 : ℝ)^5855 ≤ (23134009802673/100000000000000 : ℝ)^4831 := by
    have hnat : (597680569 : ℕ)^5855*100000000000000^4831 ≤ 23134009802673^4831*2000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597680569 2000000000 23134009802673 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100702813/10000000000 : ℝ)^5855 ≤ (22111998621719/50000000000000 : ℝ)^4831 := by
    have hnat : (5100702813 : ℕ)^5855*50000000000000^4831 ≤ 22111998621719^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100702813 10000000000 22111998621719 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3970213367/10000000000 : ℝ), (597680569/2000000000 : ℝ), (5100702813/10000000000 : ℝ)] ![(4080249116611/12500000000000 : ℝ), (23134009802673/100000000000000 : ℝ), (22111998621719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3970213367/10000000000 : ℝ)|^5855 ≤ (4080249116611/12500000000000 : ℝ)^4831
        have hw : |(3970213367/10000000000 : ℝ)|=(3970213367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597680569/2000000000 : ℝ)|^5855 ≤ (23134009802673/100000000000000 : ℝ)^4831
        have hw : |(597680569/2000000000 : ℝ)|=(597680569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100702813/10000000000 : ℝ)|^5855 ≤ (22111998621719/50000000000000 : ℝ)^4831
        have hw : |(5100702813/10000000000 : ℝ)|=(5100702813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s0_4 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1154886551/10000000000 : ℝ)*x 0 + (1250292197/2500000000 : ℝ)*x 1 + (5598834277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1154886551/10000000000 : ℝ)^5855 ≤ (1827136721193/25000000000000 : ℝ)^4831 := by
    have hnat : (1154886551 : ℕ)^5855*25000000000000^4831 ≤ 1827136721193^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154886551 10000000000 1827136721193 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250292197/2500000000 : ℝ)^5855 ≤ (43180273297311/100000000000000 : ℝ)^4831 := by
    have hnat : (1250292197 : ℕ)^5855*100000000000000^4831 ≤ 43180273297311^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250292197 2500000000 43180273297311 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5598834277/10000000000 : ℝ)^5855 ≤ (49511179800737/100000000000000 : ℝ)^4831 := by
    have hnat : (5598834277 : ℕ)^5855*100000000000000^4831 ≤ 49511179800737^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598834277 10000000000 49511179800737 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1154886551/10000000000 : ℝ), (1250292197/2500000000 : ℝ), (5598834277/10000000000 : ℝ)] ![(1827136721193/25000000000000 : ℝ), (43180273297311/100000000000000 : ℝ), (49511179800737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1154886551/10000000000 : ℝ)|^5855 ≤ (1827136721193/25000000000000 : ℝ)^4831
        have hw : |(-1154886551/10000000000 : ℝ)|=(1154886551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250292197/2500000000 : ℝ)|^5855 ≤ (43180273297311/100000000000000 : ℝ)^4831
        have hw : |(1250292197/2500000000 : ℝ)|=(1250292197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5598834277/10000000000 : ℝ)|^5855 ≤ (49511179800737/100000000000000 : ℝ)^4831
        have hw : |(5598834277/10000000000 : ℝ)|=(5598834277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s0_5 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198316403/10000000000 : ℝ)*x 0 + (-109652549/1250000000 : ℝ)*x 1 + (559883433/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198316403/10000000000 : ℝ)^5855 ≤ (45251785588001/100000000000000 : ℝ)^4831 := by
    have hnat : (5198316403 : ℕ)^5855*100000000000000^4831 ≤ 45251785588001^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198316403 10000000000 45251785588001 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109652549/1250000000 : ℝ)^5855 ≤ (1047406806401/20000000000000 : ℝ)^4831 := by
    have hnat : (109652549 : ℕ)^5855*20000000000000^4831 ≤ 1047406806401^4831*1250000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109652549 1250000000 1047406806401 20000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559883433/1000000000 : ℝ)^5855 ≤ (49511180368767/100000000000000 : ℝ)^4831 := by
    have hnat : (559883433 : ℕ)^5855*100000000000000^4831 ≤ 49511180368767^4831*1000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559883433 1000000000 49511180368767 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198316403/10000000000 : ℝ), (-109652549/1250000000 : ℝ), (559883433/1000000000 : ℝ)] ![(45251785588001/100000000000000 : ℝ), (1047406806401/20000000000000 : ℝ), (49511180368767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198316403/10000000000 : ℝ)|^5855 ≤ (45251785588001/100000000000000 : ℝ)^4831
        have hw : |(5198316403/10000000000 : ℝ)|=(5198316403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109652549/1250000000 : ℝ)|^5855 ≤ (1047406806401/20000000000000 : ℝ)^4831
        have hw : |(-109652549/1250000000 : ℝ)|=(109652549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559883433/1000000000 : ℝ)|^5855 ≤ (49511180368767/100000000000000 : ℝ)^4831
        have hw : |(559883433/1000000000 : ℝ)|=(559883433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s0_6 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198315839/10000000000 : ℝ)*x 0 + (139970861/250000000 : ℝ)*x 1 + (-219305263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198315839/10000000000 : ℝ)^5855 ≤ (22625889818829/50000000000000 : ℝ)^4831 := by
    have hnat : (5198315839 : ℕ)^5855*50000000000000^4831 ≤ 22625889818829^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198315839 10000000000 22625889818829 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139970861/250000000 : ℝ)^5855 ≤ (49511181547697/100000000000000 : ℝ)^4831 := by
    have hnat : (139970861 : ℕ)^5855*100000000000000^4831 ≤ 49511181547697^4831*250000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139970861 250000000 49511181547697 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219305263/2500000000 : ℝ)^5855 ≤ (2618519403707/50000000000000 : ℝ)^4831 := by
    have hnat : (219305263 : ℕ)^5855*50000000000000^4831 ≤ 2618519403707^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219305263 2500000000 2618519403707 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198315839/10000000000 : ℝ), (139970861/250000000 : ℝ), (-219305263/2500000000 : ℝ)] ![(22625889818829/50000000000000 : ℝ), (49511181547697/100000000000000 : ℝ), (2618519403707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198315839/10000000000 : ℝ)|^5855 ≤ (22625889818829/50000000000000 : ℝ)^4831
        have hw : |(5198315839/10000000000 : ℝ)|=(5198315839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(139970861/250000000 : ℝ)|^5855 ≤ (49511181547697/100000000000000 : ℝ)^4831
        have hw : |(139970861/250000000 : ℝ)|=(139970861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219305263/2500000000 : ℝ)|^5855 ≤ (2618519403707/50000000000000 : ℝ)^4831
        have hw : |(-219305263/2500000000 : ℝ)|=(219305263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s0_7 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1987225321/5000000000 : ℝ)*x 0 + (5047314917/10000000000 : ℝ)*x 1 + (3043522527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987225321/5000000000 : ℝ)^5855 ≤ (16342109879453/50000000000000 : ℝ)^4831 := by
    have hnat : (1987225321 : ℕ)^5855*50000000000000^4831 ≤ 16342109879453^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987225321 5000000000 16342109879453 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5047314917/10000000000 : ℝ)^5855 ≤ (436636241393/1000000000000 : ℝ)^4831 := by
    have hnat : (5047314917 : ℕ)^5855*1000000000000^4831 ≤ 436636241393^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5047314917 10000000000 436636241393 1000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3043522527/10000000000 : ℝ)^5855 ≤ (1478259755893/6250000000000 : ℝ)^4831 := by
    have hnat : (3043522527 : ℕ)^5855*6250000000000^4831 ≤ 1478259755893^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3043522527 10000000000 1478259755893 6250000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1987225321/5000000000 : ℝ), (5047314917/10000000000 : ℝ), (3043522527/10000000000 : ℝ)] ![(16342109879453/50000000000000 : ℝ), (436636241393/1000000000000 : ℝ), (1478259755893/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1987225321/5000000000 : ℝ)|^5855 ≤ (16342109879453/50000000000000 : ℝ)^4831
        have hw : |(1987225321/5000000000 : ℝ)|=(1987225321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5047314917/10000000000 : ℝ)|^5855 ≤ (436636241393/1000000000000 : ℝ)^4831
        have hw : |(5047314917/10000000000 : ℝ)|=(5047314917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3043522527/10000000000 : ℝ)|^5855 ≤ (1478259755893/6250000000000 : ℝ)^4831
        have hw : |(3043522527/10000000000 : ℝ)|=(3043522527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1755_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (173/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5139/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5839/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5839 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5839*1^1024 ≤ 0^1024*1^5839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5839/1024 : ℝ) ≤ (134532437208042193/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5839 ≤ (134532437208042193/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5839*25000000000000000000^1024 ≤ 134532437208042193^1024*5^5839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 134532437208042193 25000000000000000000 5839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (134532437208042193/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5839 := by
      have hnat : (1 : ℕ)^1024*1^5839 ≤ 1^5839*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25134532437208042193/25000000000000000000 : ℝ) ≤ (10009416444603229/10000000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (25134532437208042193/25000000000000000000 : ℝ)^1024 ≤ (10009416444603229/10000000000000000 : ℝ)^5839 := by
      have hnat : (25134532437208042193 : ℕ)^1024*10000000000000000^5839 ≤ 10009416444603229^5839*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25134532437208042193 25000000000000000000 10009416444603229 10000000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009416444603229/10000000000000000 : ℝ)) (X := (25134532437208042193/25000000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12634532437208042193/12500000000000000000 : ℝ) ≤ (5009416444603229/5000000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (12634532437208042193/12500000000000000000 : ℝ)^1024 ≤ (5009416444603229/5000000000000000 : ℝ)^5839 := by
      have hnat : (12634532437208042193 : ℕ)^1024*5000000000000000^5839 ≤ 5009416444603229^5839*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12634532437208042193 12500000000000000000 5009416444603229 5000000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009416444603229/5000000000000000 : ℝ)) (X := (12634532437208042193/12500000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9416444603229/4000000000000000 : ℝ)*(0 : ℝ))^(5839/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9416444603229/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(134532437208042193/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9416444603229/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5839/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9416444603229/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10009416444603229/10000000000000000 : ℝ) by norm_num, show 1+(134532437208042193/25000000000000000000 : ℝ)+(0 : ℝ)=(25134532437208042193/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(134532437208042193/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9416444603229/4000000000000000 : ℝ)*(2/5 : ℝ))^(5839/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9416444603229/4000000000000000 : ℝ)*(2/5 : ℝ)=(5009416444603229/5000000000000000 : ℝ) by norm_num, show 1+2*(134532437208042193/25000000000000000000 : ℝ)=(12634532437208042193/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9416444603229/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9416444603229/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9416444603229/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9416444603229/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9416444603229/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9416444603229/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1153623067/10000000000 : ℝ)*X 0 0+(561527467/1000000000 : ℝ)*X 0 1+(4985245623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2683017013/5000000000 : ℝ)*X 1 0+(-1490810361/10000000000 : ℝ)*X 1 1+(4985246201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268301833/500000000 : ℝ)*X 2 0+(2492622371/5000000000 : ℝ)*X 2 1+(-1490808791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3970213367/10000000000 : ℝ)*X 0 0+(597680569/2000000000 : ℝ)*X 0 1+(5100702813/10000000000 : ℝ)*X 0 2+(3970213367/10000000000 : ℝ)*X 1 0+(597680569/2000000000 : ℝ)*X 1 1+(5100702813/10000000000 : ℝ)*X 1 2+(3970213367/10000000000 : ℝ)*X 2 0+(597680569/2000000000 : ℝ)*X 2 1+(5100702813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1154886551/10000000000 : ℝ)*X 0 0+(1250292197/2500000000 : ℝ)*X 0 1+(5598834277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198316403/10000000000 : ℝ)*X 1 0+(-109652549/1250000000 : ℝ)*X 1 1+(559883433/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5198315839/10000000000 : ℝ)*X 2 0+(139970861/250000000 : ℝ)*X 2 1+(-219305263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1987225321/5000000000 : ℝ)*X 0 0+(5047314917/10000000000 : ℝ)*X 0 1+(3043522527/10000000000 : ℝ)*X 0 2+(1987225321/5000000000 : ℝ)*X 1 0+(5047314917/10000000000 : ℝ)*X 1 1+(3043522527/10000000000 : ℝ)*X 1 2+(1987225321/5000000000 : ℝ)*X 2 0+(5047314917/10000000000 : ℝ)*X 2 1+(3043522527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30812252875409026814109/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (482950447/50000000000000 : ℝ)*(base19) + (1440595451/100000000000000 : ℝ)*(base23) + (11422791/10000000000000 : ℝ)*(base24) + (25515219/25000000000000 : ℝ)*(upper4) + (355190283/100000000000000 : ℝ)*(upper5) + (103033122130093/10000000000000 : ℝ)*(major0) + (103033122130093/10000000000000 : ℝ)*(major1) + (103033122130093/10000000000000 : ℝ)*(major2) + (198403859268877/12500000000000 : ℝ)*(sp0) + (198404912196231/12500000000000 : ℝ)*(sp1) + (1587238708647381/100000000000000 : ℝ)*(sp2) + (236710027734091/50000000000000 : ℝ)*(sp3) + (9389319727/100000000000000 : ℝ)*(sp4) + (1918247907/100000000000000 : ℝ)*(sp7) + (47342197371609/10000000000000 : ℝ)*(f.failure) + (1587240263470743/100000000000000 : ℝ)*(f.sum) + (123468357090297/20000000000000000000000000000 : ℝ)*base65 + (72343378329703/40000000000000000000000000000 : ℝ)*base68 + (46496586209703/40000000000000000000000000000 : ℝ)*base70 + (285056980430297/40000000000000000000000000000 : ℝ)*base71 + (11052478250297/20000000000000000000000000000 : ℝ)*base73 + (286332929750297/40000000000000000000000000000 : ℝ)*base75 + (205883403950297/40000000000000000000000000000 : ℝ)*base77 + (370149617430297/40000000000000000000000000000 : ℝ)*base79 + (29267294190297/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4230043/500000000000000000000 : ℝ)*base89 + (4230043/500000000000000000000 : ℝ)*base91 + (4230043/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1829880501724702173/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (570185727/50000000000000 : ℝ)*(base19) + (1029573079/100000000000000 : ℝ)*(base23) + (58403339/100000000000000 : ℝ)*(upper2) + (49184213/25000000000000 : ℝ)*(upper3) + (170779021/100000000000000 : ℝ)*(upper5) + (1086114621193431/100000000000000 : ℝ)*(major0) + (1086114621193431/100000000000000 : ℝ)*(major1) + (1086114621193431/100000000000000 : ℝ)*(major2) + (79966953/1562500000000 : ℝ)*(sp1) + (765595471/20000000000000 : ℝ)*(sp2) + (836587749295737/50000000000000 : ℝ)*(sp4) + (418292310083757/25000000000000 : ℝ)*(sp5) + (1673170641041039/100000000000000 : ℝ)*(sp6) + (499053621803349/100000000000000 : ℝ)*(sp7) + (499053621803349/100000000000000 : ℝ)*(f.failure) + (836587749295737/50000000000000 : ℝ)*(f.sum) + (420020479388699/200000000000000000000000000000 : ℝ)*base65 + (4438980961811301/400000000000000000000000000000 : ℝ)*base68 + (1765671632211301/400000000000000000000000000000 : ℝ)*base70 + (2657153597411301/400000000000000000000000000000 : ℝ)*base72 + (614054467188699/200000000000000000000000000000 : ℝ)*base73 + (1421540565811301/400000000000000000000000000000 : ℝ)*base76 + (84333175411301/400000000000000000000000000000 : ℝ)*base78 + (592455785011301/400000000000000000000000000000 : ℝ)*base80 + (221834838188699/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11836977/5000000000000000000000 : ℝ)*base90 + (11836977/5000000000000000000000 : ℝ)*base92 + (11836977/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1755_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (173/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5139/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1755_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1755_s1_0 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-597007317/5000000000 : ℝ)*x 0 + (5493028049/10000000000 : ℝ)*x 1 + (1270101353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (597007317/5000000000 : ℝ)^5855 ≤ (3804858946237/50000000000000 : ℝ)^4831 := by
    have hnat : (597007317 : ℕ)^5855*50000000000000^4831 ≤ 3804858946237^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597007317 5000000000 3804858946237 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493028049/10000000000 : ℝ)^5855 ≤ (12094869701389/25000000000000 : ℝ)^4831 := by
    have hnat : (5493028049 : ℕ)^5855*25000000000000^4831 ≤ 12094869701389^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493028049 10000000000 12094869701389 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270101353/2500000000 : ℝ)^5855 ≤ (1760432131697/4000000000000 : ℝ)^4831 := by
    have hnat : (1270101353 : ℕ)^5855*4000000000000^4831 ≤ 1760432131697^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270101353 2500000000 1760432131697 4000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-597007317/5000000000 : ℝ), (5493028049/10000000000 : ℝ), (1270101353/2500000000 : ℝ)] ![(3804858946237/50000000000000 : ℝ), (12094869701389/25000000000000 : ℝ), (1760432131697/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-597007317/5000000000 : ℝ)|^5855 ≤ (3804858946237/50000000000000 : ℝ)^4831
        have hw : |(-597007317/5000000000 : ℝ)|=(597007317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493028049/10000000000 : ℝ)|^5855 ≤ (12094869701389/25000000000000 : ℝ)^4831
        have hw : |(5493028049/10000000000 : ℝ)|=(5493028049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270101353/2500000000 : ℝ)|^5855 ≤ (1760432131697/4000000000000 : ℝ)^4831
        have hw : |(1270101353/2500000000 : ℝ)|=(1270101353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s1_1 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5333539331/10000000000 : ℝ)*x 0 + (-35244637/250000000 : ℝ)*x 1 + (254020251/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5333539331/10000000000 : ℝ)^5855 ≤ (46682328206377/100000000000000 : ℝ)^4831 := by
    have hnat : (5333539331 : ℕ)^5855*100000000000000^4831 ≤ 46682328206377^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5333539331 10000000000 46682328206377 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35244637/250000000 : ℝ)^5855 ≤ (9306872608111/100000000000000 : ℝ)^4831 := by
    have hnat : (35244637 : ℕ)^5855*100000000000000^4831 ≤ 9306872608111^4831*250000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35244637 250000000 9306872608111 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254020251/500000000 : ℝ)^5855 ≤ (4401079917679/10000000000000 : ℝ)^4831 := by
    have hnat : (254020251 : ℕ)^5855*10000000000000^4831 ≤ 4401079917679^4831*500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254020251 500000000 4401079917679 10000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5333539331/10000000000 : ℝ), (-35244637/250000000 : ℝ), (254020251/500000000 : ℝ)] ![(46682328206377/100000000000000 : ℝ), (9306872608111/100000000000000 : ℝ), (4401079917679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5333539331/10000000000 : ℝ)|^5855 ≤ (46682328206377/100000000000000 : ℝ)^4831
        have hw : |(5333539331/10000000000 : ℝ)|=(5333539331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35244637/250000000 : ℝ)|^5855 ≤ (9306872608111/100000000000000 : ℝ)^4831
        have hw : |(-35244637/250000000 : ℝ)|=(35244637/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254020251/500000000 : ℝ)|^5855 ≤ (4401079917679/10000000000000 : ℝ)^4831
        have hw : |(254020251/500000000 : ℝ)|=(254020251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s1_2 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2666769117/5000000000 : ℝ)*x 0 + (158762679/312500000 : ℝ)*x 1 + (-352446501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2666769117/5000000000 : ℝ)^5855 ≤ (46682316569579/100000000000000 : ℝ)^4831 := by
    have hnat : (2666769117 : ℕ)^5855*100000000000000^4831 ≤ 46682316569579^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666769117 5000000000 46682316569579 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158762679/312500000 : ℝ)^5855 ≤ (44010806610131/100000000000000 : ℝ)^4831 := by
    have hnat : (158762679 : ℕ)^5855*100000000000000^4831 ≤ 44010806610131^4831*312500000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158762679 312500000 44010806610131 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352446501/2500000000 : ℝ)^5855 ≤ (46534384003/500000000000 : ℝ)^4831 := by
    have hnat : (352446501 : ℕ)^5855*500000000000^4831 ≤ 46534384003^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352446501 2500000000 46534384003 500000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2666769117/5000000000 : ℝ), (158762679/312500000 : ℝ), (-352446501/2500000000 : ℝ)] ![(46682316569579/100000000000000 : ℝ), (44010806610131/100000000000000 : ℝ), (46534384003/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2666769117/5000000000 : ℝ)|^5855 ≤ (46682316569579/100000000000000 : ℝ)^4831
        have hw : |(2666769117/5000000000 : ℝ)|=(2666769117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158762679/312500000 : ℝ)|^5855 ≤ (44010806610131/100000000000000 : ℝ)^4831
        have hw : |(158762679/312500000 : ℝ)|=(158762679/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352446501/2500000000 : ℝ)|^5855 ≤ (46534384003/500000000000 : ℝ)^4831
        have hw : |(-352446501/2500000000 : ℝ)|=(352446501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s1_3 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4009921473/10000000000 : ℝ)*x 0 + (837484169/2500000000 : ℝ)*x 1 + (11833341/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4009921473/10000000000 : ℝ)^5855 ≤ (6607616016229/20000000000000 : ℝ)^4831 := by
    have hnat : (4009921473 : ℕ)^5855*20000000000000^4831 ≤ 6607616016229^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009921473 10000000000 6607616016229 20000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837484169/2500000000 : ℝ)^5855 ≤ (13284073533961/50000000000000 : ℝ)^4831 := by
    have hnat : (837484169 : ℕ)^5855*50000000000000^4831 ≤ 13284073533961^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837484169 2500000000 13284073533961 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11833341/25000000 : ℝ)^5855 ≤ (10098443210229/25000000000000 : ℝ)^4831 := by
    have hnat : (11833341 : ℕ)^5855*25000000000000^4831 ≤ 10098443210229^4831*25000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11833341 25000000 10098443210229 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4009921473/10000000000 : ℝ), (837484169/2500000000 : ℝ), (11833341/25000000 : ℝ)] ![(6607616016229/20000000000000 : ℝ), (13284073533961/50000000000000 : ℝ), (10098443210229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4009921473/10000000000 : ℝ)|^5855 ≤ (6607616016229/20000000000000 : ℝ)^4831
        have hw : |(4009921473/10000000000 : ℝ)|=(4009921473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(837484169/2500000000 : ℝ)|^5855 ≤ (13284073533961/50000000000000 : ℝ)^4831
        have hw : |(837484169/2500000000 : ℝ)|=(837484169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11833341/25000000 : ℝ)|^5855 ≤ (10098443210229/25000000000000 : ℝ)^4831
        have hw : |(11833341/25000000 : ℝ)|=(11833341/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s1_4 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18661997/156250000 : ℝ)*x 0 + (5087249803/10000000000 : ℝ)*x 1 + (2743019269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18661997/156250000 : ℝ)^5855 ≤ (3806222967407/50000000000000 : ℝ)^4831 := by
    have hnat : (18661997 : ℕ)^5855*50000000000000^4831 ≤ 3806222967407^4831*156250000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18661997 156250000 3806222967407 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5087249803/10000000000 : ℝ)^5855 ≤ (5510334160241/12500000000000 : ℝ)^4831 := by
    have hnat : (5087249803 : ℕ)^5855*12500000000000^4831 ≤ 5510334160241^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087249803 10000000000 5510334160241 12500000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743019269/5000000000 : ℝ)^5855 ≤ (48304880762807/100000000000000 : ℝ)^4831 := by
    have hnat : (2743019269 : ℕ)^5855*100000000000000^4831 ≤ 48304880762807^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743019269 5000000000 48304880762807 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18661997/156250000 : ℝ), (5087249803/10000000000 : ℝ), (2743019269/5000000000 : ℝ)] ![(3806222967407/50000000000000 : ℝ), (5510334160241/12500000000000 : ℝ), (48304880762807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18661997/156250000 : ℝ)|^5855 ≤ (3806222967407/50000000000000 : ℝ)^4831
        have hw : |(-18661997/156250000 : ℝ)|=(18661997/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5087249803/10000000000 : ℝ)|^5855 ≤ (5510334160241/12500000000000 : ℝ)^4831
        have hw : |(5087249803/10000000000 : ℝ)|=(5087249803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743019269/5000000000 : ℝ)|^5855 ≤ (48304880762807/100000000000000 : ℝ)^4831
        have hw : |(2743019269/5000000000 : ℝ)|=(2743019269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s1_5 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612151307/5000000000 : ℝ)*x 0 + (-125519057/1250000000 : ℝ)*x 1 + (1371509629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612151307/5000000000 : ℝ)^5855 ≤ (22763045874081/50000000000000 : ℝ)^4831 := by
    have hnat : (2612151307 : ℕ)^5855*50000000000000^4831 ≤ 22763045874081^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612151307 5000000000 22763045874081 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125519057/1250000000 : ℝ)^5855 ≤ (385564231827/6250000000000 : ℝ)^4831 := by
    have hnat : (125519057 : ℕ)^5855*6250000000000^4831 ≤ 385564231827^4831*1250000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125519057 1250000000 385564231827 6250000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371509629/2500000000 : ℝ)^5855 ≤ (12076220132009/25000000000000 : ℝ)^4831 := by
    have hnat : (1371509629 : ℕ)^5855*25000000000000^4831 ≤ 12076220132009^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371509629 2500000000 12076220132009 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612151307/5000000000 : ℝ), (-125519057/1250000000 : ℝ), (1371509629/2500000000 : ℝ)] ![(22763045874081/50000000000000 : ℝ), (385564231827/6250000000000 : ℝ), (12076220132009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612151307/5000000000 : ℝ)|^5855 ≤ (22763045874081/50000000000000 : ℝ)^4831
        have hw : |(2612151307/5000000000 : ℝ)|=(2612151307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125519057/1250000000 : ℝ)|^5855 ≤ (385564231827/6250000000000 : ℝ)^4831
        have hw : |(-125519057/1250000000 : ℝ)|=(125519057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371509629/2500000000 : ℝ)|^5855 ≤ (12076220132009/25000000000000 : ℝ)^4831
        have hw : |(1371509629/2500000000 : ℝ)|=(1371509629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s1_6 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224302629/10000000000 : ℝ)*x 0 + (5486038437/10000000000 : ℝ)*x 1 + (-1004152549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224302629/10000000000 : ℝ)^5855 ≤ (5690761488323/12500000000000 : ℝ)^4831 := by
    have hnat : (5224302629 : ℕ)^5855*12500000000000^4831 ≤ 5690761488323^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224302629 10000000000 5690761488323 12500000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486038437/10000000000 : ℝ)^5855 ≤ (24152439842497/50000000000000 : ℝ)^4831 := by
    have hnat : (5486038437 : ℕ)^5855*50000000000000^4831 ≤ 24152439842497^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486038437 10000000000 24152439842497 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004152549/10000000000 : ℝ)^5855 ≤ (1233805680337/20000000000000 : ℝ)^4831 := by
    have hnat : (1004152549 : ℕ)^5855*20000000000000^4831 ≤ 1233805680337^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004152549 10000000000 1233805680337 20000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224302629/10000000000 : ℝ), (5486038437/10000000000 : ℝ), (-1004152549/10000000000 : ℝ)] ![(5690761488323/12500000000000 : ℝ), (24152439842497/50000000000000 : ℝ), (1233805680337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224302629/10000000000 : ℝ)|^5855 ≤ (5690761488323/12500000000000 : ℝ)^4831
        have hw : |(5224302629/10000000000 : ℝ)|=(5224302629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486038437/10000000000 : ℝ)|^5855 ≤ (24152439842497/50000000000000 : ℝ)^4831
        have hw : |(5486038437/10000000000 : ℝ)|=(5486038437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004152549/10000000000 : ℝ)|^5855 ≤ (1233805680337/20000000000000 : ℝ)^4831
        have hw : |(-1004152549/10000000000 : ℝ)|=(1004152549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s1_7 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2005552401/5000000000 : ℝ)*x 0 + (94207753/200000000 : ℝ)*x 1 + (843342679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005552401/5000000000 : ℝ)^5855 ≤ (33049896554637/100000000000000 : ℝ)^4831 := by
    have hnat : (2005552401 : ℕ)^5855*100000000000000^4831 ≤ 33049896554637^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005552401 5000000000 33049896554637 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94207753/200000000 : ℝ)^5855 ≤ (20078270645547/50000000000000 : ℝ)^4831 := by
    have hnat : (94207753 : ℕ)^5855*50000000000000^4831 ≤ 20078270645547^4831*200000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94207753 200000000 20078270645547 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843342679/2500000000 : ℝ)^5855 ≤ (26793562148899/100000000000000 : ℝ)^4831 := by
    have hnat : (843342679 : ℕ)^5855*100000000000000^4831 ≤ 26793562148899^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843342679 2500000000 26793562148899 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2005552401/5000000000 : ℝ), (94207753/200000000 : ℝ), (843342679/2500000000 : ℝ)] ![(33049896554637/100000000000000 : ℝ), (20078270645547/50000000000000 : ℝ), (26793562148899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2005552401/5000000000 : ℝ)|^5855 ≤ (33049896554637/100000000000000 : ℝ)^4831
        have hw : |(2005552401/5000000000 : ℝ)|=(2005552401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(94207753/200000000 : ℝ)|^5855 ≤ (20078270645547/50000000000000 : ℝ)^4831
        have hw : |(94207753/200000000 : ℝ)|=(94207753/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(843342679/2500000000 : ℝ)|^5855 ≤ (26793562148899/100000000000000 : ℝ)^4831
        have hw : |(843342679/2500000000 : ℝ)|=(843342679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1755_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5139/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (173/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (4527/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3587/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5139/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (173/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5139/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (173/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5139/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (173/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5139/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (173/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5139/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (173/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5139/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (173/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (173/2500 : ℝ) ^ (5839/1024 : ℝ) ≤ (24328356928253/100000000000000000000 : ℝ) := by
    have hpowers : (173/2500 : ℝ)^5839 ≤ (24328356928253/100000000000000000000 : ℝ)^1024 := by
      have hnat : (173 : ℕ)^5839*100000000000000000000^1024 ≤ 24328356928253^1024*2500^5839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        173 2500 24328356928253 100000000000000000000 5839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (173/2500 : ℝ)) (X := (24328356928253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5139/25000 : ℝ) ^ (5839/1024 : ℝ) ≤ (6042879960686253/50000000000000000000 : ℝ) := by
    have hpowers : (5139/25000 : ℝ)^5839 ≤ (6042879960686253/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5139 : ℕ)^5839*50000000000000000000^1024 ≤ 6042879960686253^1024*25000^5839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5139 25000 6042879960686253 50000000000000000000 5839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5139/25000 : ℝ)) (X := (6042879960686253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000024328356928253/50000000000000000000 : ℝ) ≤ (10000000853304761/10000000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (50000024328356928253/50000000000000000000 : ℝ)^1024 ≤ (10000000853304761/10000000000000000 : ℝ)^5839 := by
      have hnat : (50000024328356928253 : ℕ)^1024*10000000000000000^5839 ≤ 10000000853304761^5839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000024328356928253 50000000000000000000 10000000853304761 10000000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000853304761/10000000000000000 : ℝ)) (X := (50000024328356928253/50000000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100012110088278300759/100000000000000000000 : ℝ) ≤ (1000021236703639/1000000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (100012110088278300759/100000000000000000000 : ℝ)^1024 ≤ (1000021236703639/1000000000000000 : ℝ)^5839 := by
      have hnat : (100012110088278300759 : ℕ)^1024*1000000000000000^5839 ≤ 1000021236703639^5839*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012110088278300759 100000000000000000000 1000021236703639 1000000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021236703639/1000000000000000 : ℝ)) (X := (100012110088278300759/100000000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006042879960686253/25000000000000000000 : ℝ) ≤ (10000423880768019/10000000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (25006042879960686253/25000000000000000000 : ℝ)^1024 ≤ (10000423880768019/10000000000000000 : ℝ)^5839 := by
      have hnat : (25006042879960686253 : ℕ)^1024*10000000000000000^5839 ≤ 10000423880768019^5839*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006042879960686253 25000000000000000000 10000423880768019 10000000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000423880768019/10000000000000000 : ℝ)) (X := (25006042879960686253/25000000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24328356928253/100000000000000000000 : ℝ) ≤ ((34089271071404493909/34090000000000000000 : ℝ)+2*(211513731629/1363600000000000 : ℝ)*(173/2500 : ℝ))^(5839/1024 : ℝ) := by
    rw [show (34089271071404493909/34090000000000000000 : ℝ)+2*(211513731629/1363600000000000 : ℝ)*(173/2500 : ℝ)=(10000000853304761/10000000000000000 : ℝ) by norm_num, show 1+2*(24328356928253/100000000000000000000 : ℝ)=(50000024328356928253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6042879960686253/50000000000000000000 : ℝ)+(24328356928253/100000000000000000000 : ℝ) ≤ ((34089271071404493909/34090000000000000000 : ℝ)+(211513731629/1363600000000000 : ℝ)*((5139/25000 : ℝ)+(173/2500 : ℝ)))^(5839/1024 : ℝ) := by
    rw [show (34089271071404493909/34090000000000000000 : ℝ)+(211513731629/1363600000000000 : ℝ)*((5139/25000 : ℝ)+(173/2500 : ℝ))=(1000021236703639/1000000000000000 : ℝ) by norm_num, show 1+(6042879960686253/50000000000000000000 : ℝ)+(24328356928253/100000000000000000000 : ℝ)=(100012110088278300759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6042879960686253/50000000000000000000 : ℝ) ≤ ((34089271071404493909/34090000000000000000 : ℝ)+2*(211513731629/1363600000000000 : ℝ)*(5139/25000 : ℝ))^(5839/1024 : ℝ) := by
    rw [show (34089271071404493909/34090000000000000000 : ℝ)+2*(211513731629/1363600000000000 : ℝ)*(5139/25000 : ℝ)=(10000423880768019/10000000000000000 : ℝ) by norm_num, show 1+2*(6042879960686253/50000000000000000000 : ℝ)=(25006042879960686253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34089271071404493909/34090000000000000000 : ℝ)*(X 1 0+X 2 0)+(211513731629/1363600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (173/2500 : ℝ)) (hi := (5139/25000 : ℝ)) (c := (34089271071404493909/34090000000000000000 : ℝ)) (alpha := (211513731629/1363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34089271071404493909/34090000000000000000 : ℝ)*(X 0 1+X 2 1)+(211513731629/1363600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (173/2500 : ℝ)) (hi := (5139/25000 : ℝ)) (c := (34089271071404493909/34090000000000000000 : ℝ)) (alpha := (211513731629/1363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34089271071404493909/34090000000000000000 : ℝ)*(X 0 2+X 1 2)+(211513731629/1363600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (173/2500 : ℝ)) (hi := (5139/25000 : ℝ)) (c := (34089271071404493909/34090000000000000000 : ℝ)) (alpha := (211513731629/1363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-597007317/5000000000 : ℝ)*X 0 0+(5493028049/10000000000 : ℝ)*X 0 1+(1270101353/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5333539331/10000000000 : ℝ)*X 1 0+(-35244637/250000000 : ℝ)*X 1 1+(254020251/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2666769117/5000000000 : ℝ)*X 2 0+(158762679/312500000 : ℝ)*X 2 1+(-352446501/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4009921473/10000000000 : ℝ)*X 0 0+(837484169/2500000000 : ℝ)*X 0 1+(11833341/25000000 : ℝ)*X 0 2+(4009921473/10000000000 : ℝ)*X 1 0+(837484169/2500000000 : ℝ)*X 1 1+(11833341/25000000 : ℝ)*X 1 2+(4009921473/10000000000 : ℝ)*X 2 0+(837484169/2500000000 : ℝ)*X 2 1+(11833341/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-18661997/156250000 : ℝ)*X 0 0+(5087249803/10000000000 : ℝ)*X 0 1+(2743019269/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2612151307/5000000000 : ℝ)*X 1 0+(-125519057/1250000000 : ℝ)*X 1 1+(1371509629/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5224302629/10000000000 : ℝ)*X 2 0+(5486038437/10000000000 : ℝ)*X 2 1+(-1004152549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2005552401/5000000000 : ℝ)*X 0 0+(94207753/200000000 : ℝ)*X 0 1+(843342679/2500000000 : ℝ)*X 0 2+(2005552401/5000000000 : ℝ)*X 1 0+(94207753/200000000 : ℝ)*X 1 1+(843342679/2500000000 : ℝ)*X 1 2+(2005552401/5000000000 : ℝ)*X 2 0+(94207753/200000000 : ℝ)*X 2 1+(843342679/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10241634459218769829064691729/852250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (427030969/25000000000000 : ℝ)*(base19) + (531814331/50000000000000 : ℝ)*(base23) + (39530167/50000000000000 : ℝ)*(lower2) + (90112019/20000000000000 : ℝ)*(upper3) + (294723/25000000000000 : ℝ)*(lower4) + (1573203990866173/100000000000000 : ℝ)*(major0) + (1573203990866173/100000000000000 : ℝ)*(major1) + (1573203990866173/100000000000000 : ℝ)*(major2) + (605884080909353/25000000000000 : ℝ)*(sp0) + (1211770941147901/50000000000000 : ℝ)*(sp1) + (484708505358203/20000000000000 : ℝ)*(sp2) + (7228595162991/1000000000000 : ℝ)*(sp3) + (1453356453/20000000000000 : ℝ)*(sp4) + (559305147/12500000000000 : ℝ)*(sp7) + (180715997685069/25000000000000 : ℝ)*(f.failure) + (1211771795209839/50000000000000 : ℝ)*(f.sum) + (513442352188503/68180000000000000000000000000 : ℝ)*base66 + (31968189977711065257/3409000000000000000000000000000000 : ℝ)*base67 + (25255653027788065257/3409000000000000000000000000000000 : ℝ)*base69 + (8098840168067934743/3409000000000000000000000000000000 : ℝ)*base72 + (65610470781383/68180000000000000000000000000 : ℝ)*base74 + (1016559445854065257/3409000000000000000000000000000000 : ℝ)*base75 + (7967848257300065257/3409000000000000000000000000000000 : ℝ)*base77 + (51815316603478065257/3409000000000000000000000000000000 : ℝ)*base79 + (23897943445737/68180000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2397463/1250000000000000000000 : ℝ)*base89 + (2397463/1250000000000000000000 : ℝ)*base91 + (2397463/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5530939780877919926368985187/852250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235176161/25000000000000 : ℝ)*(base19) + (930135939/100000000000000 : ℝ)*(base23) + (139611157/100000000000000 : ℝ)*(upper3) + (157053/6250000000000 : ℝ)*(lower4) + (188024549/100000000000000 : ℝ)*(upper5) + (813881953768673/50000000000000 : ℝ)*(major0) + (813881953768673/50000000000000 : ℝ)*(major1) + (813881953768673/50000000000000 : ℝ)*(major2) + (6890520407/100000000000000 : ℝ)*(sp1) + (5810755011/100000000000000 : ℝ)*(sp2) + (1253797066192103/50000000000000 : ℝ)*(sp4) + (501517260231831/20000000000000 : ℝ)*(sp5) + (313448423936657/12500000000000 : ℝ)*(sp6) + (747933466363501/100000000000000 : ℝ)*(sp7) + (747933466363501/100000000000000 : ℝ)*(f.failure) + (1253797066192103/50000000000000 : ℝ)*(f.sum) + (12473550200457/34090000000000000000000000000 : ℝ)*base65 + (27773353068375437757/1704500000000000000000000000000000 : ℝ)*base67 + (24314933688533437757/1704500000000000000000000000000000 : ℝ)*base69 + (24804085737880937757/1704500000000000000000000000000000 : ℝ)*base71 + (130283604333417/34090000000000000000000000000 : ℝ)*base73 + (10725421723819437757/1704500000000000000000000000000000 : ℝ)*base75 + (20299089321481437757/1704500000000000000000000000000000 : ℝ)*base77 + (22254910806896437757/1704500000000000000000000000000000 : ℝ)*base79 + (156651417604797/34090000000000000000000000000 : ℝ)*base81 + (74468073/5000000000000000000000 : ℝ)*base90 + (74468073/5000000000000000000000 : ℝ)*base92 + (74468073/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1755_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5139/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (173/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3587/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1755_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1755_s2_0 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-298708723/2500000000 : ℝ)*x 0 + (5490391401/10000000000 : ℝ)*x 1 + (2541241167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (298708723/2500000000 : ℝ)^5855 ≤ (7616054121357/100000000000000 : ℝ)^4831 := by
    have hnat : (298708723 : ℕ)^5855*100000000000000^4831 ≤ 7616054121357^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298708723 2500000000 7616054121357 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490391401/10000000000 : ℝ)^5855 ≤ (9670267175399/20000000000000 : ℝ)^4831 := by
    have hnat : (5490391401 : ℕ)^5855*20000000000000^4831 ≤ 9670267175399^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490391401 10000000000 9670267175399 20000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541241167/5000000000 : ℝ)^5855 ≤ (44032609984351/100000000000000 : ℝ)^4831 := by
    have hnat : (2541241167 : ℕ)^5855*100000000000000^4831 ≤ 44032609984351^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541241167 5000000000 44032609984351 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-298708723/2500000000 : ℝ), (5490391401/10000000000 : ℝ), (2541241167/5000000000 : ℝ)] ![(7616054121357/100000000000000 : ℝ), (9670267175399/20000000000000 : ℝ), (44032609984351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-298708723/2500000000 : ℝ)|^5855 ≤ (7616054121357/100000000000000 : ℝ)^4831
        have hw : |(-298708723/2500000000 : ℝ)|=(298708723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490391401/10000000000 : ℝ)|^5855 ≤ (9670267175399/20000000000000 : ℝ)^4831
        have hw : |(5490391401/10000000000 : ℝ)|=(5490391401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541241167/5000000000 : ℝ)|^5855 ≤ (44032609984351/100000000000000 : ℝ)^4831
        have hw : |(2541241167/5000000000 : ℝ)|=(2541241167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s2_1 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533280467/1000000000 : ℝ)*x 0 + (-704016629/5000000000 : ℝ)*x 1 + (1016496463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533280467/1000000000 : ℝ)^5855 ≤ (11668633788869/25000000000000 : ℝ)^4831 := by
    have hnat : (533280467 : ℕ)^5855*25000000000000^4831 ≤ 11668633788869^4831*1000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533280467 1000000000 11668633788869 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (704016629/5000000000 : ℝ)^5855 ≤ (9292855045751/100000000000000 : ℝ)^4831 := by
    have hnat : (704016629 : ℕ)^5855*100000000000000^4831 ≤ 9292855045751^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704016629 5000000000 9292855045751 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016496463/2000000000 : ℝ)^5855 ≤ (11008152446213/25000000000000 : ℝ)^4831 := by
    have hnat : (1016496463 : ℕ)^5855*25000000000000^4831 ≤ 11008152446213^4831*2000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016496463 2000000000 11008152446213 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533280467/1000000000 : ℝ), (-704016629/5000000000 : ℝ), (1016496463/2000000000 : ℝ)] ![(11668633788869/25000000000000 : ℝ), (9292855045751/100000000000000 : ℝ), (11008152446213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533280467/1000000000 : ℝ)|^5855 ≤ (11668633788869/25000000000000 : ℝ)^4831
        have hw : |(533280467/1000000000 : ℝ)|=(533280467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-704016629/5000000000 : ℝ)|^5855 ≤ (9292855045751/100000000000000 : ℝ)^4831
        have hw : |(-704016629/5000000000 : ℝ)|=(704016629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016496463/2000000000 : ℝ)|^5855 ≤ (11008152446213/25000000000000 : ℝ)^4831
        have hw : |(1016496463/2000000000 : ℝ)|=(1016496463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s2_2 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2666402333/5000000000 : ℝ)*x 0 + (5082482321/10000000000 : ℝ)*x 1 + (-281606651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2666402333/5000000000 : ℝ)^5855 ≤ (23337267556523/50000000000000 : ℝ)^4831 := by
    have hnat : (2666402333 : ℕ)^5855*50000000000000^4831 ≤ 23337267556523^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666402333 5000000000 23337267556523 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082482321/10000000000 : ℝ)^5855 ≤ (44032609847851/100000000000000 : ℝ)^4831 := by
    have hnat : (5082482321 : ℕ)^5855*100000000000000^4831 ≤ 44032609847851^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082482321 10000000000 44032609847851 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281606651/2000000000 : ℝ)^5855 ≤ (1858571004351/20000000000000 : ℝ)^4831 := by
    have hnat : (281606651 : ℕ)^5855*20000000000000^4831 ≤ 1858571004351^4831*2000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281606651 2000000000 1858571004351 20000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2666402333/5000000000 : ℝ), (5082482321/10000000000 : ℝ), (-281606651/2000000000 : ℝ)] ![(23337267556523/50000000000000 : ℝ), (44032609847851/100000000000000 : ℝ), (1858571004351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2666402333/5000000000 : ℝ)|^5855 ≤ (23337267556523/50000000000000 : ℝ)^4831
        have hw : |(2666402333/5000000000 : ℝ)|=(2666402333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082482321/10000000000 : ℝ)|^5855 ≤ (44032609847851/100000000000000 : ℝ)^4831
        have hw : |(5082482321/10000000000 : ℝ)|=(5082482321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281606651/2000000000 : ℝ)|^5855 ≤ (1858571004351/20000000000000 : ℝ)^4831
        have hw : |(-281606651/2000000000 : ℝ)|=(281606651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s2_3 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4010595221/10000000000 : ℝ)*x 0 + (335778947/1000000000 : ℝ)*x 1 + (59067309/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4010595221/10000000000 : ℝ)^5855 ≤ (8261201973947/25000000000000 : ℝ)^4831 := by
    have hnat : (4010595221 : ℕ)^5855*25000000000000^4831 ≤ 8261201973947^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010595221 10000000000 8261201973947 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335778947/1000000000 : ℝ)^5855 ≤ (26643646998437/100000000000000 : ℝ)^4831 := by
    have hnat : (335778947 : ℕ)^5855*100000000000000^4831 ≤ 26643646998437^4831*1000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335778947 1000000000 26643646998437 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59067309/125000000 : ℝ)^5855 ≤ (20155772542309/50000000000000 : ℝ)^4831 := by
    have hnat : (59067309 : ℕ)^5855*50000000000000^4831 ≤ 20155772542309^4831*125000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59067309 125000000 20155772542309 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4010595221/10000000000 : ℝ), (335778947/1000000000 : ℝ), (59067309/125000000 : ℝ)] ![(8261201973947/25000000000000 : ℝ), (26643646998437/100000000000000 : ℝ), (20155772542309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4010595221/10000000000 : ℝ)|^5855 ≤ (8261201973947/25000000000000 : ℝ)^4831
        have hw : |(4010595221/10000000000 : ℝ)|=(4010595221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(335778947/1000000000 : ℝ)|^5855 ≤ (26643646998437/100000000000000 : ℝ)^4831
        have hw : |(335778947/1000000000 : ℝ)|=(335778947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59067309/125000000 : ℝ)|^5855 ≤ (20155772542309/50000000000000 : ℝ)^4831
        have hw : |(59067309/125000000 : ℝ)|=(59067309/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s2_4 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1195175767/10000000000 : ℝ)*x 0 + (508917177/1000000000 : ℝ)*x 1 + (1370890497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1195175767/10000000000 : ℝ)^5855 ≤ (1904671885549/25000000000000 : ℝ)^4831 := by
    have hnat : (1195175767 : ℕ)^5855*25000000000000^4831 ≤ 1904671885549^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195175767 10000000000 1904671885549 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508917177/1000000000 : ℝ)^5855 ≤ (1102571467833/2500000000000 : ℝ)^4831 := by
    have hnat : (508917177 : ℕ)^5855*2500000000000^4831 ≤ 1102571467833^4831*1000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508917177 1000000000 1102571467833 2500000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370890497/2500000000 : ℝ)^5855 ≤ (24139226866889/50000000000000 : ℝ)^4831 := by
    have hnat : (1370890497 : ℕ)^5855*50000000000000^4831 ≤ 24139226866889^4831*2500000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370890497 2500000000 24139226866889 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1195175767/10000000000 : ℝ), (508917177/1000000000 : ℝ), (1370890497/2500000000 : ℝ)] ![(1904671885549/25000000000000 : ℝ), (1102571467833/2500000000000 : ℝ), (24139226866889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1195175767/10000000000 : ℝ)|^5855 ≤ (1904671885549/25000000000000 : ℝ)^4831
        have hw : |(-1195175767/10000000000 : ℝ)|=(1195175767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508917177/1000000000 : ℝ)|^5855 ≤ (1102571467833/2500000000000 : ℝ)^4831
        have hw : |(508917177/1000000000 : ℝ)|=(508917177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370890497/2500000000 : ℝ)|^5855 ≤ (24139226866889/50000000000000 : ℝ)^4831
        have hw : |(1370890497/2500000000 : ℝ)|=(1370890497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s2_5 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224829377/10000000000 : ℝ)*x 0 + (-201390727/2000000000 : ℝ)*x 1 + (2741781013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224829377/10000000000 : ℝ)^5855 ≤ (5691456895959/12500000000000 : ℝ)^4831 := by
    have hnat : (5224829377 : ℕ)^5855*12500000000000^4831 ≤ 5691456895959^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224829377 10000000000 5691456895959 12500000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201390727/2000000000 : ℝ)^5855 ≤ (6189890676421/100000000000000 : ℝ)^4831 := by
    have hnat : (201390727 : ℕ)^5855*100000000000000^4831 ≤ 6189890676421^4831*2000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201390727 2000000000 6189890676421 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741781013/5000000000 : ℝ)^5855 ≤ (48278454139253/100000000000000 : ℝ)^4831 := by
    have hnat : (2741781013 : ℕ)^5855*100000000000000^4831 ≤ 48278454139253^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741781013 5000000000 48278454139253 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224829377/10000000000 : ℝ), (-201390727/2000000000 : ℝ), (2741781013/5000000000 : ℝ)] ![(5691456895959/12500000000000 : ℝ), (6189890676421/100000000000000 : ℝ), (48278454139253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224829377/10000000000 : ℝ)|^5855 ≤ (5691456895959/12500000000000 : ℝ)^4831
        have hw : |(5224829377/10000000000 : ℝ)|=(5224829377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201390727/2000000000 : ℝ)|^5855 ≤ (6189890676421/100000000000000 : ℝ)^4831
        have hw : |(-201390727/2000000000 : ℝ)|=(201390727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741781013/5000000000 : ℝ)|^5855 ≤ (48278454139253/100000000000000 : ℝ)^4831
        have hw : |(2741781013/5000000000 : ℝ)|=(2741781013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s2_6 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653103673/1250000000 : ℝ)*x 0 + (5483562033/10000000000 : ℝ)*x 1 + (-201390723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653103673/1250000000 : ℝ)^5855 ≤ (11382913810401/25000000000000 : ℝ)^4831 := by
    have hnat : (653103673 : ℕ)^5855*25000000000000^4831 ≤ 11382913810401^4831*1250000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653103673 1250000000 11382913810401 25000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483562033/10000000000 : ℝ)^5855 ≤ (24139227106973/50000000000000 : ℝ)^4831 := by
    have hnat : (5483562033 : ℕ)^5855*50000000000000^4831 ≤ 24139227106973^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483562033 10000000000 24139227106973 50000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201390723/2000000000 : ℝ)^5855 ≤ (6189890527419/100000000000000 : ℝ)^4831 := by
    have hnat : (201390723 : ℕ)^5855*100000000000000^4831 ≤ 6189890527419^4831*2000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201390723 2000000000 6189890527419 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653103673/1250000000 : ℝ), (5483562033/10000000000 : ℝ), (-201390723/2000000000 : ℝ)] ![(11382913810401/25000000000000 : ℝ), (24139227106973/50000000000000 : ℝ), (6189890527419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653103673/1250000000 : ℝ)|^5855 ≤ (11382913810401/25000000000000 : ℝ)^4831
        have hw : |(653103673/1250000000 : ℝ)|=(653103673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483562033/10000000000 : ℝ)|^5855 ≤ (24139227106973/50000000000000 : ℝ)^4831
        have hw : |(5483562033/10000000000 : ℝ)|=(5483562033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201390723/2000000000 : ℝ)|^5855 ≤ (6189890527419/100000000000000 : ℝ)^4831
        have hw : |(-201390723/2000000000 : ℝ)|=(201390723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1755_s2_7 (p : ℝ) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2005868991/5000000000 : ℝ)*x 0 + (2351478637/5000000000 : ℝ)*x 1 + (3380686083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005868991/5000000000 : ℝ)^5855 ≤ (33056219659889/100000000000000 : ℝ)^4831 := by
    have hnat : (2005868991 : ℕ)^5855*100000000000000^4831 ≤ 33056219659889^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005868991 5000000000 33056219659889 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351478637/5000000000 : ℝ)^5855 ≤ (40079782582243/100000000000000 : ℝ)^4831 := by
    have hnat : (2351478637 : ℕ)^5855*100000000000000^4831 ≤ 40079782582243^4831*5000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351478637 5000000000 40079782582243 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3380686083/10000000000 : ℝ)^5855 ≤ (26863997731551/100000000000000 : ℝ)^4831 := by
    have hnat : (3380686083 : ℕ)^5855*100000000000000^4831 ≤ 26863997731551^4831*10000000000^5855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3380686083 10000000000 26863997731551 100000000000000 5855 4831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5855/1024 : ℝ)) 5855 4831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2005868991/5000000000 : ℝ), (2351478637/5000000000 : ℝ), (3380686083/10000000000 : ℝ)] ![(33056219659889/100000000000000 : ℝ), (40079782582243/100000000000000 : ℝ), (26863997731551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2005868991/5000000000 : ℝ)|^5855 ≤ (33056219659889/100000000000000 : ℝ)^4831
        have hw : |(2005868991/5000000000 : ℝ)|=(2005868991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2351478637/5000000000 : ℝ)|^5855 ≤ (40079782582243/100000000000000 : ℝ)^4831
        have hw : |(2351478637/5000000000 : ℝ)|=(2351478637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3380686083/10000000000 : ℝ)|^5855 ≤ (26863997731551/100000000000000 : ℝ)^4831
        have hw : |(3380686083/10000000000 : ℝ)|=(3380686083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1755_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3587/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17879/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3587/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3587/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3587/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3587/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3587/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3587/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4527/50000 : ℝ) ^ (5839/1024 : ℝ) ≤ (28163695461089/25000000000000000000 : ℝ) := by
    have hpowers : (4527/50000 : ℝ)^5839 ≤ (28163695461089/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4527 : ℕ)^5839*25000000000000000000^1024 ≤ 28163695461089^1024*50000^5839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4527 50000 28163695461089 25000000000000000000 5839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4527/50000 : ℝ)) (X := (28163695461089/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3587/20000 : ℝ) ^ (5839/1024 : ℝ) ≤ (5552575798392941/100000000000000000000 : ℝ) := by
    have hpowers : (3587/20000 : ℝ)^5839 ≤ (5552575798392941/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3587 : ℕ)^5839*100000000000000000000^1024 ≤ 5552575798392941^1024*20000^5839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3587 20000 5552575798392941 100000000000000000000 5839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3587/20000 : ℝ)) (X := (5552575798392941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500028163695461089/12500000000000000000 : ℝ) ≤ (10000003951306369/10000000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (12500028163695461089/12500000000000000000 : ℝ)^1024 ≤ (10000003951306369/10000000000000000 : ℝ)^5839 := by
      have hnat : (12500028163695461089 : ℕ)^1024*10000000000000000^5839 ≤ 10000003951306369^5839*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500028163695461089 12500000000000000000 10000003951306369 10000000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003951306369/10000000000000000 : ℝ)) (X := (12500028163695461089/12500000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005665230580237297/100000000000000000000 : ℝ) ≤ (2500024837560419/2500000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (100005665230580237297/100000000000000000000 : ℝ)^1024 ≤ (2500024837560419/2500000000000000 : ℝ)^5839 := by
      have hnat : (100005665230580237297 : ℕ)^1024*2500000000000000^5839 ≤ 2500024837560419^5839*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005665230580237297 100000000000000000000 2500024837560419 2500000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500024837560419/2500000000000000 : ℝ)) (X := (100005665230580237297/100000000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50005552575798392941/50000000000000000000 : ℝ) ≤ (10000194749176983/10000000000000000 : ℝ) ^ (5839/1024 : ℝ) := by
    have hpowers : (50005552575798392941/50000000000000000000 : ℝ)^1024 ≤ (10000194749176983/10000000000000000 : ℝ)^5839 := by
      have hnat : (50005552575798392941 : ℕ)^1024*10000000000000000^5839 ≤ 10000194749176983^5839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005552575798392941 50000000000000000000 10000194749176983 10000000000000000 1024 5839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000194749176983/10000000000000000 : ℝ)) (X := (50005552575798392941/50000000000000000000 : ℝ)) (by norm_num) 5839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28163695461089/25000000000000000000 : ℝ) ≤ ((88808307607631323933/88810000000000000000 : ℝ)+2*(95398935307/888100000000000 : ℝ)*(4527/50000 : ℝ))^(5839/1024 : ℝ) := by
    rw [show (88808307607631323933/88810000000000000000 : ℝ)+2*(95398935307/888100000000000 : ℝ)*(4527/50000 : ℝ)=(10000003951306369/10000000000000000 : ℝ) by norm_num, show 1+2*(28163695461089/25000000000000000000 : ℝ)=(12500028163695461089/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5552575798392941/100000000000000000000 : ℝ)+(28163695461089/25000000000000000000 : ℝ) ≤ ((88808307607631323933/88810000000000000000 : ℝ)+(95398935307/888100000000000 : ℝ)*((3587/20000 : ℝ)+(4527/50000 : ℝ)))^(5839/1024 : ℝ) := by
    rw [show (88808307607631323933/88810000000000000000 : ℝ)+(95398935307/888100000000000 : ℝ)*((3587/20000 : ℝ)+(4527/50000 : ℝ))=(2500024837560419/2500000000000000 : ℝ) by norm_num, show 1+(5552575798392941/100000000000000000000 : ℝ)+(28163695461089/25000000000000000000 : ℝ)=(100005665230580237297/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5552575798392941/100000000000000000000 : ℝ) ≤ ((88808307607631323933/88810000000000000000 : ℝ)+2*(95398935307/888100000000000 : ℝ)*(3587/20000 : ℝ))^(5839/1024 : ℝ) := by
    rw [show (88808307607631323933/88810000000000000000 : ℝ)+2*(95398935307/888100000000000 : ℝ)*(3587/20000 : ℝ)=(10000194749176983/10000000000000000 : ℝ) by norm_num, show 1+2*(5552575798392941/100000000000000000000 : ℝ)=(50005552575798392941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88808307607631323933/88810000000000000000 : ℝ)*(X 1 0+X 2 0)+(95398935307/888100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (4527/50000 : ℝ)) (hi := (3587/20000 : ℝ)) (c := (88808307607631323933/88810000000000000000 : ℝ)) (alpha := (95398935307/888100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88808307607631323933/88810000000000000000 : ℝ)*(X 0 1+X 2 1)+(95398935307/888100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (4527/50000 : ℝ)) (hi := (3587/20000 : ℝ)) (c := (88808307607631323933/88810000000000000000 : ℝ)) (alpha := (95398935307/888100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88808307607631323933/88810000000000000000 : ℝ)*(X 0 2+X 1 2)+(95398935307/888100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5839/1024 : ℝ)) (lo := (4527/50000 : ℝ)) (hi := (3587/20000 : ℝ)) (c := (88808307607631323933/88810000000000000000 : ℝ)) (alpha := (95398935307/888100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-298708723/2500000000 : ℝ)*X 0 0+(5490391401/10000000000 : ℝ)*X 0 1+(2541241167/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((533280467/1000000000 : ℝ)*X 1 0+(-704016629/5000000000 : ℝ)*X 1 1+(1016496463/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2666402333/5000000000 : ℝ)*X 2 0+(5082482321/10000000000 : ℝ)*X 2 1+(-281606651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4010595221/10000000000 : ℝ)*X 0 0+(335778947/1000000000 : ℝ)*X 0 1+(59067309/125000000 : ℝ)*X 0 2+(4010595221/10000000000 : ℝ)*X 1 0+(335778947/1000000000 : ℝ)*X 1 1+(59067309/125000000 : ℝ)*X 1 2+(4010595221/10000000000 : ℝ)*X 2 0+(335778947/1000000000 : ℝ)*X 2 1+(59067309/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1195175767/10000000000 : ℝ)*X 0 0+(508917177/1000000000 : ℝ)*X 0 1+(1370890497/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224829377/10000000000 : ℝ)*X 1 0+(-201390727/2000000000 : ℝ)*X 1 1+(2741781013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((653103673/1250000000 : ℝ)*X 2 0+(5483562033/10000000000 : ℝ)*X 2 1+(-201390723/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2005868991/5000000000 : ℝ)*X 0 0+(2351478637/5000000000 : ℝ)*X 0 1+(3380686083/10000000000 : ℝ)*X 0 2+(2005868991/5000000000 : ℝ)*X 1 0+(2351478637/5000000000 : ℝ)*X 1 1+(3380686083/10000000000 : ℝ)*X 1 2+(2005868991/5000000000 : ℝ)*X 2 0+(2351478637/5000000000 : ℝ)*X 2 1+(3380686083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1755_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13758594819623893295652601287/1110125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43190683/2500000000000 : ℝ)*(base19) + (80712729/5000000000000 : ℝ)*(base23) + (59478847/100000000000000 : ℝ)*(lower2) + (11856799/4000000000000 : ℝ)*(upper3) + (43656653/20000000000000 : ℝ)*(upper5) + (795693333237887/50000000000000 : ℝ)*(major0) + (795693333237887/50000000000000 : ℝ)*(major1) + (795693333237887/50000000000000 : ℝ)*(major2) + (1225770291523053/50000000000000 : ℝ)*(sp0) + (2451552530654011/100000000000000 : ℝ)*(sp1) + (9806210576107/400000000000 : ℝ)*(sp2) + (91401784462907/12500000000000 : ℝ)*(sp3) + (547009409/4000000000000 : ℝ)*(sp4) + (219292123/5000000000000 : ℝ)*(sp7) + (182804665386429/25000000000000 : ℝ)*(f.failure) + (245155425828133/10000000000000 : ℝ)*(f.sum) + (146781701788173/44405000000000000000000000000 : ℝ)*base65 + (1133274313478349571/4440500000000000000000000000000000 : ℝ)*base67 + (1238291747714349571/4440500000000000000000000000000000 : ℝ)*base69 + (9052082128703349571/4440500000000000000000000000000000 : ℝ)*base71 + (1708391277901/5550625000000000000000000000 : ℝ)*base73 + (24828316969506150429/4440500000000000000000000000000000 : ℝ)*base76 + (47179173699438349571/4440500000000000000000000000000000 : ℝ)*base77 + (40309345803121349571/4440500000000000000000000000000000 : ℝ)*base79 + (1046719017301/1387656250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (10501817/1250000000000000000000 : ℝ)*base90 + (10501817/1250000000000000000000 : ℝ)*base92 + (10501817/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18369088533584394809604956751/2220250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1044582461/100000000000000 : ℝ)*(base19) + (568485059/50000000000000 : ℝ)*(base23) + (73451023/25000000000000 : ℝ)*(lower1) + (187610193/100000000000000 : ℝ)*(upper3) + (18305443/50000000000000 : ℝ)*(lower4) + (164606943/100000000000000 : ℝ)*(upper5) + (822956052789517/50000000000000 : ℝ)*(major0) + (822956052789517/50000000000000 : ℝ)*(major1) + (822956052789517/50000000000000 : ℝ)*(major2) + (457753033/50000000000000 : ℝ)*(sp2) + (1267775820070551/50000000000000 : ℝ)*(sp4) + (1267775297779321/50000000000000 : ℝ)*(sp5) + (1267774793832459/50000000000000 : ℝ)*(sp6) + (756272295235869/100000000000000 : ℝ)*(sp7) + (756272295235869/100000000000000 : ℝ)*(f.failure) + (1267775820070551/50000000000000 : ℝ)*(f.sum) + (46460783321109/22202500000000000000000000000 : ℝ)*base65 + (35756890396102510361/4440500000000000000000000000000000 : ℝ)*base67 + (54853747959894010361/4440500000000000000000000000000000 : ℝ)*base69 + (4531957158489510361/4440500000000000000000000000000000 : ℝ)*base71 + (8972116546071/22202500000000000000000000000 : ℝ)*base74 + (3149907363896010361/4440500000000000000000000000000000 : ℝ)*base75 + (50799176597312510361/4440500000000000000000000000000000 : ℝ)*base77 + (37670626269032510361/4440500000000000000000000000000000 : ℝ)*base79 + (43423019936003/44405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (77310937/5000000000000000000000 : ℝ)*base90 + (77310937/5000000000000000000000 : ℝ)*base92 + (77310937/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1755_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3587/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17879/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1755_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1755_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17879/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1755_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1755_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1755_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5839/1024 : ℝ) ≤ p) (hpb : p ≤ (5855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (108817427/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17879/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1755_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
