-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1567_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:26:31.183525+00:00
-- url     : https://prove2.me/submissions/1ad30c0c-d8c6-4afb-985b-102190dadcef

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
theorem support_rectangle_w1567_s0_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-203627761/1250000000 : ℝ)*x 0 + (5871718741/10000000000 : ℝ)*x 1 + (2439073209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203627761/1250000000 : ℝ)^4631 ≤ (4865965322139/50000000000000 : ℝ)^3607 := by
    have hnat : (203627761 : ℕ)^4631*50000000000000^3607 ≤ 4865965322139^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203627761 1250000000 4865965322139 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5871718741/10000000000 : ℝ)^4631 ≤ (10096002352899/20000000000000 : ℝ)^3607 := by
    have hnat : (5871718741 : ℕ)^4631*20000000000000^3607 ≤ 10096002352899^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5871718741 10000000000 10096002352899 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2439073209/5000000000 : ℝ)^4631 ≤ (159152230303/400000000000 : ℝ)^3607 := by
    have hnat : (2439073209 : ℕ)^4631*400000000000^3607 ≤ 159152230303^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439073209 5000000000 159152230303 400000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203627761/1250000000 : ℝ), (5871718741/10000000000 : ℝ), (2439073209/5000000000 : ℝ)] ![(4865965322139/50000000000000 : ℝ), (10096002352899/20000000000000 : ℝ), (159152230303/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203627761/1250000000 : ℝ)|^4631 ≤ (4865965322139/50000000000000 : ℝ)^3607
        have hw : |(-203627761/1250000000 : ℝ)|=(203627761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5871718741/10000000000 : ℝ)|^4631 ≤ (10096002352899/20000000000000 : ℝ)^3607
        have hw : |(5871718741/10000000000 : ℝ)|=(5871718741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2439073209/5000000000 : ℝ)|^4631 ≤ (159152230303/400000000000 : ℝ)^3607
        have hw : |(2439073209/5000000000 : ℝ)|=(2439073209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s0_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2733059381/5000000000 : ℝ)*x 0 + (-218212567/1000000000 : ℝ)*x 1 + (2439073211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2733059381/5000000000 : ℝ)^4631 ≤ (46047720356767/100000000000000 : ℝ)^3607 := by
    have hnat : (2733059381 : ℕ)^4631*100000000000000^3607 ≤ 46047720356767^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733059381 5000000000 46047720356767 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218212567/1000000000 : ℝ)^4631 ≤ (442631937949/3125000000000 : ℝ)^3607 := by
    have hnat : (218212567 : ℕ)^4631*3125000000000^3607 ≤ 442631937949^3607*1000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218212567 1000000000 442631937949 3125000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2439073211/5000000000 : ℝ)^4631 ≤ (39788057617637/100000000000000 : ℝ)^3607 := by
    have hnat : (2439073211 : ℕ)^4631*100000000000000^3607 ≤ 39788057617637^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439073211 5000000000 39788057617637 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2733059381/5000000000 : ℝ), (-218212567/1000000000 : ℝ), (2439073211/5000000000 : ℝ)] ![(46047720356767/100000000000000 : ℝ), (442631937949/3125000000000 : ℝ), (39788057617637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2733059381/5000000000 : ℝ)|^4631 ≤ (46047720356767/100000000000000 : ℝ)^3607
        have hw : |(2733059381/5000000000 : ℝ)|=(2733059381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218212567/1000000000 : ℝ)|^4631 ≤ (442631937949/3125000000000 : ℝ)^3607
        have hw : |(-218212567/1000000000 : ℝ)|=(218212567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2439073211/5000000000 : ℝ)|^4631 ≤ (39788057617637/100000000000000 : ℝ)^3607
        have hw : |(2439073211/5000000000 : ℝ)|=(2439073211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s0_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093223763/2000000000 : ℝ)*x 0 + (121953659/250000000 : ℝ)*x 1 + (-1091062839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093223763/2000000000 : ℝ)^4631 ≤ (46047720930003/100000000000000 : ℝ)^3607 := by
    have hnat : (1093223763 : ℕ)^4631*100000000000000^3607 ≤ 46047720930003^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093223763 2000000000 46047720930003 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121953659/250000000 : ℝ)^4631 ≤ (19894028484189/50000000000000 : ℝ)^3607 := by
    have hnat : (121953659 : ℕ)^4631*50000000000000^3607 ≤ 19894028484189^3607*250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121953659 250000000 19894028484189 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091062839/5000000000 : ℝ)^4631 ≤ (7082111040519/50000000000000 : ℝ)^3607 := by
    have hnat : (1091062839 : ℕ)^4631*50000000000000^3607 ≤ 7082111040519^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091062839 5000000000 7082111040519 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093223763/2000000000 : ℝ), (121953659/250000000 : ℝ), (-1091062839/5000000000 : ℝ)] ![(46047720930003/100000000000000 : ℝ), (19894028484189/50000000000000 : ℝ), (7082111040519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093223763/2000000000 : ℝ)|^4631 ≤ (46047720930003/100000000000000 : ℝ)^3607
        have hw : |(1093223763/2000000000 : ℝ)|=(1093223763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121953659/250000000 : ℝ)|^4631 ≤ (19894028484189/50000000000000 : ℝ)^3607
        have hw : |(121953659/250000000 : ℝ)|=(121953659/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091062839/5000000000 : ℝ)|^4631 ≤ (7082111040519/50000000000000 : ℝ)^3607
        have hw : |(-1091062839/5000000000 : ℝ)|=(1091062839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s0_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2065312833/5000000000 : ℝ)*x 0 + (3092996547/10000000000 : ℝ)*x 1 + (1086718619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065312833/5000000000 : ℝ)^4631 ≤ (32137022898453/100000000000000 : ℝ)^3607 := by
    have hnat : (2065312833 : ℕ)^4631*100000000000000^3607 ≤ 32137022898453^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065312833 5000000000 32137022898453 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3092996547/10000000000 : ℝ)^4631 ≤ (2770843690399/12500000000000 : ℝ)^3607 := by
    have hnat : (3092996547 : ℕ)^4631*12500000000000^3607 ≤ 2770843690399^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092996547 10000000000 2770843690399 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086718619/2000000000 : ℝ)^4631 ≤ (22848113783053/50000000000000 : ℝ)^3607 := by
    have hnat : (1086718619 : ℕ)^4631*50000000000000^3607 ≤ 22848113783053^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086718619 2000000000 22848113783053 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2065312833/5000000000 : ℝ), (3092996547/10000000000 : ℝ), (1086718619/2000000000 : ℝ)] ![(32137022898453/100000000000000 : ℝ), (2770843690399/12500000000000 : ℝ), (22848113783053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2065312833/5000000000 : ℝ)|^4631 ≤ (32137022898453/100000000000000 : ℝ)^3607
        have hw : |(2065312833/5000000000 : ℝ)|=(2065312833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3092996547/10000000000 : ℝ)|^4631 ≤ (2770843690399/12500000000000 : ℝ)^3607
        have hw : |(3092996547/10000000000 : ℝ)|=(3092996547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086718619/2000000000 : ℝ)|^4631 ≤ (22848113783053/50000000000000 : ℝ)^3607
        have hw : |(1086718619/2000000000 : ℝ)|=(1086718619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s0_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-816049531/5000000000 : ℝ)*x 0 + (2451601483/5000000000 : ℝ)*x 1 + (5845774443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (816049531/5000000000 : ℝ)^4631 ≤ (975553764809/10000000000000 : ℝ)^3607 := by
    have hnat : (816049531 : ℕ)^4631*10000000000000^3607 ≤ 975553764809^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816049531 5000000000 975553764809 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2451601483/5000000000 : ℝ)^4631 ≤ (5006329869547/12500000000000 : ℝ)^3607 := by
    have hnat : (2451601483 : ℕ)^4631*12500000000000^3607 ≤ 5006329869547^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451601483 5000000000 5006329869547 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5845774443/10000000000 : ℝ)^4631 ≤ (50193823377913/100000000000000 : ℝ)^3607 := by
    have hnat : (5845774443 : ℕ)^4631*100000000000000^3607 ≤ 50193823377913^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845774443 10000000000 50193823377913 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-816049531/5000000000 : ℝ), (2451601483/5000000000 : ℝ), (5845774443/10000000000 : ℝ)] ![(975553764809/10000000000000 : ℝ), (5006329869547/12500000000000 : ℝ), (50193823377913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-816049531/5000000000 : ℝ)|^4631 ≤ (975553764809/10000000000000 : ℝ)^3607
        have hw : |(-816049531/5000000000 : ℝ)|=(816049531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2451601483/5000000000 : ℝ)|^4631 ≤ (5006329869547/12500000000000 : ℝ)^3607
        have hw : |(2451601483/5000000000 : ℝ)|=(2451601483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5845774443/10000000000 : ℝ)|^4631 ≤ (50193823377913/100000000000000 : ℝ)^3607
        have hw : |(5845774443/10000000000 : ℝ)|=(5845774443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s0_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194503989/10000000000 : ℝ)*x 0 + (-1214499437/10000000000 : ℝ)*x 1 + (5845774741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194503989/10000000000 : ℝ)^4631 ≤ (5391370966293/12500000000000 : ℝ)^3607 := by
    have hnat : (5194503989 : ℕ)^4631*12500000000000^3607 ≤ 5391370966293^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194503989 10000000000 5391370966293 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214499437/10000000000 : ℝ)^4631 ≤ (6675205591393/100000000000000 : ℝ)^3607 := by
    have hnat : (1214499437 : ℕ)^4631*100000000000000^3607 ≤ 6675205591393^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214499437 10000000000 6675205591393 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5845774741/10000000000 : ℝ)^4631 ≤ (6274228332881/12500000000000 : ℝ)^3607 := by
    have hnat : (5845774741 : ℕ)^4631*12500000000000^3607 ≤ 6274228332881^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845774741 10000000000 6274228332881 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194503989/10000000000 : ℝ), (-1214499437/10000000000 : ℝ), (5845774741/10000000000 : ℝ)] ![(5391370966293/12500000000000 : ℝ), (6675205591393/100000000000000 : ℝ), (6274228332881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194503989/10000000000 : ℝ)|^4631 ≤ (5391370966293/12500000000000 : ℝ)^3607
        have hw : |(5194503989/10000000000 : ℝ)|=(5194503989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1214499437/10000000000 : ℝ)|^4631 ≤ (6675205591393/100000000000000 : ℝ)^3607
        have hw : |(-1214499437/10000000000 : ℝ)|=(1214499437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5845774741/10000000000 : ℝ)|^4631 ≤ (6274228332881/12500000000000 : ℝ)^3607
        have hw : |(5845774741/10000000000 : ℝ)|=(5845774741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s0_6 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298626403/2500000000 : ℝ)*x 0 + (584577413/1000000000 : ℝ)*x 1 + (-60724897/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298626403/2500000000 : ℝ)^4631 ≤ (5391373129023/12500000000000 : ℝ)^3607 := by
    have hnat : (1298626403 : ℕ)^4631*12500000000000^3607 ≤ 5391373129023^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298626403 2500000000 5391373129023 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584577413/1000000000 : ℝ)^4631 ≤ (2509690996371/5000000000000 : ℝ)^3607 := by
    have hnat : (584577413 : ℕ)^4631*5000000000000^3607 ≤ 2509690996371^3607*1000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584577413 1000000000 2509690996371 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60724897/500000000 : ℝ)^4631 ≤ (6675195027653/100000000000000 : ℝ)^3607 := by
    have hnat : (60724897 : ℕ)^4631*100000000000000^3607 ≤ 6675195027653^3607*500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60724897 500000000 6675195027653 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298626403/2500000000 : ℝ), (584577413/1000000000 : ℝ), (-60724897/500000000 : ℝ)] ![(5391373129023/12500000000000 : ℝ), (2509690996371/5000000000000 : ℝ), (6675195027653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298626403/2500000000 : ℝ)|^4631 ≤ (5391373129023/12500000000000 : ℝ)^3607
        have hw : |(1298626403/2500000000 : ℝ)|=(1298626403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(584577413/1000000000 : ℝ)|^4631 ≤ (2509690996371/5000000000000 : ℝ)^3607
        have hw : |(584577413/1000000000 : ℝ)|=(584577413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60724897/500000000 : ℝ)|^4631 ≤ (6675195027653/100000000000000 : ℝ)^3607
        have hw : |(-60724897/500000000 : ℝ)|=(60724897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s0_7 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4137873409/10000000000 : ℝ)*x 0 + (2687283773/5000000000 : ℝ)*x 1 + (1577056641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137873409/10000000000 : ℝ)^4631 ≤ (1965908083/6103515625 : ℝ)^3607 := by
    have hnat : (4137873409 : ℕ)^4631*6103515625^3607 ≤ 1965908083^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137873409 10000000000 1965908083 6103515625 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687283773/5000000000 : ℝ)^4631 ≤ (22529943232161/50000000000000 : ℝ)^3607 := by
    have hnat : (2687283773 : ℕ)^4631*50000000000000^3607 ≤ 22529943232161^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687283773 5000000000 22529943232161 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577056641/5000000000 : ℝ)^4631 ≤ (22730675489799/100000000000000 : ℝ)^3607 := by
    have hnat : (1577056641 : ℕ)^4631*100000000000000^3607 ≤ 22730675489799^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577056641 5000000000 22730675489799 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137873409/10000000000 : ℝ), (2687283773/5000000000 : ℝ), (1577056641/5000000000 : ℝ)] ![(1965908083/6103515625 : ℝ), (22529943232161/50000000000000 : ℝ), (22730675489799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137873409/10000000000 : ℝ)|^4631 ≤ (1965908083/6103515625 : ℝ)^3607
        have hw : |(4137873409/10000000000 : ℝ)|=(4137873409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687283773/5000000000 : ℝ)|^4631 ≤ (22529943232161/50000000000000 : ℝ)^3607
        have hw : |(2687283773/5000000000 : ℝ)|=(2687283773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577056641/5000000000 : ℝ)|^4631 ≤ (22730675489799/100000000000000 : ℝ)^3607
        have hw : |(1577056641/5000000000 : ℝ)|=(1577056641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3509/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24791/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4629/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4629 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4629*1^1024 ≤ 0^1024*1^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4629/1024 : ℝ) ≤ (794472897266716089/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4629 ≤ (794472897266716089/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4629*50000000000000000000^1024 ≤ 794472897266716089^1024*5^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 794472897266716089 50000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (794472897266716089/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4629 := by
      have hnat : (1 : ℕ)^1024*1^4629 ≤ 1^4629*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50794472897266716089/50000000000000000000 : ℝ) ≤ (5017467132883607/5000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50794472897266716089/50000000000000000000 : ℝ)^1024 ≤ (5017467132883607/5000000000000000 : ℝ)^4629 := by
      have hnat : (50794472897266716089 : ℕ)^1024*5000000000000000^4629 ≤ 5017467132883607^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50794472897266716089 50000000000000000000 5017467132883607 5000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017467132883607/5000000000000000 : ℝ)) (X := (50794472897266716089/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25794472897266716089/25000000000000000000 : ℝ) ≤ (2517467132883607/2500000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (25794472897266716089/25000000000000000000 : ℝ)^1024 ≤ (2517467132883607/2500000000000000 : ℝ)^4629 := by
      have hnat : (25794472897266716089 : ℕ)^1024*2500000000000000^4629 ≤ 2517467132883607^4629*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25794472897266716089 25000000000000000000 2517467132883607 2500000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517467132883607/2500000000000000 : ℝ)) (X := (25794472897266716089/25000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17467132883607/2000000000000000 : ℝ)*(0 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17467132883607/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(794472897266716089/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17467132883607/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17467132883607/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5017467132883607/5000000000000000 : ℝ) by norm_num, show 1+(794472897266716089/50000000000000000000 : ℝ)+(0 : ℝ)=(50794472897266716089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(794472897266716089/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17467132883607/2000000000000000 : ℝ)*(2/5 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17467132883607/2000000000000000 : ℝ)*(2/5 : ℝ)=(2517467132883607/2500000000000000 : ℝ) by norm_num, show 1+2*(794472897266716089/50000000000000000000 : ℝ)=(25794472897266716089/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17467132883607/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17467132883607/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17467132883607/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17467132883607/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17467132883607/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17467132883607/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-203627761/1250000000 : ℝ)*X 0 0+(5871718741/10000000000 : ℝ)*X 0 1+(2439073209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2733059381/5000000000 : ℝ)*X 1 0+(-218212567/1000000000 : ℝ)*X 1 1+(2439073211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1093223763/2000000000 : ℝ)*X 2 0+(121953659/250000000 : ℝ)*X 2 1+(-1091062839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2065312833/5000000000 : ℝ)*X 0 0+(3092996547/10000000000 : ℝ)*X 0 1+(1086718619/2000000000 : ℝ)*X 0 2+(2065312833/5000000000 : ℝ)*X 1 0+(3092996547/10000000000 : ℝ)*X 1 1+(1086718619/2000000000 : ℝ)*X 1 2+(2065312833/5000000000 : ℝ)*X 2 0+(3092996547/10000000000 : ℝ)*X 2 1+(1086718619/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-816049531/5000000000 : ℝ)*X 0 0+(2451601483/5000000000 : ℝ)*X 0 1+(5845774443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194503989/10000000000 : ℝ)*X 1 0+(-1214499437/10000000000 : ℝ)*X 1 1+(5845774741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1298626403/2500000000 : ℝ)*X 2 0+(584577413/1000000000 : ℝ)*X 2 1+(-60724897/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4137873409/10000000000 : ℝ)*X 0 0+(2687283773/5000000000 : ℝ)*X 0 1+(1577056641/5000000000 : ℝ)*X 0 2+(4137873409/10000000000 : ℝ)*X 1 0+(2687283773/5000000000 : ℝ)*X 1 1+(1577056641/5000000000 : ℝ)*X 1 2+(4137873409/10000000000 : ℝ)*X 2 0+(2687283773/5000000000 : ℝ)*X 2 1+(1577056641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (342976670830060100371719/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8060939/25000000000000 : ℝ)*(base1) + (693597807/100000000000000 : ℝ)*(base19) + (703356669/100000000000000 : ℝ)*(base23) + (89177011/100000000000000 : ℝ)*(upper3) + (44657287/50000000000000 : ℝ)*(upper5) + (716859028584261/100000000000000 : ℝ)*(major0) + (716859028584261/100000000000000 : ℝ)*(major1) + (716859028584261/100000000000000 : ℝ)*(major2) + (251617925942461/25000000000000 : ℝ)*(sp0) + (1006473569288149/100000000000000 : ℝ)*(sp1) + (503236779764643/50000000000000 : ℝ)*(sp2) + (213621273669791/50000000000000 : ℝ)*(sp3) + (647839967/25000000000000 : ℝ)*(sp4) + (220074733/20000000000000 : ℝ)*(sp7) + (106810919989251/25000000000000 : ℝ)*(f.failure) + (251618565721489/25000000000000 : ℝ)*(f.sum) + (2593045790573/100000000000000000000000000000 : ℝ)*base66 + (783496837909427/200000000000000000000000000000 : ℝ)*base67 + (737644277909427/200000000000000000000000000000 : ℝ)*base69 + (89807721890573/200000000000000000000000000000 : ℝ)*base72 + (117198243709427/100000000000000000000000000000 : ℝ)*base73 + (226428165509427/200000000000000000000000000000 : ℝ)*base75 + (1007199367709427/200000000000000000000000000000 : ℝ)*base77 + (1643920024309427/200000000000000000000000000000 : ℝ)*base79 + (158450186090573/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3338481/625000000000000000000 : ℝ)*base89 + (3338481/625000000000000000000 : ℝ)*base91 + (3338481/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (535808087602490074841529/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137281339/25000000000000 : ℝ)*(base19) + (63654721/6250000000000 : ℝ)*(base23) + (41130597/100000000000000 : ℝ)*(base39) + (38016711/20000000000000 : ℝ)*(upper3) + (32079543/25000000000000 : ℝ)*(upper5) + (377821513767973/50000000000000 : ℝ)*(major0) + (377821513767973/50000000000000 : ℝ)*(major1) + (755642986405349/100000000000000 : ℝ)*(major2) + (143962541/20000000000000 : ℝ)*(sp1) + (645779657/25000000000000 : ℝ)*(sp2) + (265231781176581/25000000000000 : ℝ)*(sp4) + (530462927884131/50000000000000 : ℝ)*(sp5) + (1060923564242757/100000000000000 : ℝ)*(sp6) + (45035871063227/10000000000000 : ℝ)*(sp7) + (45035871063227/10000000000000 : ℝ)*(f.failure) + (1060927165836921/100000000000000 : ℝ)*(f.sum) + (19190300509787/40000000000000000000000000000 : ℝ)*base66 + (770835541586157/200000000000000000000000000000 : ℝ)*base68 + (478369353881389/100000000000000000000000000000 : ℝ)*base70 + (762297612386157/200000000000000000000000000000 : ℝ)*base72 + (71859170130213/40000000000000000000000000000 : ℝ)*base73 + (138102234118611/100000000000000000000000000000 : ℝ)*base75 + (590415240081389/100000000000000000000000000000 : ℝ)*base78 + (1065838577681389/100000000000000000000000000000 : ℝ)*base80 + (40606424518611/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1960937/250000000000000000000 : ℝ)*base89 + (1960937/250000000000000000000 : ℝ)*base91 + (1960937/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1567_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3509/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24791/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1567_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1567_s1_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1768386197/10000000000 : ℝ)*x 0 + (5536540353/10000000000 : ℝ)*x 1 + (1280877957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1768386197/10000000000 : ℝ)^4631 ≤ (5406795689383/50000000000000 : ℝ)^3607 := by
    have hnat : (1768386197 : ℕ)^4631*50000000000000^3607 ≤ 5406795689383^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768386197 10000000000 5406795689383 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5536540353/10000000000 : ℝ)^4631 ≤ (46810773177449/100000000000000 : ℝ)^3607 := by
    have hnat : (5536540353 : ℕ)^4631*100000000000000^3607 ≤ 46810773177449^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536540353 10000000000 46810773177449 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280877957/2500000000 : ℝ)^4631 ≤ (42375635431183/100000000000000 : ℝ)^3607 := by
    have hnat : (1280877957 : ℕ)^4631*100000000000000^3607 ≤ 42375635431183^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280877957 2500000000 42375635431183 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1768386197/10000000000 : ℝ), (5536540353/10000000000 : ℝ), (1280877957/2500000000 : ℝ)] ![(5406795689383/50000000000000 : ℝ), (46810773177449/100000000000000 : ℝ), (42375635431183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1768386197/10000000000 : ℝ)|^4631 ≤ (5406795689383/50000000000000 : ℝ)^3607
        have hw : |(-1768386197/10000000000 : ℝ)|=(1768386197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5536540353/10000000000 : ℝ)|^4631 ≤ (46810773177449/100000000000000 : ℝ)^3607
        have hw : |(5536540353/10000000000 : ℝ)|=(5536540353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1280877957/2500000000 : ℝ)|^4631 ≤ (42375635431183/100000000000000 : ℝ)^3607
        have hw : |(1280877957/2500000000 : ℝ)|=(1280877957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s1_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688472797/5000000000 : ℝ)*x 0 + (-992248593/5000000000 : ℝ)*x 1 + (5123511659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688472797/5000000000 : ℝ)^4631 ≤ (45085485469927/100000000000000 : ℝ)^3607 := by
    have hnat : (2688472797 : ℕ)^4631*100000000000000^3607 ≤ 45085485469927^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688472797 5000000000 45085485469927 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992248593/5000000000 : ℝ)^4631 ≤ (626944044043/5000000000000 : ℝ)^3607 := by
    have hnat : (992248593 : ℕ)^4631*5000000000000^3607 ≤ 626944044043^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992248593 5000000000 626944044043 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123511659/10000000000 : ℝ)^4631 ≤ (42375633636599/100000000000000 : ℝ)^3607 := by
    have hnat : (5123511659 : ℕ)^4631*100000000000000^3607 ≤ 42375633636599^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123511659 10000000000 42375633636599 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688472797/5000000000 : ℝ), (-992248593/5000000000 : ℝ), (5123511659/10000000000 : ℝ)] ![(45085485469927/100000000000000 : ℝ), (626944044043/5000000000000 : ℝ), (42375633636599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688472797/5000000000 : ℝ)|^4631 ≤ (45085485469927/100000000000000 : ℝ)^3607
        have hw : |(2688472797/5000000000 : ℝ)|=(2688472797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992248593/5000000000 : ℝ)|^4631 ≤ (626944044043/5000000000000 : ℝ)^3607
        have hw : |(-992248593/5000000000 : ℝ)|=(992248593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123511659/10000000000 : ℝ)|^4631 ≤ (42375633636599/100000000000000 : ℝ)^3607
        have hw : |(5123511659/10000000000 : ℝ)|=(5123511659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s1_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10753891/20000000 : ℝ)*x 0 + (2561756047/5000000000 : ℝ)*x 1 + (-1984496741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10753891/20000000 : ℝ)^4631 ≤ (2254274222899/5000000000000 : ℝ)^3607 := by
    have hnat : (10753891 : ℕ)^4631*5000000000000^3607 ≤ 2254274222899^3607*20000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10753891 20000000 2254274222899 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2561756047/5000000000 : ℝ)^4631 ≤ (8475127651159/20000000000000 : ℝ)^3607 := by
    have hnat : (2561756047 : ℕ)^4631*20000000000000^3607 ≤ 8475127651159^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561756047 5000000000 8475127651159 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984496741/10000000000 : ℝ)^4631 ≤ (2507775454189/20000000000000 : ℝ)^3607 := by
    have hnat : (1984496741 : ℕ)^4631*20000000000000^3607 ≤ 2507775454189^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984496741 10000000000 2507775454189 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10753891/20000000 : ℝ), (2561756047/5000000000 : ℝ), (-1984496741/10000000000 : ℝ)] ![(2254274222899/5000000000000 : ℝ), (8475127651159/20000000000000 : ℝ), (2507775454189/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10753891/20000000 : ℝ)|^4631 ≤ (2254274222899/5000000000000 : ℝ)^3607
        have hw : |(10753891/20000000 : ℝ)|=(10753891/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2561756047/5000000000 : ℝ)|^4631 ≤ (8475127651159/20000000000000 : ℝ)^3607
        have hw : |(2561756047/5000000000 : ℝ)|=(2561756047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984496741/10000000000 : ℝ)|^4631 ≤ (2507775454189/20000000000000 : ℝ)^3607
        have hw : |(-1984496741/10000000000 : ℝ)|=(1984496741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s1_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4229552527/10000000000 : ℝ)*x 0 + (470708191/1250000000 : ℝ)*x 1 + (296165881/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229552527/10000000000 : ℝ)^4631 ≤ (33128535523691/100000000000000 : ℝ)^3607 := by
    have hnat : (4229552527 : ℕ)^4631*100000000000000^3607 ≤ 33128535523691^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229552527 10000000000 33128535523691 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470708191/1250000000 : ℝ)^4631 ≤ (28538189915117/100000000000000 : ℝ)^3607 := by
    have hnat : (470708191 : ℕ)^4631*100000000000000^3607 ≤ 28538189915117^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470708191 1250000000 28538189915117 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296165881/625000000 : ℝ)^4631 ≤ (38333274545031/100000000000000 : ℝ)^3607 := by
    have hnat : (296165881 : ℕ)^4631*100000000000000^3607 ≤ 38333274545031^3607*625000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296165881 625000000 38333274545031 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229552527/10000000000 : ℝ), (470708191/1250000000 : ℝ), (296165881/625000000 : ℝ)] ![(33128535523691/100000000000000 : ℝ), (28538189915117/100000000000000 : ℝ), (38333274545031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229552527/10000000000 : ℝ)|^4631 ≤ (33128535523691/100000000000000 : ℝ)^3607
        have hw : |(4229552527/10000000000 : ℝ)|=(4229552527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(470708191/1250000000 : ℝ)|^4631 ≤ (28538189915117/100000000000000 : ℝ)^3607
        have hw : |(470708191/1250000000 : ℝ)|=(470708191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(296165881/625000000 : ℝ)|^4631 ≤ (38333274545031/100000000000000 : ℝ)^3607
        have hw : |(296165881/625000000 : ℝ)|=(296165881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s1_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1768601289/10000000000 : ℝ)*x 0 + (5127790393/10000000000 : ℝ)*x 1 + (345762399/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1768601289/10000000000 : ℝ)^4631 ≤ (10815280081601/100000000000000 : ℝ)^3607 := by
    have hnat : (1768601289 : ℕ)^4631*100000000000000^3607 ≤ 10815280081601^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768601289 10000000000 10815280081601 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127790393/10000000000 : ℝ)^4631 ≤ (21210537108607/50000000000000 : ℝ)^3607 := by
    have hnat : (5127790393 : ℕ)^4631*50000000000000^3607 ≤ 21210537108607^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127790393 10000000000 21210537108607 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345762399/625000000 : ℝ)^4631 ≤ (292272785523/625000000000 : ℝ)^3607 := by
    have hnat : (345762399 : ℕ)^4631*625000000000^3607 ≤ 292272785523^3607*625000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345762399 625000000 292272785523 625000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1768601289/10000000000 : ℝ), (5127790393/10000000000 : ℝ), (345762399/625000000 : ℝ)] ![(10815280081601/100000000000000 : ℝ), (21210537108607/50000000000000 : ℝ), (292272785523/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1768601289/10000000000 : ℝ)|^4631 ≤ (10815280081601/100000000000000 : ℝ)^3607
        have hw : |(-1768601289/10000000000 : ℝ)|=(1768601289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127790393/10000000000 : ℝ)|^4631 ≤ (21210537108607/50000000000000 : ℝ)^3607
        have hw : |(5127790393/10000000000 : ℝ)|=(5127790393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345762399/625000000 : ℝ)|^4631 ≤ (292272785523/625000000000 : ℝ)^3607
        have hw : |(345762399/625000000 : ℝ)|=(345762399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s1_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267497087/10000000000 : ℝ)*x 0 + (-393952591/2500000000 : ℝ)*x 1 + (5532198797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267497087/10000000000 : ℝ)^4631 ≤ (21955325363759/50000000000000 : ℝ)^3607 := by
    have hnat : (5267497087 : ℕ)^4631*50000000000000^3607 ≤ 21955325363759^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267497087 10000000000 21955325363759 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393952591/2500000000 : ℝ)^4631 ≤ (9325699096421/100000000000000 : ℝ)^3607 := by
    have hnat : (393952591 : ℕ)^4631*100000000000000^3607 ≤ 9325699096421^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393952591 2500000000 9325699096421 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5532198797/10000000000 : ℝ)^4631 ≤ (2338182508293/5000000000000 : ℝ)^3607 := by
    have hnat : (5532198797 : ℕ)^4631*5000000000000^3607 ≤ 2338182508293^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5532198797 10000000000 2338182508293 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267497087/10000000000 : ℝ), (-393952591/2500000000 : ℝ), (5532198797/10000000000 : ℝ)] ![(21955325363759/50000000000000 : ℝ), (9325699096421/100000000000000 : ℝ), (2338182508293/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267497087/10000000000 : ℝ)|^4631 ≤ (21955325363759/50000000000000 : ℝ)^3607
        have hw : |(5267497087/10000000000 : ℝ)|=(5267497087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393952591/2500000000 : ℝ)|^4631 ≤ (9325699096421/100000000000000 : ℝ)^3607
        have hw : |(-393952591/2500000000 : ℝ)|=(393952591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5532198797/10000000000 : ℝ)|^4631 ≤ (2338182508293/5000000000000 : ℝ)^3607
        have hw : |(5532198797/10000000000 : ℝ)|=(5532198797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s1_6 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658437079/1250000000 : ℝ)*x 0 + (5532198961/10000000000 : ℝ)*x 1 + (-157581077/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658437079/1250000000 : ℝ)^4631 ≤ (2195532292889/5000000000000 : ℝ)^3607 := by
    have hnat : (658437079 : ℕ)^4631*5000000000000^3607 ≤ 2195532292889^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658437079 1250000000 2195532292889 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5532198961/10000000000 : ℝ)^4631 ≤ (46763651945709/100000000000000 : ℝ)^3607 := by
    have hnat : (5532198961 : ℕ)^4631*100000000000000^3607 ≤ 46763651945709^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5532198961 10000000000 46763651945709 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157581077/1000000000 : ℝ)^4631 ≤ (4662851090629/50000000000000 : ℝ)^3607 := by
    have hnat : (157581077 : ℕ)^4631*50000000000000^3607 ≤ 4662851090629^3607*1000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157581077 1000000000 4662851090629 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658437079/1250000000 : ℝ), (5532198961/10000000000 : ℝ), (-157581077/1000000000 : ℝ)] ![(2195532292889/5000000000000 : ℝ), (46763651945709/100000000000000 : ℝ), (4662851090629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658437079/1250000000 : ℝ)|^4631 ≤ (2195532292889/5000000000000 : ℝ)^3607
        have hw : |(658437079/1250000000 : ℝ)|=(658437079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5532198961/10000000000 : ℝ)|^4631 ≤ (46763651945709/100000000000000 : ℝ)^3607
        have hw : |(5532198961/10000000000 : ℝ)|=(5532198961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157581077/1000000000 : ℝ)|^4631 ≤ (4662851090629/50000000000000 : ℝ)^3607
        have hw : |(-157581077/1000000000 : ℝ)|=(157581077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s1_7 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2115029017/5000000000 : ℝ)*x 0 + (5910719/12500000 : ℝ)*x 1 + (943973577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115029017/5000000000 : ℝ)^4631 ≤ (33133619119291/100000000000000 : ℝ)^3607 := by
    have hnat : (2115029017 : ℕ)^4631*100000000000000^3607 ≤ 33133619119291^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115029017 5000000000 33133619119291 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5910719/12500000 : ℝ)^4631 ≤ (38228626454439/100000000000000 : ℝ)^3607 := by
    have hnat : (5910719 : ℕ)^4631*100000000000000^3607 ≤ 38228626454439^3607*12500000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910719 12500000 38228626454439 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943973577/2500000000 : ℝ)^4631 ≤ (2863775440407/10000000000000 : ℝ)^3607 := by
    have hnat : (943973577 : ℕ)^4631*10000000000000^3607 ≤ 2863775440407^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943973577 2500000000 2863775440407 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115029017/5000000000 : ℝ), (5910719/12500000 : ℝ), (943973577/2500000000 : ℝ)] ![(33133619119291/100000000000000 : ℝ), (38228626454439/100000000000000 : ℝ), (2863775440407/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115029017/5000000000 : ℝ)|^4631 ≤ (33133619119291/100000000000000 : ℝ)^3607
        have hw : |(2115029017/5000000000 : ℝ)|=(2115029017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5910719/12500000 : ℝ)|^4631 ≤ (38228626454439/100000000000000 : ℝ)^3607
        have hw : |(5910719/12500000 : ℝ)|=(5910719/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943973577/2500000000 : ℝ)|^4631 ≤ (2863775440407/10000000000000 : ℝ)^3607
        have hw : |(943973577/2500000000 : ℝ)|=(943973577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2259/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8891/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3509/100000 : ℝ) ^ (4629/1024 : ℝ) ≤ (13257451731803/50000000000000000000 : ℝ) := by
    have hpowers : (3509/100000 : ℝ)^4629 ≤ (13257451731803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3509 : ℕ)^4629*50000000000000000000^1024 ≤ 13257451731803^1024*100000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3509 100000 13257451731803 50000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3509/100000 : ℝ)) (X := (13257451731803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24791/100000 : ℝ) ^ (4629/1024 : ℝ) ≤ (182768564130853563/100000000000000000000 : ℝ) := by
    have hpowers : (24791/100000 : ℝ)^4629 ≤ (182768564130853563/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24791 : ℕ)^4629*100000000000000000000^1024 ≤ 182768564130853563^1024*100000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24791 100000 182768564130853563 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24791/100000 : ℝ)) (X := (182768564130853563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013257451731803/25000000000000000000 : ℝ) ≤ (10000001173093781/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (25000013257451731803/25000000000000000000 : ℝ)^1024 ≤ (10000001173093781/10000000000000000 : ℝ)^4629 := by
      have hnat : (25000013257451731803 : ℕ)^1024*10000000000000000^4629 ≤ 10000001173093781^4629*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013257451731803 25000000000000000000 10000001173093781 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001173093781/10000000000000000 : ℝ)) (X := (25000013257451731803/25000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100182795079034317169/100000000000000000000 : ℝ) ≤ (2501010202368467/2500000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (100182795079034317169/100000000000000000000 : ℝ)^1024 ≤ (2501010202368467/2500000000000000 : ℝ)^4629 := by
      have hnat : (100182795079034317169 : ℕ)^1024*2500000000000000^4629 ≤ 2501010202368467^4629*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100182795079034317169 100000000000000000000 2501010202368467 2500000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501010202368467/2500000000000000 : ℝ)) (X := (100182795079034317169/100000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50182768564130853563/50000000000000000000 : ℝ) ≤ (2001616089170791/2000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50182768564130853563/50000000000000000000 : ℝ)^1024 ≤ (2001616089170791/2000000000000000 : ℝ)^4629 := by
      have hnat : (50182768564130853563 : ℕ)^1024*2000000000000000^4629 ≤ 2001616089170791^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50182768564130853563 50000000000000000000 2001616089170791 2000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001616089170791/2000000000000000 : ℝ)) (X := (50182768564130853563/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13257451731803/50000000000000000000 : ℝ) ≤ ((17732639566472199723/17735000000000000000 : ℝ)+2*(1346545460029/709400000000000 : ℝ)*(3509/100000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (17732639566472199723/17735000000000000000 : ℝ)+2*(1346545460029/709400000000000 : ℝ)*(3509/100000 : ℝ)=(10000001173093781/10000000000000000 : ℝ) by norm_num, show 1+2*(13257451731803/50000000000000000000 : ℝ)=(25000013257451731803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(182768564130853563/100000000000000000000 : ℝ)+(13257451731803/50000000000000000000 : ℝ) ≤ ((17732639566472199723/17735000000000000000 : ℝ)+(1346545460029/709400000000000 : ℝ)*((24791/100000 : ℝ)+(3509/100000 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (17732639566472199723/17735000000000000000 : ℝ)+(1346545460029/709400000000000 : ℝ)*((24791/100000 : ℝ)+(3509/100000 : ℝ))=(2501010202368467/2500000000000000 : ℝ) by norm_num, show 1+(182768564130853563/100000000000000000000 : ℝ)+(13257451731803/50000000000000000000 : ℝ)=(100182795079034317169/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(182768564130853563/100000000000000000000 : ℝ) ≤ ((17732639566472199723/17735000000000000000 : ℝ)+2*(1346545460029/709400000000000 : ℝ)*(24791/100000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (17732639566472199723/17735000000000000000 : ℝ)+2*(1346545460029/709400000000000 : ℝ)*(24791/100000 : ℝ)=(2001616089170791/2000000000000000 : ℝ) by norm_num, show 1+2*(182768564130853563/100000000000000000000 : ℝ)=(50182768564130853563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17732639566472199723/17735000000000000000 : ℝ)*(X 1 0+X 2 0)+(1346545460029/709400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (3509/100000 : ℝ)) (hi := (24791/100000 : ℝ)) (c := (17732639566472199723/17735000000000000000 : ℝ)) (alpha := (1346545460029/709400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17732639566472199723/17735000000000000000 : ℝ)*(X 0 1+X 2 1)+(1346545460029/709400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (3509/100000 : ℝ)) (hi := (24791/100000 : ℝ)) (c := (17732639566472199723/17735000000000000000 : ℝ)) (alpha := (1346545460029/709400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17732639566472199723/17735000000000000000 : ℝ)*(X 0 2+X 1 2)+(1346545460029/709400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (3509/100000 : ℝ)) (hi := (24791/100000 : ℝ)) (c := (17732639566472199723/17735000000000000000 : ℝ)) (alpha := (1346545460029/709400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1768386197/10000000000 : ℝ)*X 0 0+(5536540353/10000000000 : ℝ)*X 0 1+(1280877957/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688472797/5000000000 : ℝ)*X 1 0+(-992248593/5000000000 : ℝ)*X 1 1+(5123511659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((10753891/20000000 : ℝ)*X 2 0+(2561756047/5000000000 : ℝ)*X 2 1+(-1984496741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4229552527/10000000000 : ℝ)*X 0 0+(470708191/1250000000 : ℝ)*X 0 1+(296165881/625000000 : ℝ)*X 0 2+(4229552527/10000000000 : ℝ)*X 1 0+(470708191/1250000000 : ℝ)*X 1 1+(296165881/625000000 : ℝ)*X 1 2+(4229552527/10000000000 : ℝ)*X 2 0+(470708191/1250000000 : ℝ)*X 2 1+(296165881/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1768601289/10000000000 : ℝ)*X 0 0+(5127790393/10000000000 : ℝ)*X 0 1+(345762399/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5267497087/10000000000 : ℝ)*X 1 0+(-393952591/2500000000 : ℝ)*X 1 1+(5532198797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((658437079/1250000000 : ℝ)*X 2 0+(5532198961/10000000000 : ℝ)*X 2 1+(-157581077/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2115029017/5000000000 : ℝ)*X 0 0+(5910719/12500000 : ℝ)*X 0 1+(943973577/2500000000 : ℝ)*X 0 2+(2115029017/5000000000 : ℝ)*X 1 0+(5910719/12500000 : ℝ)*X 1 1+(943973577/2500000000 : ℝ)*X 1 2+(2115029017/5000000000 : ℝ)*X 2 0+(5910719/12500000 : ℝ)*X 2 1+(943973577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8161851340356616576311/8867500000000000000000000000 : ℝ) := by norm_num
    linear_combination (13697759/25000000000000 : ℝ)*(base1) + (62961803/10000000000000 : ℝ)*(base19) + (617936189/100000000000000 : ℝ)*(base23) + (27254099/25000000000000 : ℝ)*(upper5) + (431115153601763/25000000000000 : ℝ)*(major0) + (431115153601763/25000000000000 : ℝ)*(major1) + (431115153601763/25000000000000 : ℝ)*(major2) + (605286435807491/25000000000000 : ℝ)*(sp0) + (484230176680637/20000000000000 : ℝ)*(sp1) + (1210576200296957/50000000000000 : ℝ)*(sp2) + (41110600676621/4000000000000 : ℝ)*(sp3) + (293203647/4000000000000 : ℝ)*(sp4) + (1505508889/100000000000000 : ℝ)*(sp5) + (3107896667/100000000000000 : ℝ)*(sp7) + (256942044900807/25000000000000 : ℝ)*(f.failure) + (2421153018530103/100000000000000 : ℝ)*(f.sum) + (5702170690701/4433750000000000000000000000 : ℝ)*base65 + (498478071362961649/443375000000000000000000000000000 : ℝ)*base67 + (88367563495413351/443375000000000000000000000000000 : ℝ)*base70 + (577098249026336649/443375000000000000000000000000000 : ℝ)*base71 + (553136208417/2216875000000000000000000000 : ℝ)*base74 + (3705493995199413351/443375000000000000000000000000000 : ℝ)*base76 + (3841108051332711649/443375000000000000000000000000000 : ℝ)*base77 + (360772414062413351/443375000000000000000000000000000 : ℝ)*base80 + (118983337477/2216875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2088083/625000000000000000000 : ℝ)*base90 + (2088083/625000000000000000000 : ℝ)*base92 + (2088083/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (223950969069293852124421653/110843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (323384217/100000000000000 : ℝ)*(base19) + (65470069/25000000000000 : ℝ)*(base23) + (85344081/100000000000000 : ℝ)*(upper2) + (59761853/50000000000000 : ℝ)*(upper3) + (2870067/20000000000000 : ℝ)*(upper5) + (220151036332863/12500000000000 : ℝ)*(major0) + (220151036332863/12500000000000 : ℝ)*(major1) + (220151036332863/12500000000000 : ℝ)*(major2) + (1554763661/50000000000000 : ℝ)*(sp1) + (1315775269/50000000000000 : ℝ)*(sp2) + (2472746939808957/100000000000000 : ℝ)*(sp4) + (1236371753448709/50000000000000 : ℝ)*(sp5) + (1236372023189071/50000000000000 : ℝ)*(sp6) + (1049669574169501/100000000000000 : ℝ)*(sp7) + (1049669574169501/100000000000000 : ℝ)*(f.failure) + (2472746939808957/100000000000000 : ℝ)*(f.sum) + (123281733768727/17735000000000000000000000000 : ℝ)*base66 + (604879005754634449/221687500000000000000000000000000 : ℝ)*base67 + (83571635230678051/221687500000000000000000000000000 : ℝ)*base70 + (45575549895321949/221687500000000000000000000000000 : ℝ)*base71 + (107001207421/34638671875000000000000000 : ℝ)*base74 + (332330108192321949/221687500000000000000000000000000 : ℝ)*base75 + (160983132740303051/221687500000000000000000000000000 : ℝ)*base78 + (2502353986295196949/221687500000000000000000000000000 : ℝ)*base79 + (68204934877871/8867500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6851231/2500000000000000000000 : ℝ)*base89 + (6851231/2500000000000000000000 : ℝ)*base91 + (6851231/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1567_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8891/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1567_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1567_s2_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1787255137/10000000000 : ℝ)*x 0 + (2721102197/5000000000 : ℝ)*x 1 + (1041111107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1787255137/10000000000 : ℝ)^4631 ≤ (5480977016483/50000000000000 : ℝ)^3607 := by
    have hnat : (1787255137 : ℕ)^4631*50000000000000^3607 ≤ 5480977016483^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787255137 10000000000 5480977016483 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721102197/5000000000 : ℝ)^4631 ≤ (45789228689561/100000000000000 : ℝ)^3607 := by
    have hnat : (2721102197 : ℕ)^4631*100000000000000^3607 ≤ 45789228689561^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721102197 5000000000 45789228689561 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041111107/2000000000 : ℝ)^4631 ≤ (10812204315581/25000000000000 : ℝ)^3607 := by
    have hnat : (1041111107 : ℕ)^4631*25000000000000^3607 ≤ 10812204315581^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041111107 2000000000 10812204315581 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1787255137/10000000000 : ℝ), (2721102197/5000000000 : ℝ), (1041111107/2000000000 : ℝ)] ![(5480977016483/50000000000000 : ℝ), (45789228689561/100000000000000 : ℝ), (10812204315581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1787255137/10000000000 : ℝ)|^4631 ≤ (5480977016483/50000000000000 : ℝ)^3607
        have hw : |(-1787255137/10000000000 : ℝ)|=(1787255137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721102197/5000000000 : ℝ)|^4631 ≤ (45789228689561/100000000000000 : ℝ)^3607
        have hw : |(2721102197/5000000000 : ℝ)|=(2721102197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041111107/2000000000 : ℝ)|^4631 ≤ (10812204315581/25000000000000 : ℝ)^3607
        have hw : |(1041111107/2000000000 : ℝ)|=(1041111107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s2_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669074889/1250000000 : ℝ)*x 0 + (-477183251/2500000000 : ℝ)*x 1 + (5205555279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669074889/1250000000 : ℝ)^4631 ≤ (11205888687133/25000000000000 : ℝ)^3607 := by
    have hnat : (669074889 : ℕ)^4631*25000000000000^3607 ≤ 11205888687133^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669074889 1250000000 11205888687133 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477183251/2500000000 : ℝ)^4631 ≤ (11927630701139/100000000000000 : ℝ)^3607 := by
    have hnat : (477183251 : ℕ)^4631*100000000000000^3607 ≤ 11927630701139^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477183251 2500000000 11927630701139 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205555279/10000000000 : ℝ)^4631 ≤ (43248814531613/100000000000000 : ℝ)^3607 := by
    have hnat : (5205555279 : ℕ)^4631*100000000000000^3607 ≤ 43248814531613^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205555279 10000000000 43248814531613 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669074889/1250000000 : ℝ), (-477183251/2500000000 : ℝ), (5205555279/10000000000 : ℝ)] ![(11205888687133/25000000000000 : ℝ), (11927630701139/100000000000000 : ℝ), (43248814531613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669074889/1250000000 : ℝ)|^4631 ≤ (11205888687133/25000000000000 : ℝ)^3607
        have hw : |(669074889/1250000000 : ℝ)|=(669074889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-477183251/2500000000 : ℝ)|^4631 ≤ (11927630701139/100000000000000 : ℝ)^3607
        have hw : |(-477183251/2500000000 : ℝ)|=(477183251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205555279/10000000000 : ℝ)|^4631 ≤ (43248814531613/100000000000000 : ℝ)^3607
        have hw : |(5205555279/10000000000 : ℝ)|=(5205555279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s2_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669074893/1250000000 : ℝ)*x 0 + (520555533/1000000000 : ℝ)*x 1 + (-381746579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669074893/1250000000 : ℝ)^4631 ≤ (44823555092581/100000000000000 : ℝ)^3607 := by
    have hnat : (669074893 : ℕ)^4631*100000000000000^3607 ≤ 44823555092581^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669074893 1250000000 44823555092581 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520555533/1000000000 : ℝ)^4631 ≤ (21624407537811/50000000000000 : ℝ)^3607 := by
    have hnat : (520555533 : ℕ)^4631*50000000000000^3607 ≤ 21624407537811^3607*1000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520555533 1000000000 21624407537811 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381746579/2000000000 : ℝ)^4631 ≤ (1192762982663/10000000000000 : ℝ)^3607 := by
    have hnat : (381746579 : ℕ)^4631*10000000000000^3607 ≤ 1192762982663^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381746579 2000000000 1192762982663 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669074893/1250000000 : ℝ), (520555533/1000000000 : ℝ), (-381746579/2000000000 : ℝ)] ![(44823555092581/100000000000000 : ℝ), (21624407537811/50000000000000 : ℝ), (1192762982663/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669074893/1250000000 : ℝ)|^4631 ≤ (44823555092581/100000000000000 : ℝ)^3607
        have hw : |(669074893/1250000000 : ℝ)|=(669074893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520555533/1000000000 : ℝ)|^4631 ≤ (21624407537811/50000000000000 : ℝ)^3607
        have hw : |(520555533/1000000000 : ℝ)|=(520555533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381746579/2000000000 : ℝ)|^4631 ≤ (1192762982663/10000000000000 : ℝ)^3607
        have hw : |(-381746579/2000000000 : ℝ)|=(381746579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s2_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243221099/10000000000 : ℝ)*x 0 + (3971906769/10000000000 : ℝ)*x 1 + (4529390379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243221099/10000000000 : ℝ)^4631 ≤ (33266053230387/100000000000000 : ℝ)^3607 := by
    have hnat : (4243221099 : ℕ)^4631*100000000000000^3607 ≤ 33266053230387^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243221099 10000000000 33266053230387 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3971906769/10000000000 : ℝ)^4631 ≤ (15280160443779/50000000000000 : ℝ)^3607 := by
    have hnat : (3971906769 : ℕ)^4631*50000000000000^3607 ≤ 15280160443779^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3971906769 10000000000 15280160443779 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529390379/10000000000 : ℝ)^4631 ≤ (1446945034743/4000000000000 : ℝ)^3607 := by
    have hnat : (4529390379 : ℕ)^4631*4000000000000^3607 ≤ 1446945034743^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529390379 10000000000 1446945034743 4000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243221099/10000000000 : ℝ), (3971906769/10000000000 : ℝ), (4529390379/10000000000 : ℝ)] ![(33266053230387/100000000000000 : ℝ), (15280160443779/50000000000000 : ℝ), (1446945034743/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243221099/10000000000 : ℝ)|^4631 ≤ (33266053230387/100000000000000 : ℝ)^3607
        have hw : |(4243221099/10000000000 : ℝ)|=(4243221099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3971906769/10000000000 : ℝ)|^4631 ≤ (15280160443779/50000000000000 : ℝ)^3607
        have hw : |(3971906769/10000000000 : ℝ)|=(3971906769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529390379/10000000000 : ℝ)|^4631 ≤ (1446945034743/4000000000000 : ℝ)^3607
        have hw : |(4529390379/10000000000 : ℝ)|=(4529390379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s2_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-357459067/2000000000 : ℝ)*x 0 + (52069681/100000000 : ℝ)*x 1 + (1088156027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357459067/2000000000 : ℝ)^4631 ≤ (2740567644571/25000000000000 : ℝ)^3607 := by
    have hnat : (357459067 : ℕ)^4631*25000000000000^3607 ≤ 2740567644571^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357459067 2000000000 2740567644571 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52069681/100000000 : ℝ)^4631 ≤ (21631942723909/50000000000000 : ℝ)^3607 := by
    have hnat : (52069681 : ℕ)^4631*50000000000000^3607 ≤ 21631942723909^3607*100000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52069681 100000000 21631942723909 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088156027/2000000000 : ℝ)^4631 ≤ (4577384395683/10000000000000 : ℝ)^3607 := by
    have hnat : (1088156027 : ℕ)^4631*10000000000000^3607 ≤ 4577384395683^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088156027 2000000000 4577384395683 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357459067/2000000000 : ℝ), (52069681/100000000 : ℝ), (1088156027/2000000000 : ℝ)] ![(2740567644571/25000000000000 : ℝ), (21631942723909/50000000000000 : ℝ), (4577384395683/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357459067/2000000000 : ℝ)|^4631 ≤ (2740567644571/25000000000000 : ℝ)^3607
        have hw : |(-357459067/2000000000 : ℝ)|=(357459067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52069681/100000000 : ℝ)|^4631 ≤ (21631942723909/50000000000000 : ℝ)^3607
        have hw : |(52069681/100000000 : ℝ)|=(52069681/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088156027/2000000000 : ℝ)|^4631 ≤ (4577384395683/10000000000000 : ℝ)^3607
        have hw : |(1088156027/2000000000 : ℝ)|=(1088156027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s2_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290004551/10000000000 : ℝ)*x 0 + (-836754221/5000000000 : ℝ)*x 1 + (2720390481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290004551/10000000000 : ℝ)^4631 ≤ (44151687793837/100000000000000 : ℝ)^3607 := by
    have hnat : (5290004551 : ℕ)^4631*100000000000000^3607 ≤ 44151687793837^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290004551 10000000000 44151687793837 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836754221/5000000000 : ℝ)^4631 ≤ (10074459295441/100000000000000 : ℝ)^3607 := by
    have hnat : (836754221 : ℕ)^4631*100000000000000^3607 ≤ 10074459295441^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836754221 5000000000 10074459295441 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720390481/5000000000 : ℝ)^4631 ≤ (45773852889687/100000000000000 : ℝ)^3607 := by
    have hnat : (2720390481 : ℕ)^4631*100000000000000^3607 ≤ 45773852889687^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720390481 5000000000 45773852889687 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290004551/10000000000 : ℝ), (-836754221/5000000000 : ℝ), (2720390481/5000000000 : ℝ)] ![(44151687793837/100000000000000 : ℝ), (10074459295441/100000000000000 : ℝ), (45773852889687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290004551/10000000000 : ℝ)|^4631 ≤ (44151687793837/100000000000000 : ℝ)^3607
        have hw : |(5290004551/10000000000 : ℝ)|=(5290004551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-836754221/5000000000 : ℝ)|^4631 ≤ (10074459295441/100000000000000 : ℝ)^3607
        have hw : |(-836754221/5000000000 : ℝ)|=(836754221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720390481/5000000000 : ℝ)|^4631 ≤ (45773852889687/100000000000000 : ℝ)^3607
        have hw : |(2720390481/5000000000 : ℝ)|=(2720390481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s2_6 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661250603/1250000000 : ℝ)*x 0 + (5440782001/10000000000 : ℝ)*x 1 + (-418376653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661250603/1250000000 : ℝ)^4631 ≤ (44151690719219/100000000000000 : ℝ)^3607 := by
    have hnat : (661250603 : ℕ)^4631*100000000000000^3607 ≤ 44151690719219^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661250603 1250000000 44151690719219 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440782001/10000000000 : ℝ)^4631 ≤ (22886932056233/50000000000000 : ℝ)^3607 := by
    have hnat : (5440782001 : ℕ)^4631*50000000000000^3607 ≤ 22886932056233^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440782001 10000000000 22886932056233 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418376653/2500000000 : ℝ)^4631 ≤ (50372225757/500000000000 : ℝ)^3607 := by
    have hnat : (418376653 : ℕ)^4631*500000000000^3607 ≤ 50372225757^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418376653 2500000000 50372225757 500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661250603/1250000000 : ℝ), (5440782001/10000000000 : ℝ), (-418376653/2500000000 : ℝ)] ![(44151690719219/100000000000000 : ℝ), (22886932056233/50000000000000 : ℝ), (50372225757/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661250603/1250000000 : ℝ)|^4631 ≤ (44151690719219/100000000000000 : ℝ)^3607
        have hw : |(661250603/1250000000 : ℝ)|=(661250603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440782001/10000000000 : ℝ)|^4631 ≤ (22886932056233/50000000000000 : ℝ)^3607
        have hw : |(5440782001/10000000000 : ℝ)|=(5440782001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418376653/2500000000 : ℝ)|^4631 ≤ (50372225757/500000000000 : ℝ)^3607
        have hw : |(-418376653/2500000000 : ℝ)|=(418376653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s2_7 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530414543/1250000000 : ℝ)*x 0 + (1131515817/2500000000 : ℝ)*x 1 + (3975262467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530414543/1250000000 : ℝ)^4631 ≤ (6653402383913/20000000000000 : ℝ)^3607 := by
    have hnat : (530414543 : ℕ)^4631*20000000000000^3607 ≤ 6653402383913^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530414543 1250000000 6653402383913 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131515817/2500000000 : ℝ)^4631 ≤ (36139514203043/100000000000000 : ℝ)^3607 := by
    have hnat : (1131515817 : ℕ)^4631*100000000000000^3607 ≤ 36139514203043^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131515817 2500000000 36139514203043 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3975262467/10000000000 : ℝ)^4631 ≤ (3059347385757/10000000000000 : ℝ)^3607 := by
    have hnat : (3975262467 : ℕ)^4631*10000000000000^3607 ≤ 3059347385757^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975262467 10000000000 3059347385757 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530414543/1250000000 : ℝ), (1131515817/2500000000 : ℝ), (3975262467/10000000000 : ℝ)] ![(6653402383913/20000000000000 : ℝ), (36139514203043/100000000000000 : ℝ), (3059347385757/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530414543/1250000000 : ℝ)|^4631 ≤ (6653402383913/20000000000000 : ℝ)^3607
        have hw : |(530414543/1250000000 : ℝ)|=(530414543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131515817/2500000000 : ℝ)|^4631 ≤ (36139514203043/100000000000000 : ℝ)^3607
        have hw : |(1131515817/2500000000 : ℝ)|=(1131515817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3975262467/10000000000 : ℝ)|^4631 ≤ (3059347385757/10000000000000 : ℝ)^3607
        have hw : |(3975262467/10000000000 : ℝ)|=(3975262467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8891/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10803/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (791/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8891/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2259/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8891/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2259/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8891/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2259/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8891/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2259/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8891/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2259/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8891/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2259/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2259/25000 : ℝ) ^ (4629/1024 : ℝ) ≤ (476894556159891/25000000000000000000 : ℝ) := by
    have hpowers : (2259/25000 : ℝ)^4629 ≤ (476894556159891/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2259 : ℕ)^4629*25000000000000000000^1024 ≤ 476894556159891^1024*25000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2259 25000 476894556159891 25000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2259/25000 : ℝ)) (X := (476894556159891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8891/50000 : ℝ) ^ (4629/1024 : ℝ) ≤ (40694102016446827/100000000000000000000 : ℝ) := by
    have hpowers : (8891/50000 : ℝ)^4629 ≤ (40694102016446827/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8891 : ℕ)^4629*100000000000000000000^1024 ≤ 40694102016446827^1024*50000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8891 50000 40694102016446827 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8891/50000 : ℝ)) (X := (40694102016446827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500476894556159891/12500000000000000000 : ℝ) ≤ (10000084395380587/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (12500476894556159891/12500000000000000000 : ℝ)^1024 ≤ (10000084395380587/10000000000000000 : ℝ)^4629 := by
      have hnat : (12500476894556159891 : ℕ)^1024*10000000000000000^4629 ≤ 10000084395380587^4629*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500476894556159891 12500000000000000000 10000084395380587 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084395380587/10000000000000000 : ℝ)) (X := (12500476894556159891/12500000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042601680241086391/100000000000000000000 : ℝ) ≤ (2500235563219263/2500000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (100042601680241086391/100000000000000000000 : ℝ)^1024 ≤ (2500235563219263/2500000000000000 : ℝ)^4629 := by
      have hnat : (100042601680241086391 : ℕ)^1024*2500000000000000^4629 ≤ 2500235563219263^4629*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042601680241086391 100000000000000000000 2500235563219263 2500000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500235563219263/2500000000000000 : ℝ)) (X := (100042601680241086391/100000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040694102016446827/50000000000000000000 : ℝ) ≤ (10001800110373517/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50040694102016446827/50000000000000000000 : ℝ)^1024 ≤ (10001800110373517/10000000000000000 : ℝ)^4629 := by
      have hnat : (50040694102016446827 : ℕ)^1024*10000000000000000^4629 ≤ 10001800110373517^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040694102016446827 50000000000000000000 10001800110373517 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001800110373517/10000000000000000 : ℝ)) (X := (50040694102016446827/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(476894556159891/25000000000000000000 : ℝ) ≤ ((43722617460661249211/43730000000000000000 : ℝ)+2*(171571499293/174920000000000 : ℝ)*(2259/25000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (43722617460661249211/43730000000000000000 : ℝ)+2*(171571499293/174920000000000 : ℝ)*(2259/25000 : ℝ)=(10000084395380587/10000000000000000 : ℝ) by norm_num, show 1+2*(476894556159891/25000000000000000000 : ℝ)=(12500476894556159891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40694102016446827/100000000000000000000 : ℝ)+(476894556159891/25000000000000000000 : ℝ) ≤ ((43722617460661249211/43730000000000000000 : ℝ)+(171571499293/174920000000000 : ℝ)*((8891/50000 : ℝ)+(2259/25000 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (43722617460661249211/43730000000000000000 : ℝ)+(171571499293/174920000000000 : ℝ)*((8891/50000 : ℝ)+(2259/25000 : ℝ))=(2500235563219263/2500000000000000 : ℝ) by norm_num, show 1+(40694102016446827/100000000000000000000 : ℝ)+(476894556159891/25000000000000000000 : ℝ)=(100042601680241086391/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40694102016446827/100000000000000000000 : ℝ) ≤ ((43722617460661249211/43730000000000000000 : ℝ)+2*(171571499293/174920000000000 : ℝ)*(8891/50000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (43722617460661249211/43730000000000000000 : ℝ)+2*(171571499293/174920000000000 : ℝ)*(8891/50000 : ℝ)=(10001800110373517/10000000000000000 : ℝ) by norm_num, show 1+2*(40694102016446827/100000000000000000000 : ℝ)=(50040694102016446827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43722617460661249211/43730000000000000000 : ℝ)*(X 1 0+X 2 0)+(171571499293/174920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (2259/25000 : ℝ)) (hi := (8891/50000 : ℝ)) (c := (43722617460661249211/43730000000000000000 : ℝ)) (alpha := (171571499293/174920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43722617460661249211/43730000000000000000 : ℝ)*(X 0 1+X 2 1)+(171571499293/174920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (2259/25000 : ℝ)) (hi := (8891/50000 : ℝ)) (c := (43722617460661249211/43730000000000000000 : ℝ)) (alpha := (171571499293/174920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43722617460661249211/43730000000000000000 : ℝ)*(X 0 2+X 1 2)+(171571499293/174920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (2259/25000 : ℝ)) (hi := (8891/50000 : ℝ)) (c := (43722617460661249211/43730000000000000000 : ℝ)) (alpha := (171571499293/174920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1787255137/10000000000 : ℝ)*X 0 0+(2721102197/5000000000 : ℝ)*X 0 1+(1041111107/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669074889/1250000000 : ℝ)*X 1 0+(-477183251/2500000000 : ℝ)*X 1 1+(5205555279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669074893/1250000000 : ℝ)*X 2 0+(520555533/1000000000 : ℝ)*X 2 1+(-381746579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4243221099/10000000000 : ℝ)*X 0 0+(3971906769/10000000000 : ℝ)*X 0 1+(4529390379/10000000000 : ℝ)*X 0 2+(4243221099/10000000000 : ℝ)*X 1 0+(3971906769/10000000000 : ℝ)*X 1 1+(4529390379/10000000000 : ℝ)*X 1 2+(4243221099/10000000000 : ℝ)*X 2 0+(3971906769/10000000000 : ℝ)*X 2 1+(4529390379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-357459067/2000000000 : ℝ)*X 0 0+(52069681/100000000 : ℝ)*X 0 1+(1088156027/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290004551/10000000000 : ℝ)*X 1 0+(-836754221/5000000000 : ℝ)*X 1 1+(2720390481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661250603/1250000000 : ℝ)*X 2 0+(5440782001/10000000000 : ℝ)*X 2 1+(-418376653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530414543/1250000000 : ℝ)*X 0 0+(1131515817/2500000000 : ℝ)*X 0 1+(3975262467/10000000000 : ℝ)*X 0 2+(530414543/1250000000 : ℝ)*X 1 0+(1131515817/2500000000 : ℝ)*X 1 1+(3975262467/10000000000 : ℝ)*X 1 2+(530414543/1250000000 : ℝ)*X 2 0+(1131515817/2500000000 : ℝ)*X 2 1+(3975262467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13011533441970606107348252367/2186500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (732207209/100000000000000 : ℝ)*(base19) + (555553503/100000000000000 : ℝ)*(base23) + (108077823/100000000000000 : ℝ)*(lower2) + (111122921/100000000000000 : ℝ)*(upper3) + (30605049/50000000000000 : ℝ)*(upper5) + (3009731327518919/100000000000000 : ℝ)*(major0) + (3009731327518919/100000000000000 : ℝ)*(major1) + (75243283187973/2500000000000 : ℝ)*(major2) + (4225675042418289/100000000000000 : ℝ)*(sp0) + (264104994458809/6250000000000 : ℝ)*(sp1) + (4225680087994651/100000000000000 : ℝ)*(sp2) + (896888838828727/50000000000000 : ℝ)*(sp3) + (700141233/12500000000000 : ℝ)*(sp4) + (2067735279/50000000000000 : ℝ)*(sp7) + (448445453282003/25000000000000 : ℝ)*(f.failure) + (2112840321774077/50000000000000 : ℝ)*(f.sum) + (7128566494753/17492000000000000000000000000 : ℝ)*base66 + (23590094591461677091/4373000000000000000000000000000000 : ℝ)*base68 + (934583629554833053/109325000000000000000000000000000 : ℝ)*base69 + (34175513802168322909/4373000000000000000000000000000000 : ℝ)*base71 + (82879719566021/17492000000000000000000000000 : ℝ)*base74 + (791104174426508053/109325000000000000000000000000000 : ℝ)*base75 + (1006782443622927091/4373000000000000000000000000000000 : ℝ)*base78 + (23359410679656927091/4373000000000000000000000000000000 : ℝ)*base80 + (2537287487791/1749200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3232193/625000000000000000000 : ℝ)*base89 + (3232193/625000000000000000000 : ℝ)*base91 + (3017807/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (865626243788523715232555631/54662500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26013973/50000000000000 : ℝ)*(base19) + (1299782319/100000000000000 : ℝ)*(base23) + (28964301/12500000000000 : ℝ)*(upper3) + (26751133/10000000000000 : ℝ)*(lower4) + (7469539/6250000000000 : ℝ)*(upper5) + (152311903494093/5000000000000 : ℝ)*(major0) + (152311903494093/5000000000000 : ℝ)*(major1) + (152311903494093/5000000000000 : ℝ)*(major2) + (6194429017/100000000000000 : ℝ)*(sp1) + (1256362961/2500000000000 : ℝ)*(sp2) + (1069233999840727/25000000000000 : ℝ)*(sp4) + (855385950581189/20000000000000 : ℝ)*(sp5) + (85537688901243/2000000000000 : ℝ)*(sp6) + (1815539612539687/100000000000000 : ℝ)*(sp7) + (1815539612539687/100000000000000 : ℝ)*(f.failure) + (1069233999840727/25000000000000 : ℝ)*(f.sum) + (9297410242643/2186500000000000000000000000 : ℝ)*base65 + (2239298874768260623/218650000000000000000000000000000 : ℝ)*base67 + (2004051482773810623/218650000000000000000000000000000 : ℝ)*base69 + (2246868316713110623/218650000000000000000000000000000 : ℝ)*base71 + (6731409550239/1093250000000000000000000000 : ℝ)*base73 + (2645676135405360623/218650000000000000000000000000000 : ℝ)*base75 + (3004840919539377/218650000000000000000000000000000 : ℝ)*base78 + (338702870710760623/218650000000000000000000000000000 : ℝ)*base79 + (18876012777073/4373000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22586803/2500000000000000000000 : ℝ)*base90 + (22586803/2500000000000000000000 : ℝ)*base92 + (22586803/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1567_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8891/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10803/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (791/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1567_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1567_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10803/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (791/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1567_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1567_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1567_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10803/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (791/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1567_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
