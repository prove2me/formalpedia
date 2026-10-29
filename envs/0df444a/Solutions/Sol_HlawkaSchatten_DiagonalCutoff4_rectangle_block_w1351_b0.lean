-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:57.35946+00:00
-- url     : https://prove2.me/submissions/19f689ec-103e-4710-b284-d512aa4a36ce

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
theorem support_rectangle_w1351_s0_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360767533/2000000000 : ℝ)*x 0 + (2996519331/5000000000 : ℝ)*x 1 + (1203262963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360767533/2000000000 : ℝ)^4311 ≤ (10579872682677/100000000000000 : ℝ)^3287 := by
    have hnat : (360767533 : ℕ)^4311*100000000000000^3287 ≤ 10579872682677^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360767533 2000000000 10579872682677 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2996519331/5000000000 : ℝ)^4311 ≤ (25547441784149/50000000000000 : ℝ)^3287 := by
    have hnat : (2996519331 : ℕ)^4311*50000000000000^3287 ≤ 25547441784149^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996519331 5000000000 25547441784149 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203262963/2500000000 : ℝ)^4311 ≤ (38325243728679/100000000000000 : ℝ)^3287 := by
    have hnat : (1203262963 : ℕ)^4311*100000000000000^3287 ≤ 38325243728679^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203262963 2500000000 38325243728679 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360767533/2000000000 : ℝ), (2996519331/5000000000 : ℝ), (1203262963/2500000000 : ℝ)] ![(10579872682677/100000000000000 : ℝ), (25547441784149/50000000000000 : ℝ), (38325243728679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360767533/2000000000 : ℝ)|^4311 ≤ (10579872682677/100000000000000 : ℝ)^3287
        have hw : |(-360767533/2000000000 : ℝ)|=(360767533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2996519331/5000000000 : ℝ)|^4311 ≤ (25547441784149/50000000000000 : ℝ)^3287
        have hw : |(2996519331/5000000000 : ℝ)|=(2996519331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203262963/2500000000 : ℝ)|^4311 ≤ (38325243728679/100000000000000 : ℝ)^3287
        have hw : |(1203262963/2500000000 : ℝ)|=(1203262963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s0_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2750402473/5000000000 : ℝ)*x 0 + (-1237049627/5000000000 : ℝ)*x 1 + (4813052301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750402473/5000000000 : ℝ)^4311 ≤ (22831327713397/50000000000000 : ℝ)^3287 := by
    have hnat : (2750402473 : ℕ)^4311*50000000000000^3287 ≤ 22831327713397^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750402473 5000000000 22831327713397 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1237049627/5000000000 : ℝ)^4311 ≤ (16012096137411/100000000000000 : ℝ)^3287 := by
    have hnat : (1237049627 : ℕ)^4311*100000000000000^3287 ≤ 16012096137411^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237049627 5000000000 16012096137411 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4813052301/10000000000 : ℝ)^4311 ≤ (19162624208887/50000000000000 : ℝ)^3287 := by
    have hnat : (4813052301 : ℕ)^4311*50000000000000^3287 ≤ 19162624208887^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813052301 10000000000 19162624208887 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750402473/5000000000 : ℝ), (-1237049627/5000000000 : ℝ), (4813052301/10000000000 : ℝ)] ![(22831327713397/50000000000000 : ℝ), (16012096137411/100000000000000 : ℝ), (19162624208887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750402473/5000000000 : ℝ)|^4311 ≤ (22831327713397/50000000000000 : ℝ)^3287
        have hw : |(2750402473/5000000000 : ℝ)|=(2750402473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1237049627/5000000000 : ℝ)|^4311 ≤ (16012096137411/100000000000000 : ℝ)^3287
        have hw : |(-1237049627/5000000000 : ℝ)|=(1237049627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4813052301/10000000000 : ℝ)|^4311 ≤ (19162624208887/50000000000000 : ℝ)^3287
        have hw : |(4813052301/10000000000 : ℝ)|=(4813052301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s0_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1375201187/2500000000 : ℝ)*x 0 + (962610389/2000000000 : ℝ)*x 1 + (-1237049973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375201187/2500000000 : ℝ)^4311 ≤ (45662653271143/100000000000000 : ℝ)^3287 := by
    have hnat : (1375201187 : ℕ)^4311*100000000000000^3287 ≤ 45662653271143^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375201187 2500000000 45662653271143 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962610389/2000000000 : ℝ)^4311 ≤ (38325244699917/100000000000000 : ℝ)^3287 := by
    have hnat : (962610389 : ℕ)^4311*100000000000000^3287 ≤ 38325244699917^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962610389 2000000000 38325244699917 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237049973/5000000000 : ℝ)^4311 ≤ (16012102011161/100000000000000 : ℝ)^3287 := by
    have hnat : (1237049973 : ℕ)^4311*100000000000000^3287 ≤ 16012102011161^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237049973 5000000000 16012102011161 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375201187/2500000000 : ℝ), (962610389/2000000000 : ℝ), (-1237049973/5000000000 : ℝ)] ![(45662653271143/100000000000000 : ℝ), (38325244699917/100000000000000 : ℝ), (16012102011161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375201187/2500000000 : ℝ)|^4311 ≤ (45662653271143/100000000000000 : ℝ)^3287
        have hw : |(1375201187/2500000000 : ℝ)|=(1375201187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962610389/2000000000 : ℝ)|^4311 ≤ (38325244699917/100000000000000 : ℝ)^3287
        have hw : |(962610389/2000000000 : ℝ)|=(962610389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1237049973/5000000000 : ℝ)|^4311 ≤ (16012102011161/100000000000000 : ℝ)^3287
        have hw : |(-1237049973/5000000000 : ℝ)|=(1237049973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s0_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4177402559/10000000000 : ℝ)*x 0 + (3106131233/10000000000 : ℝ)*x 1 + (5586069997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177402559/10000000000 : ℝ)^4311 ≤ (15913920297653/50000000000000 : ℝ)^3287 := by
    have hnat : (4177402559 : ℕ)^4311*50000000000000^3287 ≤ 15913920297653^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177402559 10000000000 15913920297653 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3106131233/10000000000 : ℝ)^4311 ≤ (21578979257501/100000000000000 : ℝ)^3287 := by
    have hnat : (3106131233 : ℕ)^4311*100000000000000^3287 ≤ 21578979257501^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106131233 10000000000 21578979257501 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5586069997/10000000000 : ℝ)^4311 ≤ (9318636025923/20000000000000 : ℝ)^3287 := by
    have hnat : (5586069997 : ℕ)^4311*20000000000000^3287 ≤ 9318636025923^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586069997 10000000000 9318636025923 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177402559/10000000000 : ℝ), (3106131233/10000000000 : ℝ), (5586069997/10000000000 : ℝ)] ![(15913920297653/50000000000000 : ℝ), (21578979257501/100000000000000 : ℝ), (9318636025923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177402559/10000000000 : ℝ)|^4311 ≤ (15913920297653/50000000000000 : ℝ)^3287
        have hw : |(4177402559/10000000000 : ℝ)|=(4177402559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3106131233/10000000000 : ℝ)|^4311 ≤ (21578979257501/100000000000000 : ℝ)^3287
        have hw : |(3106131233/10000000000 : ℝ)|=(3106131233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5586069997/10000000000 : ℝ)|^4311 ≤ (9318636025923/20000000000000 : ℝ)^3287
        have hw : |(5586069997/10000000000 : ℝ)|=(5586069997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s0_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-452061821/2500000000 : ℝ)*x 0 + (121085137/250000000 : ℝ)*x 1 + (2980800481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452061821/2500000000 : ℝ)^4311 ≤ (10613806101927/100000000000000 : ℝ)^3287 := by
    have hnat : (452061821 : ℕ)^4311*100000000000000^3287 ≤ 10613806101927^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452061821 2500000000 10613806101927 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121085137/250000000 : ℝ)^4311 ≤ (19321275165897/50000000000000 : ℝ)^3287 := by
    have hnat : (121085137 : ℕ)^4311*50000000000000^3287 ≤ 19321275165897^3287*250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121085137 250000000 19321275165897 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980800481/5000000000 : ℝ)^4311 ≤ (25371821777883/50000000000000 : ℝ)^3287 := by
    have hnat : (2980800481 : ℕ)^4311*50000000000000^3287 ≤ 25371821777883^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980800481 5000000000 25371821777883 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-452061821/2500000000 : ℝ), (121085137/250000000 : ℝ), (2980800481/5000000000 : ℝ)] ![(10613806101927/100000000000000 : ℝ), (19321275165897/50000000000000 : ℝ), (25371821777883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-452061821/2500000000 : ℝ)|^4311 ≤ (10613806101927/100000000000000 : ℝ)^3287
        have hw : |(-452061821/2500000000 : ℝ)|=(452061821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121085137/250000000 : ℝ)|^4311 ≤ (19321275165897/50000000000000 : ℝ)^3287
        have hw : |(121085137/250000000 : ℝ)|=(121085137/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2980800481/5000000000 : ℝ)|^4311 ≤ (25371821777883/50000000000000 : ℝ)^3287
        have hw : |(2980800481/5000000000 : ℝ)|=(2980800481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s0_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179163643/10000000000 : ℝ)*x 0 + (-132555181/1000000000 : ℝ)*x 1 + (2980800297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179163643/10000000000 : ℝ)^4311 ≤ (42193238412673/100000000000000 : ℝ)^3287 := by
    have hnat : (5179163643 : ℕ)^4311*100000000000000^3287 ≤ 42193238412673^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179163643 10000000000 42193238412673 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132555181/1000000000 : ℝ)^4311 ≤ (7063122126693/100000000000000 : ℝ)^3287 := by
    have hnat : (132555181 : ℕ)^4311*100000000000000^3287 ≤ 7063122126693^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132555181 1000000000 7063122126693 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980800297/5000000000 : ℝ)^4311 ≤ (50743639447629/100000000000000 : ℝ)^3287 := by
    have hnat : (2980800297 : ℕ)^4311*100000000000000^3287 ≤ 50743639447629^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980800297 5000000000 50743639447629 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179163643/10000000000 : ℝ), (-132555181/1000000000 : ℝ), (2980800297/5000000000 : ℝ)] ![(42193238412673/100000000000000 : ℝ), (7063122126693/100000000000000 : ℝ), (50743639447629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179163643/10000000000 : ℝ)|^4311 ≤ (42193238412673/100000000000000 : ℝ)^3287
        have hw : |(5179163643/10000000000 : ℝ)|=(5179163643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132555181/1000000000 : ℝ)|^4311 ≤ (7063122126693/100000000000000 : ℝ)^3287
        have hw : |(-132555181/1000000000 : ℝ)|=(132555181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2980800297/5000000000 : ℝ)|^4311 ≤ (50743639447629/100000000000000 : ℝ)^3287
        have hw : |(2980800297/5000000000 : ℝ)|=(2980800297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s0_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179163579/10000000000 : ℝ)*x 0 + (745200127/1250000000 : ℝ)*x 1 + (-662775617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179163579/10000000000 : ℝ)^4311 ≤ (42193237728853/100000000000000 : ℝ)^3287 := by
    have hnat : (5179163579 : ℕ)^4311*100000000000000^3287 ≤ 42193237728853^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179163579 10000000000 42193237728853 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745200127/1250000000 : ℝ)^4311 ≤ (5074364415859/10000000000000 : ℝ)^3287 := by
    have hnat : (745200127 : ℕ)^4311*10000000000000^3287 ≤ 5074364415859^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745200127 1250000000 5074364415859 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (662775617/5000000000 : ℝ)^4311 ≤ (706311810137/10000000000000 : ℝ)^3287 := by
    have hnat : (662775617 : ℕ)^4311*10000000000000^3287 ≤ 706311810137^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662775617 5000000000 706311810137 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179163579/10000000000 : ℝ), (745200127/1250000000 : ℝ), (-662775617/5000000000 : ℝ)] ![(42193237728853/100000000000000 : ℝ), (5074364415859/10000000000000 : ℝ), (706311810137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179163579/10000000000 : ℝ)|^4311 ≤ (42193237728853/100000000000000 : ℝ)^3287
        have hw : |(5179163579/10000000000 : ℝ)|=(5179163579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(745200127/1250000000 : ℝ)|^4311 ≤ (5074364415859/10000000000000 : ℝ)^3287
        have hw : |(745200127/1250000000 : ℝ)|=(745200127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-662775617/5000000000 : ℝ)|^4311 ≤ (706311810137/10000000000000 : ℝ)^3287
        have hw : |(-662775617/5000000000 : ℝ)|=(662775617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s0_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186667403/10000000000 : ℝ)*x 0 + (1104455583/2000000000 : ℝ)*x 1 + (3965253/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186667403/10000000000 : ℝ)^4311 ≤ (31920452583223/100000000000000 : ℝ)^3287 := by
    have hnat : (4186667403 : ℕ)^4311*100000000000000^3287 ≤ 31920452583223^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186667403 10000000000 31920452583223 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104455583/2000000000 : ℝ)^4311 ≤ (22948288180149/50000000000000 : ℝ)^3287 := by
    have hnat : (1104455583 : ℕ)^4311*50000000000000^3287 ≤ 22948288180149^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104455583 2000000000 22948288180149 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3965253/12500000 : ℝ)^4311 ≤ (5545742759787/25000000000000 : ℝ)^3287 := by
    have hnat : (3965253 : ℕ)^4311*25000000000000^3287 ≤ 5545742759787^3287*12500000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3965253 12500000 5545742759787 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186667403/10000000000 : ℝ), (1104455583/2000000000 : ℝ), (3965253/12500000 : ℝ)] ![(31920452583223/100000000000000 : ℝ), (22948288180149/50000000000000 : ℝ), (5545742759787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186667403/10000000000 : ℝ)|^4311 ≤ (31920452583223/100000000000000 : ℝ)^3287
        have hw : |(4186667403/10000000000 : ℝ)|=(4186667403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104455583/2000000000 : ℝ)|^4311 ≤ (22948288180149/50000000000000 : ℝ)^3287
        have hw : |(1104455583/2000000000 : ℝ)|=(1104455583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3965253/12500000 : ℝ)|^4311 ≤ (5545742759787/25000000000000 : ℝ)^3287
        have hw : |(3965253/12500000 : ℝ)|=(3965253/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (741/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13403/50000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (2155/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2155 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2155*1^512 ≤ 0^512*1^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2155/512 : ℝ) ≤ (2113862436189030177/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2155 ≤ (2113862436189030177/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2155*100000000000000000000^512 ≤ 2113862436189030177^512*5^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2113862436189030177 100000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2113862436189030177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2155 := by
      have hnat : (1 : ℕ)^512*1^2155 ≤ 1^2155*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102113862436189030177/100000000000000000000 : ℝ) ≤ (10049822875450293/10000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (102113862436189030177/100000000000000000000 : ℝ)^512 ≤ (10049822875450293/10000000000000000 : ℝ)^2155 := by
      have hnat : (102113862436189030177 : ℕ)^512*10000000000000000^2155 ≤ 10049822875450293^2155*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102113862436189030177 100000000000000000000 10049822875450293 10000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049822875450293/10000000000000000 : ℝ)) (X := (102113862436189030177/100000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52113862436189030177/50000000000000000000 : ℝ) ≤ (5049822875450293/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (52113862436189030177/50000000000000000000 : ℝ)^512 ≤ (5049822875450293/5000000000000000 : ℝ)^2155 := by
      have hnat : (52113862436189030177 : ℕ)^512*5000000000000000^2155 ≤ 5049822875450293^2155*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52113862436189030177 50000000000000000000 5049822875450293 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049822875450293/5000000000000000 : ℝ)) (X := (52113862436189030177/50000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49822875450293/4000000000000000 : ℝ)*(0 : ℝ))^(2155/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(49822875450293/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2113862436189030177/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49822875450293/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (1 : ℝ)+(49822875450293/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049822875450293/10000000000000000 : ℝ) by norm_num, show 1+(2113862436189030177/100000000000000000000 : ℝ)+(0 : ℝ)=(102113862436189030177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2113862436189030177/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49822875450293/4000000000000000 : ℝ)*(2/5 : ℝ))^(2155/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(49822875450293/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049822875450293/5000000000000000 : ℝ) by norm_num, show 1+2*(2113862436189030177/100000000000000000000 : ℝ)=(52113862436189030177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49822875450293/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49822875450293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49822875450293/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49822875450293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49822875450293/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49822875450293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-360767533/2000000000 : ℝ)*X 0 0+(2996519331/5000000000 : ℝ)*X 0 1+(1203262963/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2750402473/5000000000 : ℝ)*X 1 0+(-1237049627/5000000000 : ℝ)*X 1 1+(4813052301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1375201187/2500000000 : ℝ)*X 2 0+(962610389/2000000000 : ℝ)*X 2 1+(-1237049973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4177402559/10000000000 : ℝ)*X 0 0+(3106131233/10000000000 : ℝ)*X 0 1+(5586069997/10000000000 : ℝ)*X 0 2+(4177402559/10000000000 : ℝ)*X 1 0+(3106131233/10000000000 : ℝ)*X 1 1+(5586069997/10000000000 : ℝ)*X 1 2+(4177402559/10000000000 : ℝ)*X 2 0+(3106131233/10000000000 : ℝ)*X 2 1+(5586069997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-452061821/2500000000 : ℝ)*X 0 0+(121085137/250000000 : ℝ)*X 0 1+(2980800481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5179163643/10000000000 : ℝ)*X 1 0+(-132555181/1000000000 : ℝ)*X 1 1+(2980800297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5179163579/10000000000 : ℝ)*X 2 0+(745200127/1250000000 : ℝ)*X 2 1+(-662775617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186667403/10000000000 : ℝ)*X 0 0+(1104455583/2000000000 : ℝ)*X 0 1+(3965253/12500000 : ℝ)*X 0 2+(4186667403/10000000000 : ℝ)*X 1 0+(1104455583/2000000000 : ℝ)*X 1 1+(3965253/12500000 : ℝ)*X 1 2+(4186667403/10000000000 : ℝ)*X 2 0+(1104455583/2000000000 : ℝ)*X 2 1+(3965253/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47374353685939069966191/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91986911/100000000000000 : ℝ)*(base1) + (7565313/20000000000000 : ℝ)*(base16) + (404553437/100000000000000 : ℝ)*(base19) + (51484447/12500000000000 : ℝ)*(base23) + (60885369/100000000000000 : ℝ)*(upper3) + (312676614213329/50000000000000 : ℝ)*(major0) + (312676614213329/50000000000000 : ℝ)*(major1) + (312676614213329/50000000000000 : ℝ)*(major2) + (169493714856807/20000000000000 : ℝ)*(sp0) + (211867281029653/25000000000000 : ℝ)*(sp1) + (211867288655759/25000000000000 : ℝ)*(sp2) + (403236168765579/100000000000000 : ℝ)*(sp3) + (1084201489/100000000000000 : ℝ)*(sp4) + (566436399/100000000000000 : ℝ)*(sp7) + (403236827188889/100000000000000 : ℝ)*(f.failure) + (847469566498613/100000000000000 : ℝ)*(f.sum) + (257008593144603/100000000000000000000000000000 : ℝ)*base66 + (1676890738844603/200000000000000000000000000000 : ℝ)*base68 + (1552936382644603/200000000000000000000000000000 : ℝ)*base70 + (2381649844444603/200000000000000000000000000000 : ℝ)*base72 + (96710683155397/100000000000000000000000000000 : ℝ)*base73 + (2758638577444603/200000000000000000000000000000 : ℝ)*base76 + (1141393839644603/200000000000000000000000000000 : ℝ)*base78 + (714987564844603/200000000000000000000000000000 : ℝ)*base80 + (466798643144603/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (57582409/5000000000000000000000 : ℝ)*base89 + (57582409/5000000000000000000000 : ℝ)*base91 + (57582409/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (373230414571048538253729/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57369527/50000000000000 : ℝ)*(base19) + (161128851/50000000000000 : ℝ)*(base23) + (74553841/50000000000000 : ℝ)*(base39) + (29166893/100000000000000 : ℝ)*(upper2) + (75280649/100000000000000 : ℝ)*(upper5) + (659907672264513/100000000000000 : ℝ)*(major0) + (659907672264513/100000000000000 : ℝ)*(major1) + (20622110098651/3125000000000 : ℝ)*(major2) + (116896081/100000000000000 : ℝ)*(sp1) + (9658051/2500000000000 : ℝ)*(sp2) + (447148549859287/50000000000000 : ℝ)*(sp4) + (894296868083439/100000000000000 : ℝ)*(sp5) + (894296540246513/100000000000000 : ℝ)*(sp6) + (13297438546803/3125000000000 : ℝ)*(sp7) + (13297438546803/3125000000000 : ℝ)*(f.failure) + (178859449765251/20000000000000 : ℝ)*(f.sum) + (227904290019183/80000000000000000000000000000 : ℝ)*base66 + (89155340145257/12500000000000000000000000000 : ℝ)*base68 + (1070266444152309/400000000000000000000000000000 : ℝ)*base69 + (66871078032757/12500000000000000000000000000 : ℝ)*base72 + (140715106339183/80000000000000000000000000000 : ℝ)*base74 + (857775660552309/400000000000000000000000000000 : ℝ)*base75 + (2644077894647691/400000000000000000000000000000 : ℝ)*base78 + (550078340152309/400000000000000000000000000000 : ℝ)*base79 + (129259175752309/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (233343/156250000000000000000 : ℝ)*base89 + (233343/156250000000000000000 : ℝ)*base91 + (1329157/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1351_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (741/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13403/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1351_s1_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987358659/10000000000 : ℝ)*x 0 + (2819053101/5000000000 : ℝ)*x 1 + (2525223219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987358659/10000000000 : ℝ)^4311 ≤ (12013458763283/100000000000000 : ℝ)^3287 := by
    have hnat : (1987358659 : ℕ)^4311*100000000000000^3287 ≤ 12013458763283^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987358659 10000000000 12013458763283 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2819053101/5000000000 : ℝ)^4311 ≤ (11790812563769/25000000000000 : ℝ)^3287 := by
    have hnat : (2819053101 : ℕ)^4311*25000000000000^3287 ≤ 11790812563769^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819053101 5000000000 11790812563769 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2525223219/5000000000 : ℝ)^4311 ≤ (20411645482803/50000000000000 : ℝ)^3287 := by
    have hnat : (2525223219 : ℕ)^4311*50000000000000^3287 ≤ 20411645482803^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525223219 5000000000 20411645482803 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987358659/10000000000 : ℝ), (2819053101/5000000000 : ℝ), (2525223219/5000000000 : ℝ)] ![(12013458763283/100000000000000 : ℝ), (11790812563769/25000000000000 : ℝ), (20411645482803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987358659/10000000000 : ℝ)|^4311 ≤ (12013458763283/100000000000000 : ℝ)^3287
        have hw : |(-1987358659/10000000000 : ℝ)|=(1987358659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2819053101/5000000000 : ℝ)|^4311 ≤ (11790812563769/25000000000000 : ℝ)^3287
        have hw : |(2819053101/5000000000 : ℝ)|=(2819053101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2525223219/5000000000 : ℝ)|^4311 ≤ (20411645482803/50000000000000 : ℝ)^3287
        have hw : |(2525223219/5000000000 : ℝ)|=(2525223219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s1_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404777387/10000000000 : ℝ)*x 0 + (-230070659/1000000000 : ℝ)*x 1 + (2525223449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404777387/10000000000 : ℝ)^4311 ≤ (44620045613827/100000000000000 : ℝ)^3287 := by
    have hnat : (5404777387 : ℕ)^4311*100000000000000^3287 ≤ 44620045613827^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404777387 10000000000 44620045613827 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (230070659/1000000000 : ℝ)^4311 ≤ (7278329268679/50000000000000 : ℝ)^3287 := by
    have hnat : (230070659 : ℕ)^4311*50000000000000^3287 ≤ 7278329268679^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230070659 1000000000 7278329268679 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2525223449/5000000000 : ℝ)^4311 ≤ (318931998767/781250000000 : ℝ)^3287 := by
    have hnat : (2525223449 : ℕ)^4311*781250000000^3287 ≤ 318931998767^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525223449 5000000000 318931998767 781250000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404777387/10000000000 : ℝ), (-230070659/1000000000 : ℝ), (2525223449/5000000000 : ℝ)] ![(44620045613827/100000000000000 : ℝ), (7278329268679/50000000000000 : ℝ), (318931998767/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404777387/10000000000 : ℝ)|^4311 ≤ (44620045613827/100000000000000 : ℝ)^3287
        have hw : |(5404777387/10000000000 : ℝ)|=(5404777387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-230070659/1000000000 : ℝ)|^4311 ≤ (7278329268679/50000000000000 : ℝ)^3287
        have hw : |(-230070659/1000000000 : ℝ)|=(230070659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2525223449/5000000000 : ℝ)|^4311 ≤ (318931998767/781250000000 : ℝ)^3287
        have hw : |(2525223449/5000000000 : ℝ)|=(2525223449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s1_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404777359/10000000000 : ℝ)*x 0 + (5050446501/10000000000 : ℝ)*x 1 + (-575176783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404777359/10000000000 : ℝ)^4311 ≤ (697188207979/1562500000000 : ℝ)^3287 := by
    have hnat : (5404777359 : ℕ)^4311*1562500000000^3287 ≤ 697188207979^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404777359 10000000000 697188207979 1562500000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5050446501/10000000000 : ℝ)^4311 ≤ (10205822908371/25000000000000 : ℝ)^3287 := by
    have hnat : (5050446501 : ℕ)^4311*25000000000000^3287 ≤ 10205822908371^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050446501 10000000000 10205822908371 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575176783/2500000000 : ℝ)^4311 ≤ (14556663034929/100000000000000 : ℝ)^3287 := by
    have hnat : (575176783 : ℕ)^4311*100000000000000^3287 ≤ 14556663034929^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575176783 2500000000 14556663034929 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404777359/10000000000 : ℝ), (5050446501/10000000000 : ℝ), (-575176783/2500000000 : ℝ)] ![(697188207979/1562500000000 : ℝ), (10205822908371/25000000000000 : ℝ), (14556663034929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404777359/10000000000 : ℝ)|^4311 ≤ (697188207979/1562500000000 : ℝ)^3287
        have hw : |(5404777359/10000000000 : ℝ)|=(5404777359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5050446501/10000000000 : ℝ)|^4311 ≤ (10205822908371/25000000000000 : ℝ)^3287
        have hw : |(5050446501/10000000000 : ℝ)|=(5050446501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-575176783/2500000000 : ℝ)|^4311 ≤ (14556663034929/100000000000000 : ℝ)^3287
        have hw : |(-575176783/2500000000 : ℝ)|=(575176783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s1_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145352629/5000000000 : ℝ)*x 0 + (3714195989/10000000000 : ℝ)*x 1 + (989851737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145352629/5000000000 : ℝ)^4311 ≤ (32964784688721/100000000000000 : ℝ)^3287 := by
    have hnat : (2145352629 : ℕ)^4311*100000000000000^3287 ≤ 32964784688721^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145352629 5000000000 32964784688721 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3714195989/10000000000 : ℝ)^4311 ≤ (341015955691/1250000000000 : ℝ)^3287 := by
    have hnat : (3714195989 : ℕ)^4311*1250000000000^3287 ≤ 341015955691^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714195989 10000000000 341015955691 1250000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (989851737/2000000000 : ℝ)^4311 ≤ (39753938844097/100000000000000 : ℝ)^3287 := by
    have hnat : (989851737 : ℕ)^4311*100000000000000^3287 ≤ 39753938844097^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989851737 2000000000 39753938844097 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145352629/5000000000 : ℝ), (3714195989/10000000000 : ℝ), (989851737/2000000000 : ℝ)] ![(32964784688721/100000000000000 : ℝ), (341015955691/1250000000000 : ℝ), (39753938844097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145352629/5000000000 : ℝ)|^4311 ≤ (32964784688721/100000000000000 : ℝ)^3287
        have hw : |(2145352629/5000000000 : ℝ)|=(2145352629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3714195989/10000000000 : ℝ)|^4311 ≤ (341015955691/1250000000000 : ℝ)^3287
        have hw : |(3714195989/10000000000 : ℝ)|=(3714195989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(989851737/2000000000 : ℝ)|^4311 ≤ (39753938844097/100000000000000 : ℝ)^3287
        have hw : |(989851737/2000000000 : ℝ)|=(989851737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s1_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-993939473/5000000000 : ℝ)*x 0 + (2528884597/5000000000 : ℝ)*x 1 + (5630651163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993939473/5000000000 : ℝ)^4311 ≤ (300439595711/2500000000000 : ℝ)^3287 := by
    have hnat : (993939473 : ℕ)^4311*2500000000000^3287 ≤ 300439595711^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993939473 5000000000 300439595711 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2528884597/5000000000 : ℝ)^4311 ≤ (40900938767421/100000000000000 : ℝ)^3287 := by
    have hnat : (2528884597 : ℕ)^4311*100000000000000^3287 ≤ 40900938767421^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528884597 5000000000 40900938767421 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5630651163/10000000000 : ℝ)^4311 ≤ (47081477387309/100000000000000 : ℝ)^3287 := by
    have hnat : (5630651163 : ℕ)^4311*100000000000000^3287 ≤ 47081477387309^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630651163 10000000000 47081477387309 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993939473/5000000000 : ℝ), (2528884597/5000000000 : ℝ), (5630651163/10000000000 : ℝ)] ![(300439595711/2500000000000 : ℝ), (40900938767421/100000000000000 : ℝ), (47081477387309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993939473/5000000000 : ℝ)|^4311 ≤ (300439595711/2500000000000 : ℝ)^3287
        have hw : |(-993939473/5000000000 : ℝ)|=(993939473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2528884597/5000000000 : ℝ)|^4311 ≤ (40900938767421/100000000000000 : ℝ)^3287
        have hw : |(2528884597/5000000000 : ℝ)|=(2528884597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5630651163/10000000000 : ℝ)|^4311 ≤ (47081477387309/100000000000000 : ℝ)^3287
        have hw : |(5630651163/10000000000 : ℝ)|=(5630651163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s1_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252173801/10000000000 : ℝ)*x 0 + (-1720502099/10000000000 : ℝ)*x 1 + (5630651213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252173801/10000000000 : ℝ)^4311 ≤ (42975036050667/100000000000000 : ℝ)^3287 := by
    have hnat : (5252173801 : ℕ)^4311*100000000000000^3287 ≤ 42975036050667^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252173801 10000000000 42975036050667 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1720502099/10000000000 : ℝ)^4311 ≤ (1988697199099/20000000000000 : ℝ)^3287 := by
    have hnat : (1720502099 : ℕ)^4311*20000000000000^3287 ≤ 1988697199099^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720502099 10000000000 1988697199099 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5630651213/10000000000 : ℝ)^4311 ≤ (11770369483909/25000000000000 : ℝ)^3287 := by
    have hnat : (5630651213 : ℕ)^4311*25000000000000^3287 ≤ 11770369483909^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630651213 10000000000 11770369483909 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252173801/10000000000 : ℝ), (-1720502099/10000000000 : ℝ), (5630651213/10000000000 : ℝ)] ![(42975036050667/100000000000000 : ℝ), (1988697199099/20000000000000 : ℝ), (11770369483909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252173801/10000000000 : ℝ)|^4311 ≤ (42975036050667/100000000000000 : ℝ)^3287
        have hw : |(5252173801/10000000000 : ℝ)|=(5252173801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1720502099/10000000000 : ℝ)|^4311 ≤ (1988697199099/20000000000000 : ℝ)^3287
        have hw : |(-1720502099/10000000000 : ℝ)|=(1720502099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5630651213/10000000000 : ℝ)|^4311 ≤ (11770369483909/25000000000000 : ℝ)^3287
        have hw : |(5630651213/10000000000 : ℝ)|=(5630651213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s1_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626086849/5000000000 : ℝ)*x 0 + (5630651287/10000000000 : ℝ)*x 1 + (-1720502139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626086849/5000000000 : ℝ)^4311 ≤ (8595006989067/20000000000000 : ℝ)^3287 := by
    have hnat : (2626086849 : ℕ)^4311*20000000000000^3287 ≤ 8595006989067^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626086849 5000000000 8595006989067 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5630651287/10000000000 : ℝ)^4311 ≤ (1177036968679/2500000000000 : ℝ)^3287 := by
    have hnat : (5630651287 : ℕ)^4311*2500000000000^3287 ≤ 1177036968679^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630651287 10000000000 1177036968679 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720502139/10000000000 : ℝ)^4311 ≤ (994348629869/10000000000000 : ℝ)^3287 := by
    have hnat : (1720502139 : ℕ)^4311*10000000000000^3287 ≤ 994348629869^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720502139 10000000000 994348629869 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626086849/5000000000 : ℝ), (5630651287/10000000000 : ℝ), (-1720502139/10000000000 : ℝ)] ![(8595006989067/20000000000000 : ℝ), (1177036968679/2500000000000 : ℝ), (994348629869/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626086849/5000000000 : ℝ)|^4311 ≤ (8595006989067/20000000000000 : ℝ)^3287
        have hw : |(2626086849/5000000000 : ℝ)|=(2626086849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5630651287/10000000000 : ℝ)|^4311 ≤ (1177036968679/2500000000000 : ℝ)^3287
        have hw : |(5630651287/10000000000 : ℝ)|=(5630651287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720502139/10000000000 : ℝ)|^4311 ≤ (994348629869/10000000000000 : ℝ)^3287
        have hw : |(-1720502139/10000000000 : ℝ)|=(1720502139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s1_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291799141/10000000000 : ℝ)*x 0 + (2466934781/5000000000 : ℝ)*x 1 + (3729862161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291799141/10000000000 : ℝ)^4311 ≤ (32975807388979/100000000000000 : ℝ)^3287 := by
    have hnat : (4291799141 : ℕ)^4311*100000000000000^3287 ≤ 32975807388979^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291799141 10000000000 32975807388979 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2466934781/5000000000 : ℝ)^4311 ≤ (39591899059721/100000000000000 : ℝ)^3287 := by
    have hnat : (2466934781 : ℕ)^4311*100000000000000^3287 ≤ 39591899059721^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466934781 5000000000 39591899059721 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3729862161/10000000000 : ℝ)^4311 ≤ (6858073381607/25000000000000 : ℝ)^3287 := by
    have hnat : (3729862161 : ℕ)^4311*25000000000000^3287 ≤ 6858073381607^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729862161 10000000000 6858073381607 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291799141/10000000000 : ℝ), (2466934781/5000000000 : ℝ), (3729862161/10000000000 : ℝ)] ![(32975807388979/100000000000000 : ℝ), (39591899059721/100000000000000 : ℝ), (6858073381607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291799141/10000000000 : ℝ)|^4311 ≤ (32975807388979/100000000000000 : ℝ)^3287
        have hw : |(4291799141/10000000000 : ℝ)|=(4291799141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2466934781/5000000000 : ℝ)|^4311 ≤ (39591899059721/100000000000000 : ℝ)^3287
        have hw : |(2466934781/5000000000 : ℝ)|=(2466934781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3729862161/10000000000 : ℝ)|^4311 ≤ (6858073381607/25000000000000 : ℝ)^3287
        have hw : |(3729862161/10000000000 : ℝ)|=(3729862161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13403/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6973/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9697/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13403/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13403/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13403/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13403/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13403/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13403/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (741/50000 : ℝ) ^ (2155/512 : ℝ) ≤ (50011361551/2500000000000000000 : ℝ) := by
    have hpowers : (741/50000 : ℝ)^2155 ≤ (50011361551/2500000000000000000 : ℝ)^512 := by
      have hnat : (741 : ℕ)^2155*2500000000000000000^512 ≤ 50011361551^512*50000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        741 50000 50011361551 2500000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (741/50000 : ℝ)) (X := (50011361551/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13403/50000 : ℝ) ^ (2155/512 : ℝ) ≤ (1960683445468009/500000000000000000 : ℝ) := by
    have hpowers : (13403/50000 : ℝ)^2155 ≤ (1960683445468009/500000000000000000 : ℝ)^512 := by
      have hnat : (13403 : ℕ)^2155*500000000000000000^512 ≤ 1960683445468009^512*50000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13403 50000 1960683445468009 500000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13403/50000 : ℝ)) (X := (1960683445468009/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250000050011361551/1250000000000000000 : ℝ) ≤ (10000000095056397/10000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (1250000050011361551/1250000000000000000 : ℝ)^512 ≤ (10000000095056397/10000000000000000 : ℝ)^2155 := by
      have hnat : (1250000050011361551 : ℕ)^512*10000000000000000^2155 ≤ 10000000095056397^2155*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250000050011361551 1250000000000000000 10000000095056397 10000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000095056397/10000000000000000 : ℝ)) (X := (1250000050011361551/1250000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (627450866809675399/625000000000000000 : ℝ) ≤ (500465140530003/500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (627450866809675399/625000000000000000 : ℝ)^512 ≤ (500465140530003/500000000000000 : ℝ)^2155 := by
      have hnat : (627450866809675399 : ℕ)^512*500000000000000^2155 ≤ 500465140530003^2155*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        627450866809675399 625000000000000000 500465140530003 500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500465140530003/500000000000000 : ℝ)) (X := (627450866809675399/625000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (251960683445468009/250000000000000000 : ℝ) ≤ (10018605526143723/10000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (251960683445468009/250000000000000000 : ℝ)^512 ≤ (10018605526143723/10000000000000000 : ℝ)^2155 := by
      have hnat : (251960683445468009 : ℕ)^512*10000000000000000^2155 ≤ 10018605526143723^2155*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251960683445468009 250000000000000000 10018605526143723 10000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018605526143723/10000000000000000 : ℝ)) (X := (251960683445468009/250000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(50011361551/2500000000000000000 : ℝ) ≤ ((1217367447876619137/1217500000000000000 : ℝ)+2*(9302715543663/2532400000000000 : ℝ)*(741/50000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (1217367447876619137/1217500000000000000 : ℝ)+2*(9302715543663/2532400000000000 : ℝ)*(741/50000 : ℝ)=(10000000095056397/10000000000000000 : ℝ) by norm_num, show 1+2*(50011361551/2500000000000000000 : ℝ)=(1250000050011361551/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1960683445468009/500000000000000000 : ℝ)+(50011361551/2500000000000000000 : ℝ) ≤ ((1217367447876619137/1217500000000000000 : ℝ)+(9302715543663/2532400000000000 : ℝ)*((13403/50000 : ℝ)+(741/50000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (1217367447876619137/1217500000000000000 : ℝ)+(9302715543663/2532400000000000 : ℝ)*((13403/50000 : ℝ)+(741/50000 : ℝ))=(500465140530003/500000000000000 : ℝ) by norm_num, show 1+(1960683445468009/500000000000000000 : ℝ)+(50011361551/2500000000000000000 : ℝ)=(627450866809675399/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1960683445468009/500000000000000000 : ℝ) ≤ ((1217367447876619137/1217500000000000000 : ℝ)+2*(9302715543663/2532400000000000 : ℝ)*(13403/50000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (1217367447876619137/1217500000000000000 : ℝ)+2*(9302715543663/2532400000000000 : ℝ)*(13403/50000 : ℝ)=(10018605526143723/10000000000000000 : ℝ) by norm_num, show 1+2*(1960683445468009/500000000000000000 : ℝ)=(251960683445468009/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1217367447876619137/1217500000000000000 : ℝ)*(X 1 0+X 2 0)+(9302715543663/2532400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (741/50000 : ℝ)) (hi := (13403/50000 : ℝ)) (c := (1217367447876619137/1217500000000000000 : ℝ)) (alpha := (9302715543663/2532400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1217367447876619137/1217500000000000000 : ℝ)*(X 0 1+X 2 1)+(9302715543663/2532400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (741/50000 : ℝ)) (hi := (13403/50000 : ℝ)) (c := (1217367447876619137/1217500000000000000 : ℝ)) (alpha := (9302715543663/2532400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1217367447876619137/1217500000000000000 : ℝ)*(X 0 2+X 1 2)+(9302715543663/2532400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (741/50000 : ℝ)) (hi := (13403/50000 : ℝ)) (c := (1217367447876619137/1217500000000000000 : ℝ)) (alpha := (9302715543663/2532400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1987358659/10000000000 : ℝ)*X 0 0+(2819053101/5000000000 : ℝ)*X 0 1+(2525223219/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5404777387/10000000000 : ℝ)*X 1 0+(-230070659/1000000000 : ℝ)*X 1 1+(2525223449/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5404777359/10000000000 : ℝ)*X 2 0+(5050446501/10000000000 : ℝ)*X 2 1+(-575176783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2145352629/5000000000 : ℝ)*X 0 0+(3714195989/10000000000 : ℝ)*X 0 1+(989851737/2000000000 : ℝ)*X 0 2+(2145352629/5000000000 : ℝ)*X 1 0+(3714195989/10000000000 : ℝ)*X 1 1+(989851737/2000000000 : ℝ)*X 1 2+(2145352629/5000000000 : ℝ)*X 2 0+(3714195989/10000000000 : ℝ)*X 2 1+(989851737/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-993939473/5000000000 : ℝ)*X 0 0+(2528884597/5000000000 : ℝ)*X 0 1+(5630651163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252173801/10000000000 : ℝ)*X 1 0+(-1720502099/10000000000 : ℝ)*X 1 1+(5630651213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626086849/5000000000 : ℝ)*X 2 0+(5630651287/10000000000 : ℝ)*X 2 1+(-1720502139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4291799141/10000000000 : ℝ)*X 0 0+(2466934781/5000000000 : ℝ)*X 0 1+(3729862161/10000000000 : ℝ)*X 0 2+(4291799141/10000000000 : ℝ)*X 1 0+(2466934781/5000000000 : ℝ)*X 1 1+(3729862161/10000000000 : ℝ)*X 1 2+(4291799141/10000000000 : ℝ)*X 2 0+(2466934781/5000000000 : ℝ)*X 2 1+(3729862161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3395053604716424522073922059/395687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40084091/100000000000000 : ℝ)*(base1) + (1392572903/100000000000000 : ℝ)*(base19) + (1383757163/100000000000000 : ℝ)*(base23) + (261621049/100000000000000 : ℝ)*(upper3) + (3458107/10000000000000 : ℝ)*(upper5) + (627841842767787/50000000000000 : ℝ)*(major0) + (627841842767787/50000000000000 : ℝ)*(major1) + (627841842767787/50000000000000 : ℝ)*(major2) + (21270946385487/1250000000000 : ℝ)*(sp0) + (850841324454299/50000000000000 : ℝ)*(sp1) + (1701682657724339/100000000000000 : ℝ)*(sp2) + (404839328583197/50000000000000 : ℝ)*(sp3) + (1046340829/12500000000000 : ℝ)*(sp4) + (869266907/20000000000000 : ℝ)*(sp7) + (40484152179251/5000000000000 : ℝ)*(f.failure) + (850842020740751/50000000000000 : ℝ)*(f.sum) + (11642043390531/63310000000000000000000000000 : ℝ)*base65 + (824176376983048897/791375000000000000000000000000000 : ℝ)*base67 + (3938207201174673897/791375000000000000000000000000000 : ℝ)*base69 + (1103147421505673897/791375000000000000000000000000000 : ℝ)*base71 + (53643990355821/63310000000000000000000000000 : ℝ)*base73 + (1797433754031173897/791375000000000000000000000000000 : ℝ)*base75 + (1421471205747451103/791375000000000000000000000000000 : ℝ)*base78 + (6140622653259576103/791375000000000000000000000000000 : ℝ)*base80 + (368211136286911/63310000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (860931/250000000000000000000 : ℝ)*base89 + (860931/250000000000000000000 : ℝ)*base91 + (860931/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62438741251106812110220509/9892187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (13880561/20000000000000 : ℝ)*(base1) + (1291834841/100000000000000 : ℝ)*(base19) + (78440797/6250000000000 : ℝ)*(base23) + (1172113/800000000000 : ℝ)*(upper3) + (34483309/25000000000000 : ℝ)*(upper5) + (4025187454001/312500000000 : ℝ)*(major0) + (4025187454001/312500000000 : ℝ)*(major1) + (4025187454001/312500000000 : ℝ)*(major2) + (334005683/5000000000000 : ℝ)*(sp1) + (6592344669/100000000000000 : ℝ)*(sp2) + (87278003927953/5000000000000 : ℝ)*(sp4) + (872776018603877/50000000000000 : ℝ)*(sp5) + (872776080879417/50000000000000 : ℝ)*(sp6) + (830559681604089/100000000000000 : ℝ)*(sp7) + (415279875503447/50000000000000 : ℝ)*(f.failure) + (349112001831251/20000000000000 : ℝ)*(f.sum) + (1716031880551/6331000000000000000000000000 : ℝ)*base66 + (97102329122223687/9892187500000000000000000000000 : ℝ)*base67 + (128498247115444249/19784375000000000000000000000000 : ℝ)*base69 + (165942475470337999/19784375000000000000000000000000 : ℝ)*base71 + (2097049660969/1582750000000000000000000000 : ℝ)*base73 + (305086742824312999/19784375000000000000000000000000 : ℝ)*base75 + (162630427380427/38641357421875000000000000000 : ℝ)*base77 + (111007901339456749/19784375000000000000000000000000 : ℝ)*base79 + (24467204051837/6331000000000000000000000000 : ℝ)*base82 + (1674407/2500000000000000000000 : ℝ)*base89 + (1674407/2500000000000000000000 : ℝ)*base91 + (1674407/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1351_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13403/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6973/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9697/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1351_s2_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-506683339/2500000000 : ℝ)*x 0 + (5477306989/10000000000 : ℝ)*x 1 + (1296502727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506683339/2500000000 : ℝ)^4311 ≤ (12326585062587/100000000000000 : ℝ)^3287 := by
    have hnat : (506683339 : ℕ)^4311*100000000000000^3287 ≤ 12326585062587^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506683339 2500000000 12326585062587 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477306989/10000000000 : ℝ)^4311 ≤ (45407000605377/100000000000000 : ℝ)^3287 := by
    have hnat : (5477306989 : ℕ)^4311*100000000000000^3287 ≤ 45407000605377^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477306989 10000000000 45407000605377 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296502727/2500000000 : ℝ)^4311 ≤ (21133207157019/50000000000000 : ℝ)^3287 := by
    have hnat : (1296502727 : ℕ)^4311*50000000000000^3287 ≤ 21133207157019^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296502727 2500000000 21133207157019 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506683339/2500000000 : ℝ), (5477306989/10000000000 : ℝ), (1296502727/2500000000 : ℝ)] ![(12326585062587/100000000000000 : ℝ), (45407000605377/100000000000000 : ℝ), (21133207157019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506683339/2500000000 : ℝ)|^4311 ≤ (12326585062587/100000000000000 : ℝ)^3287
        have hw : |(-506683339/2500000000 : ℝ)|=(506683339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477306989/10000000000 : ℝ)|^4311 ≤ (45407000605377/100000000000000 : ℝ)^3287
        have hw : |(5477306989/10000000000 : ℝ)|=(5477306989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296502727/2500000000 : ℝ)|^4311 ≤ (21133207157019/50000000000000 : ℝ)^3287
        have hw : |(1296502727/2500000000 : ℝ)|=(1296502727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s2_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341330459/2500000000 : ℝ)*x 0 + (-544293581/2500000000 : ℝ)*x 1 + (1037202259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341330459/2500000000 : ℝ)^4311 ≤ (44193324943751/100000000000000 : ℝ)^3287 := by
    have hnat : (1341330459 : ℕ)^4311*100000000000000^3287 ≤ 44193324943751^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341330459 2500000000 44193324943751 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544293581/2500000000 : ℝ)^4311 ≤ (13540256592869/100000000000000 : ℝ)^3287 := by
    have hnat : (544293581 : ℕ)^4311*100000000000000^3287 ≤ 13540256592869^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544293581 2500000000 13540256592869 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037202259/2000000000 : ℝ)^4311 ≤ (5283302306339/12500000000000 : ℝ)^3287 := by
    have hnat : (1037202259 : ℕ)^4311*12500000000000^3287 ≤ 5283302306339^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037202259 2000000000 5283302306339 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341330459/2500000000 : ℝ), (-544293581/2500000000 : ℝ), (1037202259/2000000000 : ℝ)] ![(44193324943751/100000000000000 : ℝ), (13540256592869/100000000000000 : ℝ), (5283302306339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341330459/2500000000 : ℝ)|^4311 ≤ (44193324943751/100000000000000 : ℝ)^3287
        have hw : |(1341330459/2500000000 : ℝ)|=(1341330459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544293581/2500000000 : ℝ)|^4311 ≤ (13540256592869/100000000000000 : ℝ)^3287
        have hw : |(-544293581/2500000000 : ℝ)|=(544293581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037202259/2000000000 : ℝ)|^4311 ≤ (5283302306339/12500000000000 : ℝ)^3287
        have hw : |(1037202259/2000000000 : ℝ)|=(1037202259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s2_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365321909/10000000000 : ℝ)*x 0 + (518601121/1000000000 : ℝ)*x 1 + (-1088587169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365321909/10000000000 : ℝ)^4311 ≤ (1104833143309/2500000000000 : ℝ)^3287 := by
    have hnat : (5365321909 : ℕ)^4311*2500000000000^3287 ≤ 1104833143309^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365321909 10000000000 1104833143309 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518601121/1000000000 : ℝ)^4311 ≤ (2113320877107/5000000000000 : ℝ)^3287 := by
    have hnat : (518601121 : ℕ)^4311*5000000000000^3287 ≤ 2113320877107^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518601121 1000000000 2113320877107 5000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088587169/5000000000 : ℝ)^4311 ≤ (6770128353531/50000000000000 : ℝ)^3287 := by
    have hnat : (1088587169 : ℕ)^4311*50000000000000^3287 ≤ 6770128353531^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088587169 5000000000 6770128353531 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365321909/10000000000 : ℝ), (518601121/1000000000 : ℝ), (-1088587169/5000000000 : ℝ)] ![(1104833143309/2500000000000 : ℝ), (2113320877107/5000000000000 : ℝ), (6770128353531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365321909/10000000000 : ℝ)|^4311 ≤ (1104833143309/2500000000000 : ℝ)^3287
        have hw : |(5365321909/10000000000 : ℝ)|=(5365321909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518601121/1000000000 : ℝ)|^4311 ≤ (2113320877107/5000000000000 : ℝ)^3287
        have hw : |(518601121/1000000000 : ℝ)|=(518601121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088587169/5000000000 : ℝ)|^4311 ≤ (6770128353531/50000000000000 : ℝ)^3287
        have hw : |(-1088587169/5000000000 : ℝ)|=(1088587169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s2_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539783327/1250000000 : ℝ)*x 0 + (4022237203/10000000000 : ℝ)*x 1 + (4634443849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539783327/1250000000 : ℝ)^4311 ≤ (3324277788907/10000000000000 : ℝ)^3287 := by
    have hnat : (539783327 : ℕ)^4311*10000000000000^3287 ≤ 3324277788907^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539783327 1250000000 3324277788907 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022237203/10000000000 : ℝ)^4311 ≤ (3028638141937/10000000000000 : ℝ)^3287 := by
    have hnat : (4022237203 : ℕ)^4311*10000000000000^3287 ≤ 3028638141937^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022237203 10000000000 3028638141937 10000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4634443849/10000000000 : ℝ)^4311 ≤ (36470840673753/100000000000000 : ℝ)^3287 := by
    have hnat : (4634443849 : ℕ)^4311*100000000000000^3287 ≤ 36470840673753^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634443849 10000000000 36470840673753 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539783327/1250000000 : ℝ), (4022237203/10000000000 : ℝ), (4634443849/10000000000 : ℝ)] ![(3324277788907/10000000000000 : ℝ), (3028638141937/10000000000000 : ℝ), (36470840673753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539783327/1250000000 : ℝ)|^4311 ≤ (3324277788907/10000000000000 : ℝ)^3287
        have hw : |(539783327/1250000000 : ℝ)|=(539783327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022237203/10000000000 : ℝ)|^4311 ≤ (3028638141937/10000000000000 : ℝ)^3287
        have hw : |(4022237203/10000000000 : ℝ)|=(4022237203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4634443849/10000000000 : ℝ)|^4311 ≤ (36470840673753/100000000000000 : ℝ)^3287
        have hw : |(4634443849/10000000000 : ℝ)|=(4634443849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s2_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-405359347/2000000000 : ℝ)*x 0 + (2593910087/5000000000 : ℝ)*x 1 + (219019263/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405359347/2000000000 : ℝ)^4311 ≤ (12327090621741/100000000000000 : ℝ)^3287 := by
    have hnat : (405359347 : ℕ)^4311*100000000000000^3287 ≤ 12327090621741^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405359347 2000000000 12327090621741 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593910087/5000000000 : ℝ)^4311 ≤ (66071491801/156250000000 : ℝ)^3287 := by
    have hnat : (2593910087 : ℕ)^4311*156250000000^3287 ≤ 66071491801^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593910087 5000000000 66071491801 156250000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219019263/400000000 : ℝ)^4311 ≤ (45387154610219/100000000000000 : ℝ)^3287 := by
    have hnat : (219019263 : ℕ)^4311*100000000000000^3287 ≤ 45387154610219^3287*400000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219019263 400000000 45387154610219 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405359347/2000000000 : ℝ), (2593910087/5000000000 : ℝ), (219019263/400000000 : ℝ)] ![(12327090621741/100000000000000 : ℝ), (66071491801/156250000000 : ℝ), (45387154610219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405359347/2000000000 : ℝ)|^4311 ≤ (12327090621741/100000000000000 : ℝ)^3287
        have hw : |(-405359347/2000000000 : ℝ)|=(405359347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593910087/5000000000 : ℝ)|^4311 ≤ (66071491801/156250000000 : ℝ)^3287
        have hw : |(2593910087/5000000000 : ℝ)|=(2593910087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219019263/400000000 : ℝ)|^4311 ≤ (45387154610219/100000000000000 : ℝ)^3287
        have hw : |(219019263/400000000 : ℝ)|=(219019263/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s2_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211606699/400000000 : ℝ)*x 0 + (-1887703747/10000000000 : ℝ)*x 1 + (5475481551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211606699/400000000 : ℝ)^4311 ≤ (2711451198407/6250000000000 : ℝ)^3287 := by
    have hnat : (211606699 : ℕ)^4311*6250000000000^3287 ≤ 2711451198407^3287*400000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211606699 400000000 2711451198407 6250000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1887703747/10000000000 : ℝ)^4311 ≤ (112296264631/1000000000000 : ℝ)^3287 := by
    have hnat : (1887703747 : ℕ)^4311*1000000000000^3287 ≤ 112296264631^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887703747 10000000000 112296264631 1000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475481551/10000000000 : ℝ)^4311 ≤ (45387154349303/100000000000000 : ℝ)^3287 := by
    have hnat : (5475481551 : ℕ)^4311*100000000000000^3287 ≤ 45387154349303^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475481551 10000000000 45387154349303 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211606699/400000000 : ℝ), (-1887703747/10000000000 : ℝ), (5475481551/10000000000 : ℝ)] ![(2711451198407/6250000000000 : ℝ), (112296264631/1000000000000 : ℝ), (45387154349303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211606699/400000000 : ℝ)|^4311 ≤ (2711451198407/6250000000000 : ℝ)^3287
        have hw : |(211606699/400000000 : ℝ)|=(211606699/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1887703747/10000000000 : ℝ)|^4311 ≤ (112296264631/1000000000000 : ℝ)^3287
        have hw : |(-1887703747/10000000000 : ℝ)|=(1887703747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475481551/10000000000 : ℝ)|^4311 ≤ (45387154349303/100000000000000 : ℝ)^3287
        have hw : |(5475481551/10000000000 : ℝ)|=(5475481551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s2_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058033493/2000000000 : ℝ)*x 0 + (5475481581/10000000000 : ℝ)*x 1 + (-1887703719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058033493/2000000000 : ℝ)^4311 ≤ (10845804766739/25000000000000 : ℝ)^3287 := by
    have hnat : (1058033493 : ℕ)^4311*25000000000000^3287 ≤ 10845804766739^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058033493 2000000000 10845804766739 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475481581/10000000000 : ℝ)^4311 ≤ (5673394334431/12500000000000 : ℝ)^3287 := by
    have hnat : (5475481581 : ℕ)^4311*12500000000000^3287 ≤ 5673394334431^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475481581 10000000000 5673394334431 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887703719/10000000000 : ℝ)^4311 ≤ (5614813122321/50000000000000 : ℝ)^3287 := by
    have hnat : (1887703719 : ℕ)^4311*50000000000000^3287 ≤ 5614813122321^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887703719 10000000000 5614813122321 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058033493/2000000000 : ℝ), (5475481581/10000000000 : ℝ), (-1887703719/10000000000 : ℝ)] ![(10845804766739/25000000000000 : ℝ), (5673394334431/12500000000000 : ℝ), (5614813122321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058033493/2000000000 : ℝ)|^4311 ≤ (10845804766739/25000000000000 : ℝ)^3287
        have hw : |(1058033493/2000000000 : ℝ)|=(1058033493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475481581/10000000000 : ℝ)|^4311 ≤ (5673394334431/12500000000000 : ℝ)^3287
        have hw : |(5475481581/10000000000 : ℝ)|=(5475481581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887703719/10000000000 : ℝ)|^4311 ≤ (5614813122321/50000000000000 : ℝ)^3287
        have hw : |(-1887703719/10000000000 : ℝ)|=(1887703719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s2_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318400151/10000000000 : ℝ)*x 0 + (2315320997/5000000000 : ℝ)*x 1 + (4026073019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318400151/10000000000 : ℝ)^4311 ≤ (4155515764647/12500000000000 : ℝ)^3287 := by
    have hnat : (4318400151 : ℕ)^4311*12500000000000^3287 ≤ 4155515764647^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318400151 10000000000 4155515764647 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2315320997/5000000000 : ℝ)^4311 ≤ (2276975394971/6250000000000 : ℝ)^3287 := by
    have hnat : (2315320997 : ℕ)^4311*6250000000000^3287 ≤ 2276975394971^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315320997 5000000000 2276975394971 6250000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4026073019/10000000000 : ℝ)^4311 ≤ (30324267553079/100000000000000 : ℝ)^3287 := by
    have hnat : (4026073019 : ℕ)^4311*100000000000000^3287 ≤ 30324267553079^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026073019 10000000000 30324267553079 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318400151/10000000000 : ℝ), (2315320997/5000000000 : ℝ), (4026073019/10000000000 : ℝ)] ![(4155515764647/12500000000000 : ℝ), (2276975394971/6250000000000 : ℝ), (30324267553079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318400151/10000000000 : ℝ)|^4311 ≤ (4155515764647/12500000000000 : ℝ)^3287
        have hw : |(4318400151/10000000000 : ℝ)|=(4318400151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2315320997/5000000000 : ℝ)|^4311 ≤ (2276975394971/6250000000000 : ℝ)^3287
        have hw : |(2315320997/5000000000 : ℝ)|=(2315320997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4026073019/10000000000 : ℝ)|^4311 ≤ (30324267553079/100000000000000 : ℝ)^3287
        have hw : |(4026073019/10000000000 : ℝ)|=(4026073019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9697/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (991/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9697/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6973/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9697/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6973/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9697/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6973/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9697/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6973/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9697/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6973/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9697/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6973/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6973/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (13551003030813/1000000000000000000 : ℝ) := by
    have hpowers : (6973/100000 : ℝ)^2155 ≤ (13551003030813/1000000000000000000 : ℝ)^512 := by
      have hnat : (6973 : ℕ)^2155*1000000000000000000^512 ≤ 13551003030813^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6973 100000 13551003030813 1000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6973/100000 : ℝ)) (X := (13551003030813/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9697/50000 : ℝ) ^ (2155/512 : ℝ) ≤ (50208030347046597/50000000000000000000 : ℝ) := by
    have hpowers : (9697/50000 : ℝ)^2155 ≤ (50208030347046597/50000000000000000000 : ℝ)^512 := by
      have hnat : (9697 : ℕ)^2155*50000000000000000000^512 ≤ 50208030347046597^512*50000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9697 50000 50208030347046597 50000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9697/50000 : ℝ)) (X := (50208030347046597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (500013551003030813/500000000000000000 : ℝ) ≤ (2500016097544947/2500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (500013551003030813/500000000000000000 : ℝ)^512 ≤ (2500016097544947/2500000000000000 : ℝ)^2155 := by
      have hnat : (500013551003030813 : ℕ)^512*2500000000000000^2155 ≤ 2500016097544947^2155*500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500013551003030813 500000000000000000 2500016097544947 2500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016097544947/2500000000000000 : ℝ)) (X := (500013551003030813/500000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50050885580498587247/50000000000000000000 : ℝ) ≤ (10002417013050143/10000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (50050885580498587247/50000000000000000000 : ℝ)^512 ≤ (10002417013050143/10000000000000000 : ℝ)^2155 := by
      have hnat : (50050885580498587247 : ℕ)^512*10000000000000000^2155 ≤ 10002417013050143^2155*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50050885580498587247 50000000000000000000 10002417013050143 10000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002417013050143/10000000000000000 : ℝ)) (X := (50050885580498587247/50000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25050208030347046597/25000000000000000000 : ℝ) ≤ (5002384817960249/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (25050208030347046597/25000000000000000000 : ℝ)^512 ≤ (5002384817960249/5000000000000000 : ℝ)^2155 := by
      have hnat : (25050208030347046597 : ℕ)^512*5000000000000000^2155 ≤ 5002384817960249^2155*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25050208030347046597 25000000000000000000 5002384817960249 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002384817960249/5000000000000000 : ℝ)) (X := (25050208030347046597/25000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13551003030813/1000000000000000000 : ℝ) ≤ ((62088995055936587959/62105000000000000000 : ℝ)+2*(470524574071/248420000000000 : ℝ)*(6973/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (62088995055936587959/62105000000000000000 : ℝ)+2*(470524574071/248420000000000 : ℝ)*(6973/100000 : ℝ)=(2500016097544947/2500000000000000 : ℝ) by norm_num, show 1+2*(13551003030813/1000000000000000000 : ℝ)=(500013551003030813/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50208030347046597/50000000000000000000 : ℝ)+(13551003030813/1000000000000000000 : ℝ) ≤ ((62088995055936587959/62105000000000000000 : ℝ)+(470524574071/248420000000000 : ℝ)*((9697/50000 : ℝ)+(6973/100000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (62088995055936587959/62105000000000000000 : ℝ)+(470524574071/248420000000000 : ℝ)*((9697/50000 : ℝ)+(6973/100000 : ℝ))=(10002417013050143/10000000000000000 : ℝ) by norm_num, show 1+(50208030347046597/50000000000000000000 : ℝ)+(13551003030813/1000000000000000000 : ℝ)=(50050885580498587247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50208030347046597/50000000000000000000 : ℝ) ≤ ((62088995055936587959/62105000000000000000 : ℝ)+2*(470524574071/248420000000000 : ℝ)*(9697/50000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (62088995055936587959/62105000000000000000 : ℝ)+2*(470524574071/248420000000000 : ℝ)*(9697/50000 : ℝ)=(5002384817960249/5000000000000000 : ℝ) by norm_num, show 1+2*(50208030347046597/50000000000000000000 : ℝ)=(25050208030347046597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (62088995055936587959/62105000000000000000 : ℝ)*(X 1 0+X 2 0)+(470524574071/248420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (6973/100000 : ℝ)) (hi := (9697/50000 : ℝ)) (c := (62088995055936587959/62105000000000000000 : ℝ)) (alpha := (470524574071/248420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (62088995055936587959/62105000000000000000 : ℝ)*(X 0 1+X 2 1)+(470524574071/248420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (6973/100000 : ℝ)) (hi := (9697/50000 : ℝ)) (c := (62088995055936587959/62105000000000000000 : ℝ)) (alpha := (470524574071/248420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (62088995055936587959/62105000000000000000 : ℝ)*(X 0 2+X 1 2)+(470524574071/248420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (6973/100000 : ℝ)) (hi := (9697/50000 : ℝ)) (c := (62088995055936587959/62105000000000000000 : ℝ)) (alpha := (470524574071/248420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-506683339/2500000000 : ℝ)*X 0 0+(5477306989/10000000000 : ℝ)*X 0 1+(1296502727/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1341330459/2500000000 : ℝ)*X 1 0+(-544293581/2500000000 : ℝ)*X 1 1+(1037202259/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5365321909/10000000000 : ℝ)*X 2 0+(518601121/1000000000 : ℝ)*X 2 1+(-1088587169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539783327/1250000000 : ℝ)*X 0 0+(4022237203/10000000000 : ℝ)*X 0 1+(4634443849/10000000000 : ℝ)*X 0 2+(539783327/1250000000 : ℝ)*X 1 0+(4022237203/10000000000 : ℝ)*X 1 1+(4634443849/10000000000 : ℝ)*X 1 2+(539783327/1250000000 : ℝ)*X 2 0+(4022237203/10000000000 : ℝ)*X 2 1+(4634443849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-405359347/2000000000 : ℝ)*X 0 0+(2593910087/5000000000 : ℝ)*X 0 1+(219019263/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211606699/400000000 : ℝ)*X 1 0+(-1887703747/10000000000 : ℝ)*X 1 1+(5475481551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058033493/2000000000 : ℝ)*X 2 0+(5475481581/10000000000 : ℝ)*X 2 1+(-1887703719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318400151/10000000000 : ℝ)*X 0 0+(2315320997/5000000000 : ℝ)*X 0 1+(4026073019/10000000000 : ℝ)*X 0 2+(4318400151/10000000000 : ℝ)*X 1 0+(2315320997/5000000000 : ℝ)*X 1 1+(4026073019/10000000000 : ℝ)*X 1 2+(4318400151/10000000000 : ℝ)*X 2 0+(2315320997/5000000000 : ℝ)*X 2 1+(4026073019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12212147539663953583311379899/1552625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1350619397/100000000000000 : ℝ)*(base19) + (1357471289/100000000000000 : ℝ)*(base23) + (10692223/50000000000000 : ℝ)*(lower2) + (45571567/25000000000000 : ℝ)*(upper3) + (147915339/100000000000000 : ℝ)*(upper5) + (2533214114401113/100000000000000 : ℝ)*(major0) + (2533214114401113/100000000000000 : ℝ)*(major1) + (2533214114401113/100000000000000 : ℝ)*(major2) + (26819953351747/781250000000 : ℝ)*(sp0) + (1716486716013591/50000000000000 : ℝ)*(sp1) + (343297342517529/10000000000000 : ℝ)*(sp2) + (1633443974613879/100000000000000 : ℝ)*(sp3) + (20753622963/100000000000000 : ℝ)*(sp4) + (9209358953/100000000000000 : ℝ)*(sp7) + (51045411999151/3125000000000 : ℝ)*(f.failure) + (3432974782646579/100000000000000 : ℝ)*(f.sum) + (37013464353037/12421000000000000000000000000 : ℝ)*base65 + (8708449915114751633/6210500000000000000000000000000000 : ℝ)*base68 + (98998643524962248367/6210500000000000000000000000000000 : ℝ)*base69 + (24465612692438248367/6210500000000000000000000000000000 : ℝ)*base71 + (4407043166037/3105250000000000000000000000 : ℝ)*base74 + (92601762463873748367/6210500000000000000000000000000000 : ℝ)*base75 + (60037602487029248367/6210500000000000000000000000000000 : ℝ)*base77 + (1532086300388248367/6210500000000000000000000000000000 : ℝ)*base79 + (9476361202661/2484200000000000000000000000 : ℝ)*base81 + (50331/156250000000000000000 : ℝ)*base89 + (50331/156250000000000000000 : ℝ)*base91 + (50331/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7269441389240205046040063439/776312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (940945891/50000000000000 : ℝ)*(base19) + (2086382361/100000000000000 : ℝ)*(base23) + (224038519/100000000000000 : ℝ)*(upper3) + (86270403/100000000000000 : ℝ)*(lower4) + (32333081/20000000000000 : ℝ)*(upper5) + (641297306316031/25000000000000 : ℝ)*(major0) + (641297306316031/25000000000000 : ℝ)*(major1) + (641297306316031/25000000000000 : ℝ)*(major2) + (21386782929/100000000000000 : ℝ)*(sp1) + (6191112419/25000000000000 : ℝ)*(sp2) + (1738153469702411/50000000000000 : ℝ)*(sp4) + (27158466177579/781250000000 : ℝ)*(sp5) + (695256017714557/20000000000000 : ℝ)*(sp6) + (827035599493943/50000000000000 : ℝ)*(sp7) + (827035599493943/50000000000000 : ℝ)*(f.failure) + (1738153469702411/50000000000000 : ℝ)*(f.sum) + (3309226170867/3105250000000000000000000000 : ℝ)*base65 + (15410641233989520729/1552625000000000000000000000000000 : ℝ)*base67 + (22817068073113020729/1552625000000000000000000000000000 : ℝ)*base69 + (24530679874804770729/1552625000000000000000000000000000 : ℝ)*base71 + (44959313907/124210000000000000000000000 : ℝ)*base73 + (13289862787455895729/1552625000000000000000000000000000 : ℝ)*base75 + (12573997559059145729/1552625000000000000000000000000000 : ℝ)*base77 + (29480898482344895729/1552625000000000000000000000000000 : ℝ)*base79 + (791761680147/12421000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10461817/2500000000000000000000 : ℝ)*base90 + (10461817/2500000000000000000000 : ℝ)*base92 + (10461817/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1351_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9697/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1351_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1351_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1351_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1351_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
