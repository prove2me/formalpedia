-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1370_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:35.365981+00:00
-- url     : https://prove2.me/submissions/73c45da8-ac3c-44b0-bd51-fdbb1a3ff837

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
theorem support_rectangle_w1370_s3_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009267241/5000000000 : ℝ)*x 0 + (2711861423/5000000000 : ℝ)*x 1 + (5233948609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009267241/5000000000 : ℝ)^2165 ≤ (3074101324423/25000000000000 : ℝ)^1653 := by
    have hnat : (1009267241 : ℕ)^2165*25000000000000^1653 ≤ 3074101324423^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009267241 5000000000 3074101324423 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711861423/5000000000 : ℝ)^2165 ≤ (11218604483551/25000000000000 : ℝ)^1653 := by
    have hnat : (2711861423 : ℕ)^2165*25000000000000^1653 ≤ 11218604483551^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711861423 5000000000 11218604483551 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233948609/10000000000 : ℝ)^2165 ≤ (10707294187903/25000000000000 : ℝ)^1653 := by
    have hnat : (5233948609 : ℕ)^2165*25000000000000^1653 ≤ 10707294187903^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233948609 10000000000 10707294187903 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009267241/5000000000 : ℝ), (2711861423/5000000000 : ℝ), (5233948609/10000000000 : ℝ)] ![(3074101324423/25000000000000 : ℝ), (11218604483551/25000000000000 : ℝ), (10707294187903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009267241/5000000000 : ℝ)|^2165 ≤ (3074101324423/25000000000000 : ℝ)^1653
        have hw : |(-1009267241/5000000000 : ℝ)|=(1009267241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711861423/5000000000 : ℝ)|^2165 ≤ (11218604483551/25000000000000 : ℝ)^1653
        have hw : |(2711861423/5000000000 : ℝ)|=(2711861423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233948609/10000000000 : ℝ)|^2165 ≤ (10707294187903/25000000000000 : ℝ)^1653
        have hw : |(5233948609/10000000000 : ℝ)|=(5233948609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s3_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351687569/10000000000 : ℝ)*x 0 + (-52886429/250000000 : ℝ)*x 1 + (1046789699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351687569/10000000000 : ℝ)^2165 ≤ (8819084596761/20000000000000 : ℝ)^1653 := by
    have hnat : (5351687569 : ℕ)^2165*20000000000000^1653 ≤ 8819084596761^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351687569 10000000000 8819084596761 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52886429/250000000 : ℝ)^2165 ≤ (3268850367219/25000000000000 : ℝ)^1653 := by
    have hnat : (52886429 : ℕ)^2165*25000000000000^1653 ≤ 3268850367219^1653*250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52886429 250000000 3268850367219 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046789699/2000000000 : ℝ)^2165 ≤ (10707293882453/25000000000000 : ℝ)^1653 := by
    have hnat : (1046789699 : ℕ)^2165*25000000000000^1653 ≤ 10707293882453^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046789699 2000000000 10707293882453 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351687569/10000000000 : ℝ), (-52886429/250000000 : ℝ), (1046789699/2000000000 : ℝ)] ![(8819084596761/20000000000000 : ℝ), (3268850367219/25000000000000 : ℝ), (10707293882453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351687569/10000000000 : ℝ)|^2165 ≤ (8819084596761/20000000000000 : ℝ)^1653
        have hw : |(5351687569/10000000000 : ℝ)|=(5351687569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52886429/250000000 : ℝ)|^2165 ≤ (3268850367219/25000000000000 : ℝ)^1653
        have hw : |(-52886429/250000000 : ℝ)|=(52886429/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046789699/2000000000 : ℝ)|^2165 ≤ (10707293882453/25000000000000 : ℝ)^1653
        have hw : |(1046789699/2000000000 : ℝ)|=(1046789699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s3_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351687521/10000000000 : ℝ)*x 0 + (5233948583/10000000000 : ℝ)*x 1 + (-2115457107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351687521/10000000000 : ℝ)^2165 ≤ (22047711232903/50000000000000 : ℝ)^1653 := by
    have hnat : (5351687521 : ℕ)^2165*50000000000000^1653 ≤ 22047711232903^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351687521 10000000000 22047711232903 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233948583/10000000000 : ℝ)^2165 ≤ (10707294118239/25000000000000 : ℝ)^1653 := by
    have hnat : (5233948583 : ℕ)^2165*25000000000000^1653 ≤ 10707294118239^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233948583 10000000000 10707294118239 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115457107/10000000000 : ℝ)^2165 ≤ (13075401039823/100000000000000 : ℝ)^1653 := by
    have hnat : (2115457107 : ℕ)^2165*100000000000000^1653 ≤ 13075401039823^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115457107 10000000000 13075401039823 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351687521/10000000000 : ℝ), (5233948583/10000000000 : ℝ), (-2115457107/10000000000 : ℝ)] ![(22047711232903/50000000000000 : ℝ), (10707294118239/25000000000000 : ℝ), (13075401039823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351687521/10000000000 : ℝ)|^2165 ≤ (22047711232903/50000000000000 : ℝ)^1653
        have hw : |(5351687521/10000000000 : ℝ)|=(5351687521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233948583/10000000000 : ℝ)|^2165 ≤ (10707294118239/25000000000000 : ℝ)^1653
        have hw : |(5233948583/10000000000 : ℝ)|=(5233948583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115457107/10000000000 : ℝ)|^2165 ≤ (13075401039823/100000000000000 : ℝ)^1653
        have hw : |(-2115457107/10000000000 : ℝ)|=(2115457107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s3_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4318444191/10000000000 : ℝ)*x 0 + (4121909111/10000000000 : ℝ)*x 1 + (565449631/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318444191/10000000000 : ℝ)^2165 ≤ (16647293855929/50000000000000 : ℝ)^1653 := by
    have hnat : (4318444191 : ℕ)^2165*50000000000000^1653 ≤ 16647293855929^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318444191 10000000000 16647293855929 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4121909111/10000000000 : ℝ)^2165 ≤ (15662065962973/50000000000000 : ℝ)^1653 := by
    have hnat : (4121909111 : ℕ)^2165*50000000000000^1653 ≤ 15662065962973^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121909111 10000000000 15662065962973 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565449631/1250000000 : ℝ)^2165 ≤ (35381280347659/100000000000000 : ℝ)^1653 := by
    have hnat : (565449631 : ℕ)^2165*100000000000000^1653 ≤ 35381280347659^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565449631 1250000000 35381280347659 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318444191/10000000000 : ℝ), (4121909111/10000000000 : ℝ), (565449631/1250000000 : ℝ)] ![(16647293855929/50000000000000 : ℝ), (15662065962973/50000000000000 : ℝ), (35381280347659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318444191/10000000000 : ℝ)|^2165 ≤ (16647293855929/50000000000000 : ℝ)^1653
        have hw : |(4318444191/10000000000 : ℝ)|=(4318444191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4121909111/10000000000 : ℝ)|^2165 ≤ (15662065962973/50000000000000 : ℝ)^1653
        have hw : |(4121909111/10000000000 : ℝ)|=(4121909111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565449631/1250000000 : ℝ)|^2165 ≤ (35381280347659/100000000000000 : ℝ)^1653
        have hw : |(565449631/1250000000 : ℝ)|=(565449631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s3_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-504638019/2500000000 : ℝ)*x 0 + (2617363587/5000000000 : ℝ)*x 1 + (2711469917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504638019/2500000000 : ℝ)^2165 ≤ (3074136418371/25000000000000 : ℝ)^1653 := by
    have hnat : (504638019 : ℕ)^2165*25000000000000^1653 ≤ 3074136418371^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504638019 2500000000 3074136418371 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617363587/5000000000 : ℝ)^2165 ≤ (5354690156167/12500000000000 : ℝ)^1653 := by
    have hnat : (2617363587 : ℕ)^2165*12500000000000^1653 ≤ 5354690156167^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617363587 5000000000 5354690156167 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711469917/5000000000 : ℝ)^2165 ≤ (11216483266533/25000000000000 : ℝ)^1653 := by
    have hnat : (2711469917 : ℕ)^2165*25000000000000^1653 ≤ 11216483266533^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711469917 5000000000 11216483266533 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504638019/2500000000 : ℝ), (2617363587/5000000000 : ℝ), (2711469917/5000000000 : ℝ)] ![(3074136418371/25000000000000 : ℝ), (5354690156167/12500000000000 : ℝ), (11216483266533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504638019/2500000000 : ℝ)|^2165 ≤ (3074136418371/25000000000000 : ℝ)^1653
        have hw : |(-504638019/2500000000 : ℝ)|=(504638019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617363587/5000000000 : ℝ)|^2165 ≤ (5354690156167/12500000000000 : ℝ)^1653
        have hw : |(2617363587/5000000000 : ℝ)|=(2617363587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711469917/5000000000 : ℝ)|^2165 ≤ (11216483266533/25000000000000 : ℝ)^1653
        have hw : |(2711469917/5000000000 : ℝ)|=(2711469917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s3_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060530313/2000000000 : ℝ)*x 0 + (-240808237/1250000000 : ℝ)*x 1 + (677867479/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060530313/2000000000 : ℝ)^2165 ≤ (2178349807703/5000000000000 : ℝ)^1653 := by
    have hnat : (1060530313 : ℕ)^2165*5000000000000^1653 ≤ 2178349807703^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060530313 2000000000 2178349807703 5000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240808237/1250000000 : ℝ)^2165 ≤ (11567070783157/100000000000000 : ℝ)^1653 := by
    have hnat : (240808237 : ℕ)^2165*100000000000000^1653 ≤ 11567070783157^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240808237 1250000000 11567070783157 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677867479/1250000000 : ℝ)^2165 ≤ (2243296652223/5000000000000 : ℝ)^1653 := by
    have hnat : (677867479 : ℕ)^2165*5000000000000^1653 ≤ 2243296652223^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677867479 1250000000 2243296652223 5000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060530313/2000000000 : ℝ), (-240808237/1250000000 : ℝ), (677867479/1250000000 : ℝ)] ![(2178349807703/5000000000000 : ℝ), (11567070783157/100000000000000 : ℝ), (2243296652223/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060530313/2000000000 : ℝ)|^2165 ≤ (2178349807703/5000000000000 : ℝ)^1653
        have hw : |(1060530313/2000000000 : ℝ)|=(1060530313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240808237/1250000000 : ℝ)|^2165 ≤ (11567070783157/100000000000000 : ℝ)^1653
        have hw : |(-240808237/1250000000 : ℝ)|=(240808237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677867479/1250000000 : ℝ)|^2165 ≤ (2243296652223/5000000000000 : ℝ)^1653
        have hw : |(677867479/1250000000 : ℝ)|=(677867479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s3_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302651487/10000000000 : ℝ)*x 0 + (5422939893/10000000000 : ℝ)*x 1 + (-1926465919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302651487/10000000000 : ℝ)^2165 ≤ (10891748828677/25000000000000 : ℝ)^1653 := by
    have hnat : (5302651487 : ℕ)^2165*25000000000000^1653 ≤ 10891748828677^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302651487 10000000000 10891748828677 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422939893/10000000000 : ℝ)^2165 ≤ (44865933705453/100000000000000 : ℝ)^1653 := by
    have hnat : (5422939893 : ℕ)^2165*100000000000000^1653 ≤ 44865933705453^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422939893 10000000000 44865933705453 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926465919/10000000000 : ℝ)^2165 ≤ (11567070964031/100000000000000 : ℝ)^1653 := by
    have hnat : (1926465919 : ℕ)^2165*100000000000000^1653 ≤ 11567070964031^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926465919 10000000000 11567070964031 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302651487/10000000000 : ℝ), (5422939893/10000000000 : ℝ), (-1926465919/10000000000 : ℝ)] ![(10891748828677/25000000000000 : ℝ), (44865933705453/100000000000000 : ℝ), (11567070964031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302651487/10000000000 : ℝ)|^2165 ≤ (10891748828677/25000000000000 : ℝ)^1653
        have hw : |(5302651487/10000000000 : ℝ)|=(5302651487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422939893/10000000000 : ℝ)|^2165 ≤ (44865933705453/100000000000000 : ℝ)^1653
        have hw : |(5422939893/10000000000 : ℝ)|=(5422939893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926465919/10000000000 : ℝ)|^2165 ≤ (11567070964031/100000000000000 : ℝ)^1653
        have hw : |(-1926465919/10000000000 : ℝ)|=(1926465919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s3_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863696379/2000000000 : ℝ)*x 0 + (1130487237/2500000000 : ℝ)*x 1 + (4123566921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863696379/2000000000 : ℝ)^2165 ≤ (8323742110967/25000000000000 : ℝ)^1653 := by
    have hnat : (863696379 : ℕ)^2165*25000000000000^1653 ≤ 8323742110967^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863696379 2000000000 8323742110967 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130487237/2500000000 : ℝ)^2165 ≤ (8841099491329/25000000000000 : ℝ)^1653 := by
    have hnat : (1130487237 : ℕ)^2165*25000000000000^1653 ≤ 8841099491329^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130487237 2500000000 8841099491329 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4123566921/10000000000 : ℝ)^2165 ≤ (3134063358019/10000000000000 : ℝ)^1653 := by
    have hnat : (4123566921 : ℕ)^2165*10000000000000^1653 ≤ 3134063358019^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123566921 10000000000 3134063358019 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863696379/2000000000 : ℝ), (1130487237/2500000000 : ℝ), (4123566921/10000000000 : ℝ)] ![(8323742110967/25000000000000 : ℝ), (8841099491329/25000000000000 : ℝ), (3134063358019/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863696379/2000000000 : ℝ)|^2165 ≤ (8323742110967/25000000000000 : ℝ)^1653
        have hw : |(863696379/2000000000 : ℝ)|=(863696379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130487237/2500000000 : ℝ)|^2165 ≤ (8841099491329/25000000000000 : ℝ)^1653
        have hw : |(1130487237/2500000000 : ℝ)|=(1130487237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4123566921/10000000000 : ℝ)|^2165 ≤ (3134063358019/10000000000000 : ℝ)^1653
        have hw : |(4123566921/10000000000 : ℝ)|=(4123566921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1371/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2997/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10029/100000 : ℝ) ^ (4329/1024 : ℝ) ≤ (187338761458613/3125000000000000000 : ℝ) := by
    have hpowers : (10029/100000 : ℝ)^4329 ≤ (187338761458613/3125000000000000000 : ℝ)^1024 := by
      have hnat : (10029 : ℕ)^4329*3125000000000000000^1024 ≤ 187338761458613^1024*100000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10029 100000 187338761458613 3125000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10029/100000 : ℝ)) (X := (187338761458613/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15997/100000 : ℝ) ^ (4329/1024 : ℝ) ≤ (21578033363411669/50000000000000000000 : ℝ) := by
    have hpowers : (15997/100000 : ℝ)^4329 ≤ (21578033363411669/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15997 : ℕ)^4329*50000000000000000000^1024 ≤ 21578033363411669^1024*100000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15997 100000 21578033363411669 50000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15997/100000 : ℝ)) (X := (21578033363411669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562687338761458613/1562500000000000000 : ℝ) ≤ (500014179800413/500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (1562687338761458613/1562500000000000000 : ℝ)^1024 ≤ (500014179800413/500000000000000 : ℝ)^4329 := by
      have hnat : (1562687338761458613 : ℕ)^1024*500000000000000^4329 ≤ 500014179800413^4329*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562687338761458613 1562500000000000000 500014179800413 500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014179800413/500000000000000 : ℝ)) (X := (1562687338761458613/1562500000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024575453546749477/50000000000000000000 : ℝ) ≤ (2500290604576349/2500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (50024575453546749477/50000000000000000000 : ℝ)^1024 ≤ (2500290604576349/2500000000000000 : ℝ)^4329 := by
      have hnat : (50024575453546749477 : ℕ)^1024*2500000000000000^4329 ≤ 2500290604576349^4329*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024575453546749477 50000000000000000000 2500290604576349 2500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500290604576349/2500000000000000 : ℝ)) (X := (50024575453546749477/50000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021578033363411669/25000000000000000000 : ℝ) ≤ (2500510310150633/2500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (25021578033363411669/25000000000000000000 : ℝ)^1024 ≤ (2500510310150633/2500000000000000 : ℝ)^4329 := by
      have hnat : (25021578033363411669 : ℕ)^1024*2500000000000000^4329 ≤ 2500510310150633^4329*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021578033363411669 25000000000000000000 2500510310150633 2500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500510310150633/2500000000000000 : ℝ)) (X := (25021578033363411669/25000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(187338761458613/3125000000000000000 : ℝ) ≤ ((1864502033854416931/1865000000000000000 : ℝ)+2*(54926393571/37300000000000 : ℝ)*(10029/100000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (1864502033854416931/1865000000000000000 : ℝ)+2*(54926393571/37300000000000 : ℝ)*(10029/100000 : ℝ)=(500014179800413/500000000000000 : ℝ) by norm_num, show 1+2*(187338761458613/3125000000000000000 : ℝ)=(1562687338761458613/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21578033363411669/50000000000000000000 : ℝ)+(187338761458613/3125000000000000000 : ℝ) ≤ ((1864502033854416931/1865000000000000000 : ℝ)+(54926393571/37300000000000 : ℝ)*((15997/100000 : ℝ)+(10029/100000 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (1864502033854416931/1865000000000000000 : ℝ)+(54926393571/37300000000000 : ℝ)*((15997/100000 : ℝ)+(10029/100000 : ℝ))=(2500290604576349/2500000000000000 : ℝ) by norm_num, show 1+(21578033363411669/50000000000000000000 : ℝ)+(187338761458613/3125000000000000000 : ℝ)=(50024575453546749477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21578033363411669/50000000000000000000 : ℝ) ≤ ((1864502033854416931/1865000000000000000 : ℝ)+2*(54926393571/37300000000000 : ℝ)*(15997/100000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (1864502033854416931/1865000000000000000 : ℝ)+2*(54926393571/37300000000000 : ℝ)*(15997/100000 : ℝ)=(2500510310150633/2500000000000000 : ℝ) by norm_num, show 1+2*(21578033363411669/50000000000000000000 : ℝ)=(25021578033363411669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1864502033854416931/1865000000000000000 : ℝ)*(X 1 0+X 2 0)+(54926393571/37300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (10029/100000 : ℝ)) (hi := (15997/100000 : ℝ)) (c := (1864502033854416931/1865000000000000000 : ℝ)) (alpha := (54926393571/37300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1864502033854416931/1865000000000000000 : ℝ)*(X 0 1+X 2 1)+(54926393571/37300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (10029/100000 : ℝ)) (hi := (15997/100000 : ℝ)) (c := (1864502033854416931/1865000000000000000 : ℝ)) (alpha := (54926393571/37300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1864502033854416931/1865000000000000000 : ℝ)*(X 0 2+X 1 2)+(54926393571/37300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (10029/100000 : ℝ)) (hi := (15997/100000 : ℝ)) (c := (1864502033854416931/1865000000000000000 : ℝ)) (alpha := (54926393571/37300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1009267241/5000000000 : ℝ)*X 0 0+(2711861423/5000000000 : ℝ)*X 0 1+(5233948609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351687569/10000000000 : ℝ)*X 1 0+(-52886429/250000000 : ℝ)*X 1 1+(1046789699/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351687521/10000000000 : ℝ)*X 2 0+(5233948583/10000000000 : ℝ)*X 2 1+(-2115457107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318444191/10000000000 : ℝ)*X 0 0+(4121909111/10000000000 : ℝ)*X 0 1+(565449631/1250000000 : ℝ)*X 0 2+(4318444191/10000000000 : ℝ)*X 1 0+(4121909111/10000000000 : ℝ)*X 1 1+(565449631/1250000000 : ℝ)*X 1 2+(4318444191/10000000000 : ℝ)*X 2 0+(4121909111/10000000000 : ℝ)*X 2 1+(565449631/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-504638019/2500000000 : ℝ)*X 0 0+(2617363587/5000000000 : ℝ)*X 0 1+(2711469917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060530313/2000000000 : ℝ)*X 1 0+(-240808237/1250000000 : ℝ)*X 1 1+(677867479/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302651487/10000000000 : ℝ)*X 2 0+(5422939893/10000000000 : ℝ)*X 2 1+(-1926465919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863696379/2000000000 : ℝ)*X 0 0+(1130487237/2500000000 : ℝ)*X 0 1+(4123566921/10000000000 : ℝ)*X 0 2+(863696379/2000000000 : ℝ)*X 1 0+(1130487237/2500000000 : ℝ)*X 1 1+(4123566921/10000000000 : ℝ)*X 1 2+(863696379/2000000000 : ℝ)*X 2 0+(1130487237/2500000000 : ℝ)*X 2 1+(4123566921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (612039997816049693225234049/93250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (869875193/50000000000000 : ℝ)*(base19) + (1572214063/100000000000000 : ℝ)*(base23) + (10342273/5000000000000 : ℝ)*(upper3) + (64366717/100000000000000 : ℝ)*(upper4) + (170306411/100000000000000 : ℝ)*(upper5) + (3879502428367193/100000000000000 : ℝ)*(major0) + (3879502428367193/100000000000000 : ℝ)*(major1) + (3879502428367193/100000000000000 : ℝ)*(major2) + (5269448824183063/100000000000000 : ℝ)*(sp0) + (5269476834833979/100000000000000 : ℝ)*(sp1) + (5269477002370301/100000000000000 : ℝ)*(sp2) + (622377491581911/25000000000000 : ℝ)*(sp3) + (14875200651/50000000000000 : ℝ)*(sp4) + (16097041317/100000000000000 : ℝ)*(sp7) + (1944942237007/78125000000 : ℝ)*(f.failure) + (1053895714916873/20000000000000 : ℝ)*(f.sum) + (6495224040831/932500000000000000000000000 : ℝ)*base66 + (1737898307584705317/186500000000000000000000000000000 : ℝ)*base68 + (331625750298294683/186500000000000000000000000000000 : ℝ)*base69 + (3028831151410705317/186500000000000000000000000000000 : ℝ)*base72 + (8913033940197/1865000000000000000000000000 : ℝ)*base74 + (12628994293294683/186500000000000000000000000000000 : ℝ)*base75 + (359942814015705317/186500000000000000000000000000000 : ℝ)*base78 + (897994743885205317/186500000000000000000000000000000 : ℝ)*base80 + (11535002568427/1865000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (73/122070312500000000 : ℝ)*base89 + (73/122070312500000000 : ℝ)*base91 + (73/122070312500000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367490671116905239048035471/46625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177417053/12500000000000 : ℝ)*(base19) + (730437937/50000000000000 : ℝ)*(base23) + (154372337/100000000000000 : ℝ)*(upper3) + (59941067/100000000000000 : ℝ)*(lower4) + (85517653/50000000000000 : ℝ)*(upper5) + (3911645272857553/100000000000000 : ℝ)*(major0) + (3911645272857553/100000000000000 : ℝ)*(major1) + (3911645272857553/100000000000000 : ℝ)*(major2) + (13074775383/50000000000000 : ℝ)*(sp1) + (26869070687/100000000000000 : ℝ)*(sp2) + (664142218423379/12500000000000 : ℝ)*(sp4) + (2656555089249921/50000000000000 : ℝ)*(sp5) + (5313109417440471/100000000000000 : ℝ)*(sp6) + (1255076267800077/50000000000000 : ℝ)*(sp7) + (1255076267800077/50000000000000 : ℝ)*(f.failure) + (664142218423379/12500000000000 : ℝ)*(f.sum) + (12595164204493/1865000000000000000000000000 : ℝ)*base65 + (343997859682579843/186500000000000000000000000000000 : ℝ)*base67 + (919314372269579843/186500000000000000000000000000000 : ℝ)*base69 + (615775571411579843/186500000000000000000000000000000 : ℝ)*base71 + (8231722733237/1865000000000000000000000000 : ℝ)*base74 + (66735025920579843/186500000000000000000000000000000 : ℝ)*base75 + (1008032308131579843/186500000000000000000000000000000 : ℝ)*base77 + (585422756011420157/186500000000000000000000000000000 : ℝ)*base80 + (5069064729023/1865000000000000000000000000 : ℝ)*base81 + (17061233/5000000000000000000000 : ℝ)*base90 + (17061233/5000000000000000000000 : ℝ)*base92 + (17061233/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1370_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2997/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1370_s4_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-126236507/625000000 : ℝ)*x 0 + (5413360703/10000000000 : ℝ)*x 1 + (5243489537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126236507/625000000 : ℝ)^2165 ≤ (12306376559453/100000000000000 : ℝ)^1653 := by
    have hnat : (126236507 : ℕ)^2165*100000000000000^1653 ≤ 12306376559453^1653*625000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126236507 625000000 12306376559453 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413360703/10000000000 : ℝ)^2165 ≤ (44762162495273/100000000000000 : ℝ)^1653 := by
    have hnat : (5413360703 : ℕ)^2165*100000000000000^1653 ≤ 44762162495273^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413360703 10000000000 44762162495273 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243489537/10000000000 : ℝ)^2165 ≤ (42931460933467/100000000000000 : ℝ)^1653 := by
    have hnat : (5243489537 : ℕ)^2165*100000000000000^1653 ≤ 42931460933467^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243489537 10000000000 42931460933467 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126236507/625000000 : ℝ), (5413360703/10000000000 : ℝ), (5243489537/10000000000 : ℝ)] ![(12306376559453/100000000000000 : ℝ), (44762162495273/100000000000000 : ℝ), (42931460933467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126236507/625000000 : ℝ)|^2165 ≤ (12306376559453/100000000000000 : ℝ)^1653
        have hw : |(-126236507/625000000 : ℝ)|=(126236507/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413360703/10000000000 : ℝ)|^2165 ≤ (44762162495273/100000000000000 : ℝ)^1653
        have hw : |(5413360703/10000000000 : ℝ)|=(5413360703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243489537/10000000000 : ℝ)|^2165 ≤ (42931460933467/100000000000000 : ℝ)^1653
        have hw : |(5243489537/10000000000 : ℝ)|=(5243489537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s4_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668629429/1250000000 : ℝ)*x 0 + (-1053175241/5000000000 : ℝ)*x 1 + (5243490089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668629429/1250000000 : ℝ)^2165 ≤ (22033402124631/50000000000000 : ℝ)^1653 := by
    have hnat : (668629429 : ℕ)^2165*50000000000000^1653 ≤ 22033402124631^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668629429 1250000000 22033402124631 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053175241/5000000000 : ℝ)^2165 ≤ (1625216110617/12500000000000 : ℝ)^1653 := by
    have hnat : (1053175241 : ℕ)^2165*12500000000000^1653 ≤ 1625216110617^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053175241 5000000000 1625216110617 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243490089/10000000000 : ℝ)^2165 ≤ (4293146685289/10000000000000 : ℝ)^1653 := by
    have hnat : (5243490089 : ℕ)^2165*10000000000000^1653 ≤ 4293146685289^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243490089 10000000000 4293146685289 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668629429/1250000000 : ℝ), (-1053175241/5000000000 : ℝ), (5243490089/10000000000 : ℝ)] ![(22033402124631/50000000000000 : ℝ), (1625216110617/12500000000000 : ℝ), (4293146685289/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668629429/1250000000 : ℝ)|^2165 ≤ (22033402124631/50000000000000 : ℝ)^1653
        have hw : |(668629429/1250000000 : ℝ)|=(668629429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053175241/5000000000 : ℝ)|^2165 ≤ (1625216110617/12500000000000 : ℝ)^1653
        have hw : |(-1053175241/5000000000 : ℝ)|=(1053175241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243490089/10000000000 : ℝ)|^2165 ≤ (4293146685289/10000000000000 : ℝ)^1653
        have hw : |(5243490089/10000000000 : ℝ)|=(5243490089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s4_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674517723/5000000000 : ℝ)*x 0 + (40964761/78125000 : ℝ)*x 1 + (-1053175683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674517723/5000000000 : ℝ)^2165 ≤ (22033402200161/50000000000000 : ℝ)^1653 := by
    have hnat : (2674517723 : ℕ)^2165*50000000000000^1653 ≤ 22033402200161^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674517723 5000000000 22033402200161 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40964761/78125000 : ℝ)^2165 ≤ (10732864887531/25000000000000 : ℝ)^1653 := by
    have hnat : (40964761 : ℕ)^2165*25000000000000^1653 ≤ 10732864887531^1653*78125000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40964761 78125000 10732864887531 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053175683/5000000000 : ℝ)^2165 ≤ (13001736031673/100000000000000 : ℝ)^1653 := by
    have hnat : (1053175683 : ℕ)^2165*100000000000000^1653 ≤ 13001736031673^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053175683 5000000000 13001736031673 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674517723/5000000000 : ℝ), (40964761/78125000 : ℝ), (-1053175683/5000000000 : ℝ)] ![(22033402200161/50000000000000 : ℝ), (10732864887531/25000000000000 : ℝ), (13001736031673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674517723/5000000000 : ℝ)|^2165 ≤ (22033402200161/50000000000000 : ℝ)^1653
        have hw : |(2674517723/5000000000 : ℝ)|=(2674517723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40964761/78125000 : ℝ)|^2165 ≤ (10732864887531/25000000000000 : ℝ)^1653
        have hw : |(40964761/78125000 : ℝ)|=(40964761/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053175683/5000000000 : ℝ)|^2165 ≤ (13001736031673/100000000000000 : ℝ)^1653
        have hw : |(-1053175683/5000000000 : ℝ)|=(1053175683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s4_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4319207021/10000000000 : ℝ)*x 0 + (2071439411/5000000000 : ℝ)*x 1 + (7203903/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319207021/10000000000 : ℝ)^2165 ≤ (33302290909163/100000000000000 : ℝ)^1653 := by
    have hnat : (4319207021 : ℕ)^2165*100000000000000^1653 ≤ 33302290909163^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319207021 10000000000 33302290909163 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071439411/5000000000 : ℝ)^2165 ≤ (3153301332329/10000000000000 : ℝ)^1653 := by
    have hnat : (2071439411 : ℕ)^2165*10000000000000^1653 ≤ 3153301332329^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071439411 5000000000 3153301332329 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7203903/16000000 : ℝ)^2165 ≤ (4395586970291/12500000000000 : ℝ)^1653 := by
    have hnat : (7203903 : ℕ)^2165*12500000000000^1653 ≤ 4395586970291^1653*16000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7203903 16000000 4395586970291 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319207021/10000000000 : ℝ), (2071439411/5000000000 : ℝ), (7203903/16000000 : ℝ)] ![(33302290909163/100000000000000 : ℝ), (3153301332329/10000000000000 : ℝ), (4395586970291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319207021/10000000000 : ℝ)|^2165 ≤ (33302290909163/100000000000000 : ℝ)^1653
        have hw : |(4319207021/10000000000 : ℝ)|=(4319207021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071439411/5000000000 : ℝ)|^2165 ≤ (3153301332329/10000000000000 : ℝ)^1653
        have hw : |(2071439411/5000000000 : ℝ)|=(2071439411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7203903/16000000 : ℝ)|^2165 ≤ (4395586970291/12500000000000 : ℝ)^1653
        have hw : |(7203903/16000000 : ℝ)|=(7203903/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s4_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-504949167/2500000000 : ℝ)*x 0 + (5244113773/10000000000 : ℝ)*x 1 + (5412733327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504949167/2500000000 : ℝ)^2165 ≤ (6153238379069/50000000000000 : ℝ)^1653 := by
    have hnat : (504949167 : ℕ)^2165*50000000000000^1653 ≤ 6153238379069^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504949167 2500000000 6153238379069 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244113773/10000000000 : ℝ)^2165 ≤ (42938155109473/100000000000000 : ℝ)^1653 := by
    have hnat : (5244113773 : ℕ)^2165*100000000000000^1653 ≤ 42938155109473^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244113773 10000000000 42938155109473 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412733327/10000000000 : ℝ)^2165 ≤ (22377684062223/50000000000000 : ℝ)^1653 := by
    have hnat : (5412733327 : ℕ)^2165*50000000000000^1653 ≤ 22377684062223^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412733327 10000000000 22377684062223 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504949167/2500000000 : ℝ), (5244113773/10000000000 : ℝ), (5412733327/10000000000 : ℝ)] ![(6153238379069/50000000000000 : ℝ), (42938155109473/100000000000000 : ℝ), (22377684062223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504949167/2500000000 : ℝ)|^2165 ≤ (6153238379069/50000000000000 : ℝ)^1653
        have hw : |(-504949167/2500000000 : ℝ)|=(504949167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244113773/10000000000 : ℝ)|^2165 ≤ (42938155109473/100000000000000 : ℝ)^1653
        have hw : |(5244113773/10000000000 : ℝ)|=(5244113773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412733327/10000000000 : ℝ)|^2165 ≤ (22377684062223/50000000000000 : ℝ)^1653
        have hw : |(5412733327/10000000000 : ℝ)|=(5412733327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s4_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326285709/2500000000 : ℝ)*x 0 + (-1937107241/10000000000 : ℝ)*x 1 + (2706366611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326285709/2500000000 : ℝ)^2165 ≤ (43593806482921/100000000000000 : ℝ)^1653 := by
    have hnat : (1326285709 : ℕ)^2165*100000000000000^1653 ≤ 43593806482921^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326285709 2500000000 43593806482921 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1937107241/10000000000 : ℝ)^2165 ≤ (11650826514079/100000000000000 : ℝ)^1653 := by
    have hnat : (1937107241 : ℕ)^2165*100000000000000^1653 ≤ 11650826514079^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937107241 10000000000 11650826514079 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706366611/5000000000 : ℝ)^2165 ≤ (8951073397467/20000000000000 : ℝ)^1653 := by
    have hnat : (2706366611 : ℕ)^2165*20000000000000^1653 ≤ 8951073397467^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706366611 5000000000 8951073397467 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326285709/2500000000 : ℝ), (-1937107241/10000000000 : ℝ), (2706366611/5000000000 : ℝ)] ![(43593806482921/100000000000000 : ℝ), (11650826514079/100000000000000 : ℝ), (8951073397467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326285709/2500000000 : ℝ)|^2165 ≤ (43593806482921/100000000000000 : ℝ)^1653
        have hw : |(1326285709/2500000000 : ℝ)|=(1326285709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1937107241/10000000000 : ℝ)|^2165 ≤ (11650826514079/100000000000000 : ℝ)^1653
        have hw : |(-1937107241/10000000000 : ℝ)|=(1937107241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706366611/5000000000 : ℝ)|^2165 ≤ (8951073397467/20000000000000 : ℝ)^1653
        have hw : |(2706366611/5000000000 : ℝ)|=(2706366611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s4_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305142857/10000000000 : ℝ)*x 0 + (1353183303/2500000000 : ℝ)*x 1 + (-77484289/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305142857/10000000000 : ℝ)^2165 ≤ (43593806708933/100000000000000 : ℝ)^1653 := by
    have hnat : (5305142857 : ℕ)^2165*100000000000000^1653 ≤ 43593806708933^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305142857 10000000000 43593806708933 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353183303/2500000000 : ℝ)^2165 ≤ (44755366879039/100000000000000 : ℝ)^1653 := by
    have hnat : (1353183303 : ℕ)^2165*100000000000000^1653 ≤ 44755366879039^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353183303 2500000000 44755366879039 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77484289/400000000 : ℝ)^2165 ≤ (291270659701/2500000000000 : ℝ)^1653 := by
    have hnat : (77484289 : ℕ)^2165*2500000000000^1653 ≤ 291270659701^1653*400000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77484289 400000000 291270659701 2500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305142857/10000000000 : ℝ), (1353183303/2500000000 : ℝ), (-77484289/400000000 : ℝ)] ![(43593806708933/100000000000000 : ℝ), (44755366879039/100000000000000 : ℝ), (291270659701/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305142857/10000000000 : ℝ)|^2165 ≤ (43593806708933/100000000000000 : ℝ)^1653
        have hw : |(5305142857/10000000000 : ℝ)|=(5305142857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353183303/2500000000 : ℝ)|^2165 ≤ (44755366879039/100000000000000 : ℝ)^1653
        have hw : |(1353183303/2500000000 : ℝ)|=(1353183303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77484289/400000000 : ℝ)|^2165 ≤ (291270659701/2500000000000 : ℝ)^1653
        have hw : |(-77484289/400000000 : ℝ)|=(77484289/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s4_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4319233059/10000000000 : ℝ)*x 0 + (4501118169/10000000000 : ℝ)*x 1 + (165768321/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319233059/10000000000 : ℝ)^2165 ≤ (16651276926551/50000000000000 : ℝ)^1653 := by
    have hnat : (4319233059 : ℕ)^2165*50000000000000^1653 ≤ 16651276926551^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319233059 10000000000 16651276926551 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501118169/10000000000 : ℝ)^2165 ≤ (7030236284493/20000000000000 : ℝ)^1653 := by
    have hnat : (4501118169 : ℕ)^2165*20000000000000^1653 ≤ 7030236284493^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501118169 10000000000 7030236284493 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165768321/400000000 : ℝ)^2165 ≤ (7886566176379/25000000000000 : ℝ)^1653 := by
    have hnat : (165768321 : ℕ)^2165*25000000000000^1653 ≤ 7886566176379^1653*400000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165768321 400000000 7886566176379 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319233059/10000000000 : ℝ), (4501118169/10000000000 : ℝ), (165768321/400000000 : ℝ)] ![(16651276926551/50000000000000 : ℝ), (7030236284493/20000000000000 : ℝ), (7886566176379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319233059/10000000000 : ℝ)|^2165 ≤ (16651276926551/50000000000000 : ℝ)^1653
        have hw : |(4319233059/10000000000 : ℝ)|=(4319233059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501118169/10000000000 : ℝ)|^2165 ≤ (7030236284493/20000000000000 : ℝ)^1653
        have hw : |(4501118169/10000000000 : ℝ)|=(4501118169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165768321/400000000 : ℝ)|^2165 ≤ (7886566176379/25000000000000 : ℝ)^1653
        have hw : |(165768321/400000000 : ℝ)|=(165768321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2997/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2997/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2997/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2997/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2997/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2997/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2997/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1371/12500 : ℝ) ^ (4329/1024 : ℝ) ≤ (8751878203218371/100000000000000000000 : ℝ) := by
    have hpowers : (1371/12500 : ℝ)^4329 ≤ (8751878203218371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1371 : ℕ)^4329*100000000000000000000^1024 ≤ 8751878203218371^1024*12500^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1371 12500 8751878203218371 100000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1371/12500 : ℝ)) (X := (8751878203218371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2997/20000 : ℝ) ^ (4329/1024 : ℝ) ≤ (4092292910131601/12500000000000000000 : ℝ) := by
    have hpowers : (2997/20000 : ℝ)^4329 ≤ (4092292910131601/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2997 : ℕ)^4329*12500000000000000000^1024 ≤ 4092292910131601^1024*20000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2997 20000 4092292910131601 12500000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2997/20000 : ℝ)) (X := (4092292910131601/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008751878203218371/50000000000000000000 : ℝ) ≤ (10000414013607549/10000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (50008751878203218371/50000000000000000000 : ℝ)^1024 ≤ (10000414013607549/10000000000000000 : ℝ)^4329 := by
      have hnat : (50008751878203218371 : ℕ)^1024*10000000000000000^4329 ≤ 10000414013607549^4329*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008751878203218371 50000000000000000000 10000414013607549 10000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000414013607549/10000000000000000 : ℝ)) (X := (50008751878203218371/50000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041490221484271179/100000000000000000000 : ℝ) ≤ (10000981271876203/10000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (100041490221484271179/100000000000000000000 : ℝ)^1024 ≤ (10000981271876203/10000000000000000 : ℝ)^4329 := by
      have hnat : (100041490221484271179 : ℕ)^1024*10000000000000000^4329 ≤ 10000981271876203^4329*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041490221484271179 100000000000000000000 10000981271876203 10000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000981271876203/10000000000000000 : ℝ)) (X := (100041490221484271179/100000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254092292910131601/6250000000000000000 : ℝ) ≤ (10001548530144857/10000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (6254092292910131601/6250000000000000000 : ℝ)^1024 ≤ (10001548530144857/10000000000000000 : ℝ)^4329 := by
      have hnat : (6254092292910131601 : ℕ)^1024*10000000000000000^4329 ≤ 10001548530144857^4329*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254092292910131601 6250000000000000000 10001548530144857 10000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001548530144857/10000000000000000 : ℝ)) (X := (6254092292910131601/6250000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8751878203218371/100000000000000000000 : ℝ) ≤ ((13386406571760110063/13390000000000000000 : ℝ)+2*(283629134327/200850000000000 : ℝ)*(1371/12500 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (13386406571760110063/13390000000000000000 : ℝ)+2*(283629134327/200850000000000 : ℝ)*(1371/12500 : ℝ)=(10000414013607549/10000000000000000 : ℝ) by norm_num, show 1+2*(8751878203218371/100000000000000000000 : ℝ)=(50008751878203218371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4092292910131601/12500000000000000000 : ℝ)+(8751878203218371/100000000000000000000 : ℝ) ≤ ((13386406571760110063/13390000000000000000 : ℝ)+(283629134327/200850000000000 : ℝ)*((2997/20000 : ℝ)+(1371/12500 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (13386406571760110063/13390000000000000000 : ℝ)+(283629134327/200850000000000 : ℝ)*((2997/20000 : ℝ)+(1371/12500 : ℝ))=(10000981271876203/10000000000000000 : ℝ) by norm_num, show 1+(4092292910131601/12500000000000000000 : ℝ)+(8751878203218371/100000000000000000000 : ℝ)=(100041490221484271179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4092292910131601/12500000000000000000 : ℝ) ≤ ((13386406571760110063/13390000000000000000 : ℝ)+2*(283629134327/200850000000000 : ℝ)*(2997/20000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (13386406571760110063/13390000000000000000 : ℝ)+2*(283629134327/200850000000000 : ℝ)*(2997/20000 : ℝ)=(10001548530144857/10000000000000000 : ℝ) by norm_num, show 1+2*(4092292910131601/12500000000000000000 : ℝ)=(6254092292910131601/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13386406571760110063/13390000000000000000 : ℝ)*(X 1 0+X 2 0)+(283629134327/200850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (2997/20000 : ℝ)) (c := (13386406571760110063/13390000000000000000 : ℝ)) (alpha := (283629134327/200850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13386406571760110063/13390000000000000000 : ℝ)*(X 0 1+X 2 1)+(283629134327/200850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (2997/20000 : ℝ)) (c := (13386406571760110063/13390000000000000000 : ℝ)) (alpha := (283629134327/200850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13386406571760110063/13390000000000000000 : ℝ)*(X 0 2+X 1 2)+(283629134327/200850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (2997/20000 : ℝ)) (c := (13386406571760110063/13390000000000000000 : ℝ)) (alpha := (283629134327/200850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-126236507/625000000 : ℝ)*X 0 0+(5413360703/10000000000 : ℝ)*X 0 1+(5243489537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668629429/1250000000 : ℝ)*X 1 0+(-1053175241/5000000000 : ℝ)*X 1 1+(5243490089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674517723/5000000000 : ℝ)*X 2 0+(40964761/78125000 : ℝ)*X 2 1+(-1053175683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319207021/10000000000 : ℝ)*X 0 0+(2071439411/5000000000 : ℝ)*X 0 1+(7203903/16000000 : ℝ)*X 0 2+(4319207021/10000000000 : ℝ)*X 1 0+(2071439411/5000000000 : ℝ)*X 1 1+(7203903/16000000 : ℝ)*X 1 2+(4319207021/10000000000 : ℝ)*X 2 0+(2071439411/5000000000 : ℝ)*X 2 1+(7203903/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-504949167/2500000000 : ℝ)*X 0 0+(5244113773/10000000000 : ℝ)*X 0 1+(5412733327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326285709/2500000000 : ℝ)*X 1 0+(-1937107241/10000000000 : ℝ)*X 1 1+(2706366611/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305142857/10000000000 : ℝ)*X 2 0+(1353183303/2500000000 : ℝ)*X 2 1+(-77484289/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319233059/10000000000 : ℝ)*X 0 0+(4501118169/10000000000 : ℝ)*X 0 1+(165768321/400000000 : ℝ)*X 0 2+(4319233059/10000000000 : ℝ)*X 1 0+(4501118169/10000000000 : ℝ)*X 1 1+(165768321/400000000 : ℝ)*X 1 2+(4319233059/10000000000 : ℝ)*X 2 0+(4501118169/10000000000 : ℝ)*X 2 1+(165768321/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2514096495305921308705188057/669500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35969511/3125000000000 : ℝ)*(base19) + (1234191659/100000000000000 : ℝ)*(base23) + (269596281/50000000000000 : ℝ)*(upper3) + (9015137/10000000000000 : ℝ)*(lower4) + (4334043621380413/100000000000000 : ℝ)*(major0) + (4334043621380413/100000000000000 : ℝ)*(major1) + (4334043621380413/100000000000000 : ℝ)*(major2) + (5886856497518691/100000000000000 : ℝ)*(sp0) + (1471718759239621/25000000000000 : ℝ)*(sp1) + (5886862672331227/100000000000000 : ℝ)*(sp2) + (2781188344548503/100000000000000 : ℝ)*(sp3) + (9845232073/50000000000000 : ℝ)*(sp4) + (12281459951/100000000000000 : ℝ)*(sp6) + (35289151/156250000000 : ℝ)*(sp7) + (2781210929605143/100000000000000 : ℝ)*(f.failure) + (1471719046995709/25000000000000 : ℝ)*(f.sum) + (59089104549847/20085000000000000000000000000 : ℝ)*base65 + (30254550900341611943/4017000000000000000000000000000000 : ℝ)*base68 + (28732080492350611943/4017000000000000000000000000000000 : ℝ)*base70 + (15551990405040388057/4017000000000000000000000000000000 : ℝ)*base71 + (8838685456157/5021250000000000000000000000 : ℝ)*base74 + (12702329440110388057/4017000000000000000000000000000000 : ℝ)*base75 + (19901598320696611943/4017000000000000000000000000000000 : ℝ)*base78 + (23823549199490611943/4017000000000000000000000000000000 : ℝ)*base80 + (60607097750411/10042500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (9430147/10000000000000000000000 : ℝ)*base90 + (9430147/10000000000000000000000 : ℝ)*base92 + (9430147/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20005662398608182957/6437500000000000000000000 : ℝ) := by norm_num
    linear_combination (613215163/100000000000000 : ℝ)*(base19) + (781375629/100000000000000 : ℝ)*(base23) + (32358493/50000000000000 : ℝ)*(upper2) + (40177247/100000000000000 : ℝ)*(upper3) + (26393391/50000000000000 : ℝ)*(upper5) + (174646697124237/4000000000000 : ℝ)*(major0) + (174646697124237/4000000000000 : ℝ)*(major1) + (174646697124237/4000000000000 : ℝ)*(major2) + (2113533989/20000000000000 : ℝ)*(sp1) + (13310839611/100000000000000 : ℝ)*(sp2) + (5930509567562221/100000000000000 : ℝ)*(sp4) + (5930498386677113/100000000000000 : ℝ)*(sp5) + (5930495475346981/100000000000000 : ℝ)*(sp6) + (700456296265109/25000000000000 : ℝ)*(sp7) + (700456296265109/25000000000000 : ℝ)*(f.failure) + (5930509567562221/100000000000000 : ℝ)*(f.sum) + (31016294761/51500000000000000000000000 : ℝ)*base65 + (19119715521463313/4120000000000000000000000000000 : ℝ)*base68 + (9578941080536687/4120000000000000000000000000000 : ℝ)*base69 + (5008822291263313/4120000000000000000000000000000 : ℝ)*base72 + (641256443573/103000000000000000000000000 : ℝ)*base74 + (7931007313656687/4120000000000000000000000000000 : ℝ)*base75 + (4282138146936687/4120000000000000000000000000000 : ℝ)*base77 + (2505417640703313/4120000000000000000000000000000 : ℝ)*base80 + (168865441137/103000000000000000000000000 : ℝ)*base82 + (14108839/2500000000000000000000 : ℝ)*base89 + (14108839/2500000000000000000000 : ℝ)*base91 + (14108839/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1370_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2997/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1370_s5_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-201999059/1000000000 : ℝ)*x 0 + (43292509/80000000 : ℝ)*x 1 + (5245150619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201999059/1000000000 : ℝ)^2165 ≤ (1230802430807/10000000000000 : ℝ)^1653 := by
    have hnat : (201999059 : ℕ)^2165*10000000000000^1653 ≤ 1230802430807^1653*1000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201999059 1000000000 1230802430807 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43292509/80000000 : ℝ)^2165 ≤ (44742701110563/100000000000000 : ℝ)^1653 := by
    have hnat : (43292509 : ℕ)^2165*100000000000000^1653 ≤ 44742701110563^1653*80000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43292509 80000000 44742701110563 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245150619/10000000000 : ℝ)^2165 ≤ (42949274574067/100000000000000 : ℝ)^1653 := by
    have hnat : (5245150619 : ℕ)^2165*100000000000000^1653 ≤ 42949274574067^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245150619 10000000000 42949274574067 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201999059/1000000000 : ℝ), (43292509/80000000 : ℝ), (5245150619/10000000000 : ℝ)] ![(1230802430807/10000000000000 : ℝ), (44742701110563/100000000000000 : ℝ), (42949274574067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201999059/1000000000 : ℝ)|^2165 ≤ (1230802430807/10000000000000 : ℝ)^1653
        have hw : |(-201999059/1000000000 : ℝ)|=(201999059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43292509/80000000 : ℝ)|^2165 ≤ (44742701110563/100000000000000 : ℝ)^1653
        have hw : |(43292509/80000000 : ℝ)|=(43292509/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245150619/10000000000 : ℝ)|^2165 ≤ (42949274574067/100000000000000 : ℝ)^1653
        have hw : |(5245150619/10000000000 : ℝ)|=(5245150619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s5_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348574417/10000000000 : ℝ)*x 0 + (-105238147/500000000 : ℝ)*x 1 + (5245150583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348574417/10000000000 : ℝ)^2165 ≤ (44061829967427/100000000000000 : ℝ)^1653 := by
    have hnat : (5348574417 : ℕ)^2165*100000000000000^1653 ≤ 44061829967427^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348574417 10000000000 44061829967427 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105238147/500000000 : ℝ)^2165 ≤ (12988895830521/100000000000000 : ℝ)^1653 := by
    have hnat : (105238147 : ℕ)^2165*100000000000000^1653 ≤ 12988895830521^1653*500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105238147 500000000 12988895830521 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245150583/10000000000 : ℝ)^2165 ≤ (2147463709399/5000000000000 : ℝ)^1653 := by
    have hnat : (5245150583 : ℕ)^2165*5000000000000^1653 ≤ 2147463709399^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245150583 10000000000 2147463709399 5000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348574417/10000000000 : ℝ), (-105238147/500000000 : ℝ), (5245150583/10000000000 : ℝ)] ![(44061829967427/100000000000000 : ℝ), (12988895830521/100000000000000 : ℝ), (2147463709399/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348574417/10000000000 : ℝ)|^2165 ≤ (44061829967427/100000000000000 : ℝ)^1653
        have hw : |(5348574417/10000000000 : ℝ)|=(5348574417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105238147/500000000 : ℝ)|^2165 ≤ (12988895830521/100000000000000 : ℝ)^1653
        have hw : |(-105238147/500000000 : ℝ)|=(105238147/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245150583/10000000000 : ℝ)|^2165 ≤ (2147463709399/5000000000000 : ℝ)^1653
        have hw : |(5245150583/10000000000 : ℝ)|=(5245150583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s5_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674287239/5000000000 : ℝ)*x 0 + (5245150607/10000000000 : ℝ)*x 1 + (-2104762827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674287239/5000000000 : ℝ)^2165 ≤ (44061830625599/100000000000000 : ℝ)^1653 := by
    have hnat : (2674287239 : ℕ)^2165*100000000000000^1653 ≤ 44061830625599^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674287239 5000000000 44061830625599 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245150607/10000000000 : ℝ)^2165 ≤ (42949274445371/100000000000000 : ℝ)^1653 := by
    have hnat : (5245150607 : ℕ)^2165*100000000000000^1653 ≤ 42949274445371^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245150607 10000000000 42949274445371 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104762827/10000000000 : ℝ)^2165 ≤ (12988894917181/100000000000000 : ℝ)^1653 := by
    have hnat : (2104762827 : ℕ)^2165*100000000000000^1653 ≤ 12988894917181^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104762827 10000000000 12988894917181 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674287239/5000000000 : ℝ), (5245150607/10000000000 : ℝ), (-2104762827/10000000000 : ℝ)] ![(44061830625599/100000000000000 : ℝ), (42949274445371/100000000000000 : ℝ), (12988894917181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674287239/5000000000 : ℝ)|^2165 ≤ (44061830625599/100000000000000 : ℝ)^1653
        have hw : |(2674287239/5000000000 : ℝ)|=(2674287239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245150607/10000000000 : ℝ)|^2165 ≤ (42949274445371/100000000000000 : ℝ)^1653
        have hw : |(5245150607/10000000000 : ℝ)|=(5245150607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104762827/10000000000 : ℝ)|^2165 ≤ (12988894917181/100000000000000 : ℝ)^1653
        have hw : |(-2104762827/10000000000 : ℝ)|=(2104762827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s5_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4319329903/10000000000 : ℝ)*x 0 + (4146524799/10000000000 : ℝ)*x 1 + (2249381963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319329903/10000000000 : ℝ)^2165 ≤ (8325882958389/25000000000000 : ℝ)^1653 := by
    have hnat : (4319329903 : ℕ)^2165*25000000000000^1653 ≤ 8325882958389^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319329903 10000000000 8325882958389 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146524799/10000000000 : ℝ)^2165 ≤ (986542648257/3125000000000 : ℝ)^1653 := by
    have hnat : (4146524799 : ℕ)^2165*3125000000000^1653 ≤ 986542648257^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146524799 10000000000 986542648257 3125000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249381963/5000000000 : ℝ)^2165 ≤ (7025420681703/20000000000000 : ℝ)^1653 := by
    have hnat : (2249381963 : ℕ)^2165*20000000000000^1653 ≤ 7025420681703^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249381963 5000000000 7025420681703 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319329903/10000000000 : ℝ), (4146524799/10000000000 : ℝ), (2249381963/5000000000 : ℝ)] ![(8325882958389/25000000000000 : ℝ), (986542648257/3125000000000 : ℝ), (7025420681703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319329903/10000000000 : ℝ)|^2165 ≤ (8325882958389/25000000000000 : ℝ)^1653
        have hw : |(4319329903/10000000000 : ℝ)|=(4319329903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146524799/10000000000 : ℝ)|^2165 ≤ (986542648257/3125000000000 : ℝ)^1653
        have hw : |(4146524799/10000000000 : ℝ)|=(4146524799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249381963/5000000000 : ℝ)|^2165 ≤ (7025420681703/20000000000000 : ℝ)^1653
        have hw : |(2249381963/5000000000 : ℝ)|=(2249381963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s5_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-505000661/2500000000 : ℝ)*x 0 + (2622874939/5000000000 : ℝ)*x 1 + (5410961231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505000661/2500000000 : ℝ)^2165 ≤ (3077030125941/25000000000000 : ℝ)^1653 := by
    have hnat : (505000661 : ℕ)^2165*25000000000000^1653 ≤ 3077030125941^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505000661 2500000000 3077030125941 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622874939/5000000000 : ℝ)^2165 ≤ (42955701527681/100000000000000 : ℝ)^1653 := by
    have hnat : (2622874939 : ℕ)^2165*100000000000000^1653 ≤ 42955701527681^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622874939 5000000000 42955701527681 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410961231/10000000000 : ℝ)^2165 ≤ (44736177956627/100000000000000 : ℝ)^1653 := by
    have hnat : (5410961231 : ℕ)^2165*100000000000000^1653 ≤ 44736177956627^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410961231 10000000000 44736177956627 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505000661/2500000000 : ℝ), (2622874939/5000000000 : ℝ), (5410961231/10000000000 : ℝ)] ![(3077030125941/25000000000000 : ℝ), (42955701527681/100000000000000 : ℝ), (44736177956627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505000661/2500000000 : ℝ)|^2165 ≤ (3077030125941/25000000000000 : ℝ)^1653
        have hw : |(-505000661/2500000000 : ℝ)|=(505000661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622874939/5000000000 : ℝ)|^2165 ≤ (42955701527681/100000000000000 : ℝ)^1653
        have hw : |(2622874939/5000000000 : ℝ)|=(2622874939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410961231/10000000000 : ℝ)|^2165 ≤ (44736177956627/100000000000000 : ℝ)^1653
        have hw : |(5410961231/10000000000 : ℝ)|=(5410961231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s5_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305575123/10000000000 : ℝ)*x 0 + (-1938952281/10000000000 : ℝ)*x 1 + (1082192247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305575123/10000000000 : ℝ)^2165 ≤ (681225922283/1562500000000 : ℝ)^1653 := by
    have hnat : (5305575123 : ℕ)^2165*1562500000000^1653 ≤ 681225922283^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305575123 10000000000 681225922283 1562500000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938952281/10000000000 : ℝ)^2165 ≤ (145817036879/1250000000000 : ℝ)^1653 := by
    have hnat : (1938952281 : ℕ)^2165*1250000000000^1653 ≤ 145817036879^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938952281 10000000000 145817036879 1250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082192247/2000000000 : ℝ)^2165 ≤ (44736177999941/100000000000000 : ℝ)^1653 := by
    have hnat : (1082192247 : ℕ)^2165*100000000000000^1653 ≤ 44736177999941^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082192247 2000000000 44736177999941 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305575123/10000000000 : ℝ), (-1938952281/10000000000 : ℝ), (1082192247/2000000000 : ℝ)] ![(681225922283/1562500000000 : ℝ), (145817036879/1250000000000 : ℝ), (44736177999941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305575123/10000000000 : ℝ)|^2165 ≤ (681225922283/1562500000000 : ℝ)^1653
        have hw : |(5305575123/10000000000 : ℝ)|=(5305575123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1938952281/10000000000 : ℝ)|^2165 ≤ (145817036879/1250000000000 : ℝ)^1653
        have hw : |(-1938952281/10000000000 : ℝ)|=(1938952281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082192247/2000000000 : ℝ)|^2165 ≤ (44736177999941/100000000000000 : ℝ)^1653
        have hw : |(1082192247/2000000000 : ℝ)|=(1082192247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s5_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326393781/2500000000 : ℝ)*x 0 + (338185077/625000000 : ℝ)*x 1 + (-969476143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326393781/2500000000 : ℝ)^2165 ≤ (69757534459/160000000000 : ℝ)^1653 := by
    have hnat : (1326393781 : ℕ)^2165*160000000000^1653 ≤ 69757534459^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326393781 2500000000 69757534459 160000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338185077/625000000 : ℝ)^2165 ≤ (1398005561483/3125000000000 : ℝ)^1653 := by
    have hnat : (338185077 : ℕ)^2165*3125000000000^1653 ≤ 1398005561483^1653*625000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338185077 625000000 1398005561483 3125000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969476143/5000000000 : ℝ)^2165 ≤ (11665362989719/100000000000000 : ℝ)^1653 := by
    have hnat : (969476143 : ℕ)^2165*100000000000000^1653 ≤ 11665362989719^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969476143 5000000000 11665362989719 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326393781/2500000000 : ℝ), (338185077/625000000 : ℝ), (-969476143/5000000000 : ℝ)] ![(69757534459/160000000000 : ℝ), (1398005561483/3125000000000 : ℝ), (11665362989719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326393781/2500000000 : ℝ)|^2165 ≤ (69757534459/160000000000 : ℝ)^1653
        have hw : |(1326393781/2500000000 : ℝ)|=(1326393781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338185077/625000000 : ℝ)|^2165 ≤ (1398005561483/3125000000000 : ℝ)^1653
        have hw : |(338185077/625000000 : ℝ)|=(338185077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-969476143/5000000000 : ℝ)|^2165 ≤ (11665362989719/100000000000000 : ℝ)^1653
        have hw : |(-969476143/5000000000 : ℝ)|=(969476143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s5_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863871097/2000000000 : ℝ)*x 0 + (1124373913/2500000000 : ℝ)*x 1 + (1036949871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863871097/2000000000 : ℝ)^2165 ≤ (16651895087433/50000000000000 : ℝ)^1653 := by
    have hnat : (863871097 : ℕ)^2165*50000000000000^1653 ≤ 16651895087433^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863871097 2000000000 16651895087433 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124373913/2500000000 : ℝ)^2165 ≤ (17557066878477/50000000000000 : ℝ)^1653 := by
    have hnat : (1124373913 : ℕ)^2165*50000000000000^1653 ≤ 17557066878477^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124373913 2500000000 17557066878477 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036949871/2500000000 : ℝ)^2165 ≤ (15791038025093/50000000000000 : ℝ)^1653 := by
    have hnat : (1036949871 : ℕ)^2165*50000000000000^1653 ≤ 15791038025093^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036949871 2500000000 15791038025093 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863871097/2000000000 : ℝ), (1124373913/2500000000 : ℝ), (1036949871/2500000000 : ℝ)] ![(16651895087433/50000000000000 : ℝ), (17557066878477/50000000000000 : ℝ), (15791038025093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863871097/2000000000 : ℝ)|^2165 ≤ (16651895087433/50000000000000 : ℝ)^1653
        have hw : |(863871097/2000000000 : ℝ)|=(863871097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124373913/2500000000 : ℝ)|^2165 ≤ (17557066878477/50000000000000 : ℝ)^1653
        have hw : |(1124373913/2500000000 : ℝ)|=(1124373913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036949871/2500000000 : ℝ)|^2165 ≤ (15791038025093/50000000000000 : ℝ)^1653
        have hw : |(1036949871/2500000000 : ℝ)|=(1036949871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2793/25000 : ℝ) ^ (4329/1024 : ℝ) ≤ (9460984078540251/100000000000000000000 : ℝ) := by
    have hpowers : (2793/25000 : ℝ)^4329 ≤ (9460984078540251/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2793 : ℕ)^4329*100000000000000000000^1024 ≤ 9460984078540251^1024*25000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2793 25000 9460984078540251 100000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2793/25000 : ℝ)) (X := (9460984078540251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (4329/1024 : ℝ) ≤ (15390225163353783/50000000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^4329 ≤ (15390225163353783/50000000000000000000 : ℝ)^1024 := by
      have hnat : (923 : ℕ)^4329*50000000000000000000^1024 ≤ 15390225163353783^1024*6250^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 15390225163353783 50000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (15390225163353783/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009460984078540251/50000000000000000000 : ℝ) ≤ (2500111888981317/2500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (50009460984078540251/50000000000000000000 : ℝ)^1024 ≤ (2500111888981317/2500000000000000 : ℝ)^4329 := by
      have hnat : (50009460984078540251 : ℕ)^1024*2500000000000000^4329 ≤ 2500111888981317^4329*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009460984078540251 50000000000000000000 2500111888981317 2500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111888981317/2500000000000000 : ℝ)) (X := (50009460984078540251/50000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040241434405247817/100000000000000000000 : ℝ) ≤ (2000190348350063/2000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (100040241434405247817/100000000000000000000 : ℝ)^1024 ≤ (2000190348350063/2000000000000000 : ℝ)^4329 := by
      have hnat : (100040241434405247817 : ℕ)^1024*2000000000000000^4329 ≤ 2000190348350063^4329*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040241434405247817 100000000000000000000 2000190348350063 2000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000190348350063/2000000000000000 : ℝ)) (X := (100040241434405247817/100000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015390225163353783/25000000000000000000 : ℝ) ≤ (5000727963787681/5000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (25015390225163353783/25000000000000000000 : ℝ)^1024 ≤ (5000727963787681/5000000000000000 : ℝ)^4329 := by
      have hnat : (25015390225163353783 : ℕ)^1024*5000000000000000^4329 ≤ 5000727963787681^4329*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015390225163353783 25000000000000000000 5000727963787681 5000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000727963787681/5000000000000000 : ℝ)) (X := (25015390225163353783/25000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9460984078540251/100000000000000000000 : ℝ) ≤ ((898758597075810339/899000000000000000 : ℝ)+2*(504185825047/359600000000000 : ℝ)*(2793/25000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (898758597075810339/899000000000000000 : ℝ)+2*(504185825047/359600000000000 : ℝ)*(2793/25000 : ℝ)=(2500111888981317/2500000000000000 : ℝ) by norm_num, show 1+2*(9460984078540251/100000000000000000000 : ℝ)=(50009460984078540251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15390225163353783/50000000000000000000 : ℝ)+(9460984078540251/100000000000000000000 : ℝ) ≤ ((898758597075810339/899000000000000000 : ℝ)+(504185825047/359600000000000 : ℝ)*((923/6250 : ℝ)+(2793/25000 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (898758597075810339/899000000000000000 : ℝ)+(504185825047/359600000000000 : ℝ)*((923/6250 : ℝ)+(2793/25000 : ℝ))=(2000190348350063/2000000000000000 : ℝ) by norm_num, show 1+(15390225163353783/50000000000000000000 : ℝ)+(9460984078540251/100000000000000000000 : ℝ)=(100040241434405247817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15390225163353783/50000000000000000000 : ℝ) ≤ ((898758597075810339/899000000000000000 : ℝ)+2*(504185825047/359600000000000 : ℝ)*(923/6250 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (898758597075810339/899000000000000000 : ℝ)+2*(504185825047/359600000000000 : ℝ)*(923/6250 : ℝ)=(5000727963787681/5000000000000000 : ℝ) by norm_num, show 1+2*(15390225163353783/50000000000000000000 : ℝ)=(25015390225163353783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (898758597075810339/899000000000000000 : ℝ)*(X 1 0+X 2 0)+(504185825047/359600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (898758597075810339/899000000000000000 : ℝ)) (alpha := (504185825047/359600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (898758597075810339/899000000000000000 : ℝ)*(X 0 1+X 2 1)+(504185825047/359600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (898758597075810339/899000000000000000 : ℝ)) (alpha := (504185825047/359600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (898758597075810339/899000000000000000 : ℝ)*(X 0 2+X 1 2)+(504185825047/359600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (898758597075810339/899000000000000000 : ℝ)) (alpha := (504185825047/359600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-201999059/1000000000 : ℝ)*X 0 0+(43292509/80000000 : ℝ)*X 0 1+(5245150619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348574417/10000000000 : ℝ)*X 1 0+(-105238147/500000000 : ℝ)*X 1 1+(5245150583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674287239/5000000000 : ℝ)*X 2 0+(5245150607/10000000000 : ℝ)*X 2 1+(-2104762827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319329903/10000000000 : ℝ)*X 0 0+(4146524799/10000000000 : ℝ)*X 0 1+(2249381963/5000000000 : ℝ)*X 0 2+(4319329903/10000000000 : ℝ)*X 1 0+(4146524799/10000000000 : ℝ)*X 1 1+(2249381963/5000000000 : ℝ)*X 1 2+(4319329903/10000000000 : ℝ)*X 2 0+(4146524799/10000000000 : ℝ)*X 2 1+(2249381963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-505000661/2500000000 : ℝ)*X 0 0+(2622874939/5000000000 : ℝ)*X 0 1+(5410961231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305575123/10000000000 : ℝ)*X 1 0+(-1938952281/10000000000 : ℝ)*X 1 1+(1082192247/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326393781/2500000000 : ℝ)*X 2 0+(338185077/625000000 : ℝ)*X 2 1+(-969476143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863871097/2000000000 : ℝ)*X 0 0+(1124373913/2500000000 : ℝ)*X 0 1+(1036949871/2500000000 : ℝ)*X 0 2+(863871097/2000000000 : ℝ)*X 1 0+(1124373913/2500000000 : ℝ)*X 1 1+(1036949871/2500000000 : ℝ)*X 1 2+(863871097/2000000000 : ℝ)*X 2 0+(1124373913/2500000000 : ℝ)*X 2 1+(1036949871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108718553313368042415702627/11237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1677819759/100000000000000 : ℝ)*(base19) + (833600791/50000000000000 : ℝ)*(base23) + (42335443/100000000000000 : ℝ)*(lower2) + (11599139/10000000000000 : ℝ)*(upper3) + (209585753/100000000000000 : ℝ)*(upper5) + (2212057935852081/50000000000000 : ℝ)*(major0) + (2212057935852081/50000000000000 : ℝ)*(major1) + (2212057935852081/50000000000000 : ℝ)*(major2) + (3004590084339709/50000000000000 : ℝ)*(sp0) + (3004609152281419/50000000000000 : ℝ)*(sp1) + (1201843663036203/20000000000000 : ℝ)*(sp2) + (2838996292693527/100000000000000 : ℝ)*(sp3) + (39813703179/100000000000000 : ℝ)*(sp4) + (15145844831/100000000000000 : ℝ)*(sp7) + (1419505719269179/50000000000000 : ℝ)*(f.failure) + (6009219982382597/100000000000000 : ℝ)*(f.sum) + (4966334266993/8990000000000000000000000000 : ℝ)*base66 + (45253388503667041/44950000000000000000000000000000 : ℝ)*base68 + (263306018303667041/44950000000000000000000000000000 : ℝ)*base70 + (164308770525417041/44950000000000000000000000000000 : ℝ)*base72 + (4528729340543/8990000000000000000000000000 : ℝ)*base74 + (31111021934482959/44950000000000000000000000000000 : ℝ)*base75 + (33208487119217041/44950000000000000000000000000000 : ℝ)*base78 + (559467620004017041/44950000000000000000000000000000 : ℝ)*base80 + (5258875888183/8990000000000000000000000000 : ℝ)*base82 + (12300809/5000000000000000000000 : ℝ)*base89 + (12300809/5000000000000000000000 : ℝ)*base91 + (12300809/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46287672250216789139001/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1598187311/100000000000000 : ℝ)*(base19) + (345552483/20000000000000 : ℝ)*(base23) + (11874383/6250000000000 : ℝ)*(upper3) + (14688951/25000000000000 : ℝ)*(lower4) + (190923267/100000000000000 : ℝ)*(upper5) + (445623835322653/10000000000000 : ℝ)*(major0) + (445623835322653/10000000000000 : ℝ)*(major1) + (445623835322653/10000000000000 : ℝ)*(major2) + (16459900477/50000000000000 : ℝ)*(sp1) + (35102568003/100000000000000 : ℝ)*(sp2) + (3026425777137319/50000000000000 : ℝ)*(sp4) + (6052817036286373/100000000000000 : ℝ)*(sp5) + (6052814723944221/100000000000000 : ℝ)*(sp6) + (1429812421796967/50000000000000 : ℝ)*(sp7) + (1429812421796967/50000000000000 : ℝ)*(f.failure) + (3026425777137319/50000000000000 : ℝ)*(f.sum) + (1409708173/2000000000000000000000000 : ℝ)*base65 + (81182197692833/10000000000000000000000000000 : ℝ)*base67 + (57548994672833/10000000000000000000000000000 : ℝ)*base69 + (21515317857167/10000000000000000000000000000 : ℝ)*base72 + (6026351619/2000000000000000000000000 : ℝ)*base73 + (155206520082833/10000000000000000000000000000 : ℝ)*base75 + (28313750732833/10000000000000000000000000000 : ℝ)*base77 + (93704541597167/10000000000000000000000000000 : ℝ)*base80 + (1147854329/2000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (26398957/5000000000000000000000 : ℝ)*base89 + (26398957/5000000000000000000000 : ℝ)*base91 + (26398957/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1370_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1370_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1370_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1370_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1370_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1370_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
