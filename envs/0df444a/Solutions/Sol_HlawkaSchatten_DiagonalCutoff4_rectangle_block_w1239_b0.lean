-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:04.573209+00:00
-- url     : https://prove2.me/submissions/81bdf819-942e-45c8-9cb8-31c22477b193

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
theorem support_rectangle_w1239_s0_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-465371531/2500000000 : ℝ)*x 0 + (6032181677/10000000000 : ℝ)*x 1 + (4792616203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465371531/2500000000 : ℝ)^527 ≤ (67843677573/625000000000 : ℝ)^399 := by
    have hnat : (465371531 : ℕ)^527*625000000000^399 ≤ 67843677573^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465371531 2500000000 67843677573 625000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6032181677/10000000000 : ℝ)^527 ≤ (51292062725719/100000000000000 : ℝ)^399 := by
    have hnat : (6032181677 : ℕ)^527*100000000000000^399 ≤ 51292062725719^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032181677 10000000000 51292062725719 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4792616203/10000000000 : ℝ)^527 ≤ (9463237212461/25000000000000 : ℝ)^399 := by
    have hnat : (4792616203 : ℕ)^527*25000000000000^399 ≤ 9463237212461^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792616203 10000000000 9463237212461 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-465371531/2500000000 : ℝ), (6032181677/10000000000 : ℝ), (4792616203/10000000000 : ℝ)] ![(67843677573/625000000000 : ℝ), (51292062725719/100000000000000 : ℝ), (9463237212461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-465371531/2500000000 : ℝ)|^527 ≤ (67843677573/625000000000 : ℝ)^399
        have hw : |(-465371531/2500000000 : ℝ)|=(465371531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6032181677/10000000000 : ℝ)|^527 ≤ (51292062725719/100000000000000 : ℝ)^399
        have hw : |(6032181677/10000000000 : ℝ)|=(6032181677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4792616203/10000000000 : ℝ)|^527 ≤ (9463237212461/25000000000000 : ℝ)^399
        have hw : |(4792616203/10000000000 : ℝ)|=(4792616203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s0_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5511328501/10000000000 : ℝ)*x 0 + (-257019637/1000000000 : ℝ)*x 1 + (4792616153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511328501/10000000000 : ℝ)^527 ≤ (45525088562717/100000000000000 : ℝ)^399 := by
    have hnat : (5511328501 : ℕ)^527*100000000000000^399 ≤ 45525088562717^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511328501 10000000000 45525088562717 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257019637/1000000000 : ℝ)^527 ≤ (16621963096919/100000000000000 : ℝ)^399 := by
    have hnat : (257019637 : ℕ)^527*100000000000000^399 ≤ 16621963096919^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257019637 1000000000 16621963096919 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4792616153/10000000000 : ℝ)^527 ≤ (37852948328247/100000000000000 : ℝ)^399 := by
    have hnat : (4792616153 : ℕ)^527*100000000000000^399 ≤ 37852948328247^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792616153 10000000000 37852948328247 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511328501/10000000000 : ℝ), (-257019637/1000000000 : ℝ), (4792616153/10000000000 : ℝ)] ![(45525088562717/100000000000000 : ℝ), (16621963096919/100000000000000 : ℝ), (37852948328247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511328501/10000000000 : ℝ)|^527 ≤ (45525088562717/100000000000000 : ℝ)^399
        have hw : |(5511328501/10000000000 : ℝ)|=(5511328501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257019637/1000000000 : ℝ)|^527 ≤ (16621963096919/100000000000000 : ℝ)^399
        have hw : |(-257019637/1000000000 : ℝ)|=(257019637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4792616153/10000000000 : ℝ)|^527 ≤ (37852948328247/100000000000000 : ℝ)^399
        have hw : |(4792616153/10000000000 : ℝ)|=(4792616153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s0_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (551132843/1000000000 : ℝ)*x 0 + (191704649/400000000 : ℝ)*x 1 + (-2570196373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551132843/1000000000 : ℝ)^527 ≤ (45525087788093/100000000000000 : ℝ)^399 := by
    have hnat : (551132843 : ℕ)^527*100000000000000^399 ≤ 45525087788093^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551132843 1000000000 45525087788093 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191704649/400000000 : ℝ)^527 ≤ (18926474539673/50000000000000 : ℝ)^399 := by
    have hnat : (191704649 : ℕ)^527*50000000000000^399 ≤ 18926474539673^399*400000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191704649 400000000 18926474539673 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570196373/10000000000 : ℝ)^527 ≤ (3324392624509/20000000000000 : ℝ)^399 := by
    have hnat : (2570196373 : ℕ)^527*20000000000000^399 ≤ 3324392624509^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570196373 10000000000 3324392624509 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551132843/1000000000 : ℝ), (191704649/400000000 : ℝ), (-2570196373/10000000000 : ℝ)] ![(45525087788093/100000000000000 : ℝ), (18926474539673/50000000000000 : ℝ), (3324392624509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551132843/1000000000 : ℝ)|^527 ≤ (45525087788093/100000000000000 : ℝ)^399
        have hw : |(551132843/1000000000 : ℝ)|=(551132843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191704649/400000000 : ℝ)|^527 ≤ (18926474539673/50000000000000 : ℝ)^399
        have hw : |(191704649/400000000 : ℝ)|=(191704649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2570196373/10000000000 : ℝ)|^527 ≤ (3324392624509/20000000000000 : ℝ)^399
        have hw : |(-2570196373/10000000000 : ℝ)|=(2570196373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s0_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4193257261/10000000000 : ℝ)*x 0 + (779250959/2500000000 : ℝ)*x 1 + (5630093199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193257261/10000000000 : ℝ)^527 ≤ (7932412371861/25000000000000 : ℝ)^399 := by
    have hnat : (4193257261 : ℕ)^527*25000000000000^399 ≤ 7932412371861^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193257261 10000000000 7932412371861 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779250959/2500000000 : ℝ)^527 ≤ (21445059686441/100000000000000 : ℝ)^399 := by
    have hnat : (779250959 : ℕ)^527*100000000000000^399 ≤ 21445059686441^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779250959 2500000000 21445059686441 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5630093199/10000000000 : ℝ)^527 ≤ (23412645405307/50000000000000 : ℝ)^399 := by
    have hnat : (5630093199 : ℕ)^527*50000000000000^399 ≤ 23412645405307^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630093199 10000000000 23412645405307 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193257261/10000000000 : ℝ), (779250959/2500000000 : ℝ), (5630093199/10000000000 : ℝ)] ![(7932412371861/25000000000000 : ℝ), (21445059686441/100000000000000 : ℝ), (23412645405307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193257261/10000000000 : ℝ)|^527 ≤ (7932412371861/25000000000000 : ℝ)^399
        have hw : |(4193257261/10000000000 : ℝ)|=(4193257261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779250959/2500000000 : ℝ)|^527 ≤ (21445059686441/100000000000000 : ℝ)^399
        have hw : |(779250959/2500000000 : ℝ)|=(779250959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5630093199/10000000000 : ℝ)|^527 ≤ (23412645405307/50000000000000 : ℝ)^399
        have hw : |(5630093199/10000000000 : ℝ)|=(5630093199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s0_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-933176081/5000000000 : ℝ)*x 0 + (2412269837/5000000000 : ℝ)*x 1 + (187472811/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933176081/5000000000 : ℝ)^527 ≤ (2723120666689/25000000000000 : ℝ)^399 := by
    have hnat : (933176081 : ℕ)^527*25000000000000^399 ≤ 2723120666689^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933176081 5000000000 2723120666689 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2412269837/5000000000 : ℝ)^527 ≤ (38186327633821/100000000000000 : ℝ)^399 := by
    have hnat : (2412269837 : ℕ)^527*100000000000000^399 ≤ 38186327633821^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412269837 5000000000 38186327633821 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187472811/312500000 : ℝ)^527 ≤ (25460594840947/50000000000000 : ℝ)^399 := by
    have hnat : (187472811 : ℕ)^527*50000000000000^399 ≤ 25460594840947^399*312500000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187472811 312500000 25460594840947 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933176081/5000000000 : ℝ), (2412269837/5000000000 : ℝ), (187472811/312500000 : ℝ)] ![(2723120666689/25000000000000 : ℝ), (38186327633821/100000000000000 : ℝ), (25460594840947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933176081/5000000000 : ℝ)|^527 ≤ (2723120666689/25000000000000 : ℝ)^399
        have hw : |(-933176081/5000000000 : ℝ)|=(933176081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2412269837/5000000000 : ℝ)|^527 ≤ (38186327633821/100000000000000 : ℝ)^399
        have hw : |(2412269837/5000000000 : ℝ)|=(2412269837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187472811/312500000 : ℝ)|^527 ≤ (25460594840947/50000000000000 : ℝ)^399
        have hw : |(187472811/312500000 : ℝ)|=(187472811/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s0_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5174072907/10000000000 : ℝ)*x 0 + (-1363680421/10000000000 : ℝ)*x 1 + (5999132201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174072907/10000000000 : ℝ)^527 ≤ (10470549131829/25000000000000 : ℝ)^399 := by
    have hnat : (5174072907 : ℕ)^527*25000000000000^399 ≤ 10470549131829^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174072907 10000000000 10470549131829 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363680421/10000000000 : ℝ)^527 ≤ (7196588558139/100000000000000 : ℝ)^399 := by
    have hnat : (1363680421 : ℕ)^527*100000000000000^399 ≤ 7196588558139^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363680421 10000000000 7196588558139 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5999132201/10000000000 : ℝ)^527 ≤ (25460607447823/50000000000000 : ℝ)^399 := by
    have hnat : (5999132201 : ℕ)^527*50000000000000^399 ≤ 25460607447823^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5999132201 10000000000 25460607447823 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174072907/10000000000 : ℝ), (-1363680421/10000000000 : ℝ), (5999132201/10000000000 : ℝ)] ![(10470549131829/25000000000000 : ℝ), (7196588558139/100000000000000 : ℝ), (25460607447823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174072907/10000000000 : ℝ)|^527 ≤ (10470549131829/25000000000000 : ℝ)^399
        have hw : |(5174072907/10000000000 : ℝ)|=(5174072907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1363680421/10000000000 : ℝ)|^527 ≤ (7196588558139/100000000000000 : ℝ)^399
        have hw : |(-1363680421/10000000000 : ℝ)|=(1363680421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5999132201/10000000000 : ℝ)|^527 ≤ (25460607447823/50000000000000 : ℝ)^399
        have hw : |(5999132201/10000000000 : ℝ)|=(5999132201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s0_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5174073783/10000000000 : ℝ)*x 0 + (299956521/500000000 : ℝ)*x 1 + (-681840971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174073783/10000000000 : ℝ)^527 ≤ (41882205892983/100000000000000 : ℝ)^399 := by
    have hnat : (5174073783 : ℕ)^527*100000000000000^399 ≤ 41882205892983^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174073783 10000000000 41882205892983 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299956521/500000000 : ℝ)^527 ≤ (25460597464343/50000000000000 : ℝ)^399 := by
    have hnat : (299956521 : ℕ)^527*50000000000000^399 ≤ 25460597464343^399*500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299956521 500000000 25460597464343 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681840971/5000000000 : ℝ)^527 ≤ (287863966399/4000000000000 : ℝ)^399 := by
    have hnat : (681840971 : ℕ)^527*4000000000000^399 ≤ 287863966399^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681840971 5000000000 287863966399 4000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174073783/10000000000 : ℝ), (299956521/500000000 : ℝ), (-681840971/5000000000 : ℝ)] ![(41882205892983/100000000000000 : ℝ), (25460597464343/50000000000000 : ℝ), (287863966399/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174073783/10000000000 : ℝ)|^527 ≤ (41882205892983/100000000000000 : ℝ)^399
        have hw : |(5174073783/10000000000 : ℝ)|=(5174073783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299956521/500000000 : ℝ)|^527 ≤ (25460597464343/50000000000000 : ℝ)^399
        have hw : |(299956521/500000000 : ℝ)|=(299956521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-681840971/5000000000 : ℝ)|^527 ≤ (287863966399/4000000000000 : ℝ)^399
        have hw : |(-681840971/5000000000 : ℝ)|=(681840971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s0_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2101561713/5000000000 : ℝ)*x 0 + (5565376833/10000000000 : ℝ)*x 1 + (318400699/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101561713/5000000000 : ℝ)^527 ≤ (7957072972759/25000000000000 : ℝ)^399 := by
    have hnat : (2101561713 : ℕ)^527*25000000000000^399 ≤ 7957072972759^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101561713 5000000000 7957072972759 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5565376833/10000000000 : ℝ)^527 ≤ (9223138305791/20000000000000 : ℝ)^399 := by
    have hnat : (5565376833 : ℕ)^527*20000000000000^399 ≤ 9223138305791^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5565376833 10000000000 9223138305791 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318400699/1000000000 : ℝ)^527 ≤ (4411203311853/20000000000000 : ℝ)^399 := by
    have hnat : (318400699 : ℕ)^527*20000000000000^399 ≤ 4411203311853^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318400699 1000000000 4411203311853 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101561713/5000000000 : ℝ), (5565376833/10000000000 : ℝ), (318400699/1000000000 : ℝ)] ![(7957072972759/25000000000000 : ℝ), (9223138305791/20000000000000 : ℝ), (4411203311853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101561713/5000000000 : ℝ)|^527 ≤ (7957072972759/25000000000000 : ℝ)^399
        have hw : |(2101561713/5000000000 : ℝ)|=(2101561713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5565376833/10000000000 : ℝ)|^527 ≤ (9223138305791/20000000000000 : ℝ)^399
        have hw : |(5565376833/10000000000 : ℝ)|=(5565376833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318400699/1000000000 : ℝ)|^527 ≤ (4411203311853/20000000000000 : ℝ)^399
        have hw : |(318400699/1000000000 : ℝ)|=(318400699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (403/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27447/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8431/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8431 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8431*1^2048 ≤ 0^2048*1^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8431/2048 : ℝ) ≤ (2300385795249674903/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8431 ≤ (2300385795249674903/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8431*100000000000000000000^2048 ≤ 2300385795249674903^2048*5^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2300385795249674903 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2300385795249674903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8431 := by
      have hnat : (1 : ℕ)^2048*1^8431 ≤ 1^8431*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102300385795249674903/100000000000000000000 : ℝ) ≤ (10055399233492273/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (102300385795249674903/100000000000000000000 : ℝ)^2048 ≤ (10055399233492273/10000000000000000 : ℝ)^8431 := by
      have hnat : (102300385795249674903 : ℕ)^2048*10000000000000000^8431 ≤ 10055399233492273^8431*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102300385795249674903 100000000000000000000 10055399233492273 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055399233492273/10000000000000000 : ℝ)) (X := (102300385795249674903/100000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52300385795249674903/50000000000000000000 : ℝ) ≤ (5055399233492273/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (52300385795249674903/50000000000000000000 : ℝ)^2048 ≤ (5055399233492273/5000000000000000 : ℝ)^8431 := by
      have hnat : (52300385795249674903 : ℕ)^2048*5000000000000000^8431 ≤ 5055399233492273^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52300385795249674903 50000000000000000000 5055399233492273 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055399233492273/5000000000000000 : ℝ)) (X := (52300385795249674903/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55399233492273/4000000000000000 : ℝ)*(0 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55399233492273/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2300385795249674903/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55399233492273/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55399233492273/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055399233492273/10000000000000000 : ℝ) by norm_num, show 1+(2300385795249674903/100000000000000000000 : ℝ)+(0 : ℝ)=(102300385795249674903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2300385795249674903/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55399233492273/4000000000000000 : ℝ)*(2/5 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55399233492273/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055399233492273/5000000000000000 : ℝ) by norm_num, show 1+2*(2300385795249674903/100000000000000000000 : ℝ)=(52300385795249674903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55399233492273/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55399233492273/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55399233492273/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55399233492273/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55399233492273/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55399233492273/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-465371531/2500000000 : ℝ)*X 0 0+(6032181677/10000000000 : ℝ)*X 0 1+(4792616203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5511328501/10000000000 : ℝ)*X 1 0+(-257019637/1000000000 : ℝ)*X 1 1+(4792616153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((551132843/1000000000 : ℝ)*X 2 0+(191704649/400000000 : ℝ)*X 2 1+(-2570196373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193257261/10000000000 : ℝ)*X 0 0+(779250959/2500000000 : ℝ)*X 0 1+(5630093199/10000000000 : ℝ)*X 0 2+(4193257261/10000000000 : ℝ)*X 1 0+(779250959/2500000000 : ℝ)*X 1 1+(5630093199/10000000000 : ℝ)*X 1 2+(4193257261/10000000000 : ℝ)*X 2 0+(779250959/2500000000 : ℝ)*X 2 1+(5630093199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-933176081/5000000000 : ℝ)*X 0 0+(2412269837/5000000000 : ℝ)*X 0 1+(187472811/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174072907/10000000000 : ℝ)*X 1 0+(-1363680421/10000000000 : ℝ)*X 1 1+(5999132201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174073783/10000000000 : ℝ)*X 2 0+(299956521/500000000 : ℝ)*X 2 1+(-681840971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2101561713/5000000000 : ℝ)*X 0 0+(5565376833/10000000000 : ℝ)*X 0 1+(318400699/1000000000 : ℝ)*X 0 2+(2101561713/5000000000 : ℝ)*X 1 0+(5565376833/10000000000 : ℝ)*X 1 1+(318400699/1000000000 : ℝ)*X 1 2+(2101561713/5000000000 : ℝ)*X 2 0+(5565376833/10000000000 : ℝ)*X 2 1+(318400699/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (576984499099705613163411/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14146069/20000000000000 : ℝ)*(base1) + (1406864173/100000000000000 : ℝ)*(base19) + (325686703/25000000000000 : ℝ)*(base23) + (46862239/50000000000000 : ℝ)*(base24) + (316609321/100000000000000 : ℝ)*(upper3) + (602331443300277/100000000000000 : ℝ)*(major0) + (602331443300277/100000000000000 : ℝ)*(major1) + (602331443300277/100000000000000 : ℝ)*(major2) + (806739082705671/100000000000000 : ℝ)*(sp0) + (806740738658581/100000000000000 : ℝ)*(sp1) + (161348149810293/20000000000000 : ℝ)*(sp2) + (39791804254151/10000000000000 : ℝ)*(sp3) + (783386857/25000000000000 : ℝ)*(sp4) + (2435477769/100000000000000 : ℝ)*(sp7) + (49740068593703/12500000000000 : ℝ)*(f.failure) + (161348429104551/20000000000000 : ℝ)*(f.sum) + (607560865459621/200000000000000000000000000000 : ℝ)*base65 + (1970992627859621/400000000000000000000000000000 : ℝ)*base67 + (3499576710659621/400000000000000000000000000000 : ℝ)*base69 + (2616660184259621/400000000000000000000000000000 : ℝ)*base71 + (404513904859621/200000000000000000000000000000 : ℝ)*base73 + (3655293421059621/400000000000000000000000000000 : ℝ)*base75 + (771007036659621/400000000000000000000000000000 : ℝ)*base77 + (1338124273459621/400000000000000000000000000000 : ℝ)*base79 + (1825383427259621/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (273717/78125000000000000000 : ℝ)*base90 + (273717/78125000000000000000 : ℝ)*base92 + (273717/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (179447808447837970064421/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82257587/100000000000000 : ℝ)*(base1) + (29783991/6250000000000 : ℝ)*(base19) + (289321321/50000000000000 : ℝ)*(base23) + (117852219/100000000000000 : ℝ)*(upper3) + (317821964731347/50000000000000 : ℝ)*(major0) + (317821964731347/50000000000000 : ℝ)*(major1) + (317821964731347/50000000000000 : ℝ)*(major2) + (89070561/5000000000000 : ℝ)*(sp1) + (284107797/25000000000000 : ℝ)*(sp2) + (541995821/100000000000000 : ℝ)*(sp3) + (851359976167061/100000000000000 : ℝ)*(sp4) + (425678817977199/50000000000000 : ℝ)*(sp5) + (212839544708911/25000000000000 : ℝ)*(sp6) + (419927280946567/100000000000000 : ℝ)*(sp7) + (16797116207999/4000000000000 : ℝ)*(f.failure) + (425679946954737/50000000000000 : ℝ)*(f.sum) + (18766151281731/100000000000000000000000000000 : ℝ)*base65 + (108475089181731/200000000000000000000000000000 : ℝ)*base67 + (718113889181731/200000000000000000000000000000 : ℝ)*base69 + (923228839581731/200000000000000000000000000000 : ℝ)*base71 + (165392825518269/100000000000000000000000000000 : ℝ)*base74 + (574934771981731/200000000000000000000000000000 : ℝ)*base75 + (1386644862381731/200000000000000000000000000000 : ℝ)*base77 + (303332444018269/200000000000000000000000000000 : ℝ)*base80 + (149640751681731/100000000000000000000000000000 : ℝ)*base81 + (127389/25000000000000000000 : ℝ)*base89 + (127389/25000000000000000000 : ℝ)*base91 + (127389/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1239_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (403/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27447/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1239_s1_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059119337/10000000000 : ℝ)*x 0 + (5676350441/10000000000 : ℝ)*x 1 + (1255484963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059119337/10000000000 : ℝ)^527 ≤ (3100624542511/25000000000000 : ℝ)^399 := by
    have hnat : (2059119337 : ℕ)^527*25000000000000^399 ≤ 3100624542511^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059119337 10000000000 3100624542511 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5676350441/10000000000 : ℝ)^527 ≤ (47334098023693/100000000000000 : ℝ)^399 := by
    have hnat : (5676350441 : ℕ)^527*100000000000000^399 ≤ 47334098023693^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676350441 10000000000 47334098023693 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255484963/2500000000 : ℝ)^527 ≤ (40263403786791/100000000000000 : ℝ)^399 := by
    have hnat : (1255484963 : ℕ)^527*100000000000000^399 ≤ 40263403786791^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255484963 2500000000 40263403786791 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059119337/10000000000 : ℝ), (5676350441/10000000000 : ℝ), (1255484963/2500000000 : ℝ)] ![(3100624542511/25000000000000 : ℝ), (47334098023693/100000000000000 : ℝ), (40263403786791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059119337/10000000000 : ℝ)|^527 ≤ (3100624542511/25000000000000 : ℝ)^399
        have hw : |(-2059119337/10000000000 : ℝ)|=(2059119337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5676350441/10000000000 : ℝ)|^527 ≤ (47334098023693/100000000000000 : ℝ)^399
        have hw : |(5676350441/10000000000 : ℝ)|=(5676350441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255484963/2500000000 : ℝ)|^527 ≤ (40263403786791/100000000000000 : ℝ)^399
        have hw : |(1255484963/2500000000 : ℝ)|=(1255484963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s1_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5413818829/10000000000 : ℝ)*x 0 + (-482116199/2000000000 : ℝ)*x 1 + (2510969963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413818829/10000000000 : ℝ)^527 ≤ (44464271031847/100000000000000 : ℝ)^399 := by
    have hnat : (5413818829 : ℕ)^527*100000000000000^399 ≤ 44464271031847^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413818829 10000000000 44464271031847 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482116199/2000000000 : ℝ)^527 ≤ (3054464876413/20000000000000 : ℝ)^399 := by
    have hnat : (482116199 : ℕ)^527*20000000000000^399 ≤ 3054464876413^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482116199 2000000000 3054464876413 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510969963/5000000000 : ℝ)^527 ≤ (40263404570417/100000000000000 : ℝ)^399 := by
    have hnat : (2510969963 : ℕ)^527*100000000000000^399 ≤ 40263404570417^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510969963 5000000000 40263404570417 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413818829/10000000000 : ℝ), (-482116199/2000000000 : ℝ), (2510969963/5000000000 : ℝ)] ![(44464271031847/100000000000000 : ℝ), (3054464876413/20000000000000 : ℝ), (40263404570417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413818829/10000000000 : ℝ)|^527 ≤ (44464271031847/100000000000000 : ℝ)^399
        have hw : |(5413818829/10000000000 : ℝ)|=(5413818829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482116199/2000000000 : ℝ)|^527 ≤ (3054464876413/20000000000000 : ℝ)^399
        have hw : |(-482116199/2000000000 : ℝ)|=(482116199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510969963/5000000000 : ℝ)|^527 ≤ (40263404570417/100000000000000 : ℝ)^399
        have hw : |(2510969963/5000000000 : ℝ)|=(2510969963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s1_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2706909447/5000000000 : ℝ)*x 0 + (2510969943/5000000000 : ℝ)*x 1 + (-1205290481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706909447/5000000000 : ℝ)^527 ≤ (69475424589/156250000000 : ℝ)^399 := by
    have hnat : (2706909447 : ℕ)^527*156250000000^399 ≤ 69475424589^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706909447 5000000000 69475424589 156250000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510969943/5000000000 : ℝ)^527 ≤ (10065851036709/25000000000000 : ℝ)^399 := by
    have hnat : (2510969943 : ℕ)^527*25000000000000^399 ≤ 10065851036709^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510969943 5000000000 10065851036709 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205290481/5000000000 : ℝ)^527 ≤ (7636162052961/50000000000000 : ℝ)^399 := by
    have hnat : (1205290481 : ℕ)^527*50000000000000^399 ≤ 7636162052961^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205290481 5000000000 7636162052961 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706909447/5000000000 : ℝ), (2510969943/5000000000 : ℝ), (-1205290481/5000000000 : ℝ)] ![(69475424589/156250000000 : ℝ), (10065851036709/25000000000000 : ℝ), (7636162052961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706909447/5000000000 : ℝ)|^527 ≤ (69475424589/156250000000 : ℝ)^399
        have hw : |(2706909447/5000000000 : ℝ)|=(2706909447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510969943/5000000000 : ℝ)|^527 ≤ (10065851036709/25000000000000 : ℝ)^399
        have hw : |(2510969943/5000000000 : ℝ)|=(2510969943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1205290481/5000000000 : ℝ)|^527 ≤ (7636162052961/50000000000000 : ℝ)^399
        have hw : |(-1205290481/5000000000 : ℝ)|=(1205290481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s1_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2154558947/5000000000 : ℝ)*x 0 + (1847460189/5000000000 : ℝ)*x 1 + (200866791/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154558947/5000000000 : ℝ)^527 ≤ (32892693197417/100000000000000 : ℝ)^399 := by
    have hnat : (2154558947 : ℕ)^527*100000000000000^399 ≤ 32892693197417^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154558947 5000000000 32892693197417 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847460189/5000000000 : ℝ)^527 ≤ (5369352591799/20000000000000 : ℝ)^399 := by
    have hnat : (1847460189 : ℕ)^527*20000000000000^399 ≤ 5369352591799^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847460189 5000000000 5369352591799 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200866791/400000000 : ℝ)^527 ≤ (10065135955719/25000000000000 : ℝ)^399 := by
    have hnat : (200866791 : ℕ)^527*25000000000000^399 ≤ 10065135955719^399*400000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200866791 400000000 10065135955719 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154558947/5000000000 : ℝ), (1847460189/5000000000 : ℝ), (200866791/400000000 : ℝ)] ![(32892693197417/100000000000000 : ℝ), (5369352591799/20000000000000 : ℝ), (10065135955719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154558947/5000000000 : ℝ)|^527 ≤ (32892693197417/100000000000000 : ℝ)^399
        have hw : |(2154558947/5000000000 : ℝ)|=(2154558947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1847460189/5000000000 : ℝ)|^527 ≤ (5369352591799/20000000000000 : ℝ)^399
        have hw : |(1847460189/5000000000 : ℝ)|=(1847460189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200866791/400000000 : ℝ)|^527 ≤ (10065135955719/25000000000000 : ℝ)^399
        have hw : |(200866791/400000000 : ℝ)|=(200866791/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s1_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-257474979/1250000000 : ℝ)*x 0 + (628818287/1250000000 : ℝ)*x 1 + (2833789817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257474979/1250000000 : ℝ)^527 ≤ (3101978027179/25000000000000 : ℝ)^399 := by
    have hnat : (257474979 : ℕ)^527*25000000000000^399 ≤ 3101978027179^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257474979 1250000000 3101978027179 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628818287/1250000000 : ℝ)^527 ≤ (20177283514987/50000000000000 : ℝ)^399 := by
    have hnat : (628818287 : ℕ)^527*50000000000000^399 ≤ 20177283514987^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628818287 1250000000 20177283514987 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2833789817/5000000000 : ℝ)^527 ≤ (2952345053119/6250000000000 : ℝ)^399 := by
    have hnat : (2833789817 : ℕ)^527*6250000000000^399 ≤ 2952345053119^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833789817 5000000000 2952345053119 6250000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257474979/1250000000 : ℝ), (628818287/1250000000 : ℝ), (2833789817/5000000000 : ℝ)] ![(3101978027179/25000000000000 : ℝ), (20177283514987/50000000000000 : ℝ), (2952345053119/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257474979/1250000000 : ℝ)|^527 ≤ (3101978027179/25000000000000 : ℝ)^399
        have hw : |(-257474979/1250000000 : ℝ)|=(257474979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(628818287/1250000000 : ℝ)|^527 ≤ (20177283514987/50000000000000 : ℝ)^399
        have hw : |(628818287/1250000000 : ℝ)|=(628818287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2833789817/5000000000 : ℝ)|^527 ≤ (2952345053119/6250000000000 : ℝ)^399
        have hw : |(2833789817/5000000000 : ℝ)|=(2833789817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s1_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2622623797/5000000000 : ℝ)*x 0 + (-1764940769/10000000000 : ℝ)*x 1 + (2833789891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622623797/5000000000 : ℝ)^527 ≤ (42644827497359/100000000000000 : ℝ)^399 := by
    have hnat : (2622623797 : ℕ)^527*100000000000000^399 ≤ 42644827497359^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622623797 5000000000 42644827497359 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1764940769/10000000000 : ℝ)^527 ≤ (10117650009529/100000000000000 : ℝ)^399 := by
    have hnat : (1764940769 : ℕ)^527*100000000000000^399 ≤ 10117650009529^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764940769 10000000000 10117650009529 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2833789891/5000000000 : ℝ)^527 ≤ (47237522479159/100000000000000 : ℝ)^399 := by
    have hnat : (2833789891 : ℕ)^527*100000000000000^399 ≤ 47237522479159^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833789891 5000000000 47237522479159 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622623797/5000000000 : ℝ), (-1764940769/10000000000 : ℝ), (2833789891/5000000000 : ℝ)] ![(42644827497359/100000000000000 : ℝ), (10117650009529/100000000000000 : ℝ), (47237522479159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622623797/5000000000 : ℝ)|^527 ≤ (42644827497359/100000000000000 : ℝ)^399
        have hw : |(2622623797/5000000000 : ℝ)|=(2622623797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1764940769/10000000000 : ℝ)|^527 ≤ (10117650009529/100000000000000 : ℝ)^399
        have hw : |(-1764940769/10000000000 : ℝ)|=(1764940769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2833789891/5000000000 : ℝ)|^527 ≤ (47237522479159/100000000000000 : ℝ)^399
        have hw : |(2833789891/5000000000 : ℝ)|=(2833789891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s1_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (327827997/625000000 : ℝ)*x 0 + (113351611/200000000 : ℝ)*x 1 + (-352987829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327827997/625000000 : ℝ)^527 ≤ (42644831341693/100000000000000 : ℝ)^399 := by
    have hnat : (327827997 : ℕ)^527*100000000000000^399 ≤ 42644831341693^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327827997 625000000 42644831341693 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113351611/200000000 : ℝ)^527 ≤ (11809382733417/25000000000000 : ℝ)^399 := by
    have hnat : (113351611 : ℕ)^527*25000000000000^399 ≤ 11809382733417^399*200000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113351611 200000000 11809382733417 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352987829/2000000000 : ℝ)^527 ≤ (2023527542653/20000000000000 : ℝ)^399 := by
    have hnat : (352987829 : ℕ)^527*20000000000000^399 ≤ 2023527542653^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352987829 2000000000 2023527542653 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327827997/625000000 : ℝ), (113351611/200000000 : ℝ), (-352987829/2000000000 : ℝ)] ![(42644831341693/100000000000000 : ℝ), (11809382733417/25000000000000 : ℝ), (2023527542653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327827997/625000000 : ℝ)|^527 ≤ (42644831341693/100000000000000 : ℝ)^399
        have hw : |(327827997/625000000 : ℝ)|=(327827997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113351611/200000000 : ℝ)|^527 ≤ (11809382733417/25000000000000 : ℝ)^399
        have hw : |(113351611/200000000 : ℝ)|=(113351611/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352987829/2000000000 : ℝ)|^527 ≤ (2023527542653/20000000000000 : ℝ)^399
        have hw : |(-352987829/2000000000 : ℝ)|=(352987829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s1_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4310495899/10000000000 : ℝ)*x 0 + (1251055469/2500000000 : ℝ)*x 1 + (1856350349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310495899/10000000000 : ℝ)^527 ≤ (6581317404619/20000000000000 : ℝ)^399 := by
    have hnat : (4310495899 : ℕ)^527*20000000000000^399 ≤ 6581317404619^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310495899 10000000000 6581317404619 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251055469/2500000000 : ℝ)^527 ≤ (40075885006691/100000000000000 : ℝ)^399 := by
    have hnat : (1251055469 : ℕ)^527*100000000000000^399 ≤ 40075885006691^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251055469 2500000000 40075885006691 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856350349/5000000000 : ℝ)^527 ≤ (2701752795797/10000000000000 : ℝ)^399 := by
    have hnat : (1856350349 : ℕ)^527*10000000000000^399 ≤ 2701752795797^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856350349 5000000000 2701752795797 10000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310495899/10000000000 : ℝ), (1251055469/2500000000 : ℝ), (1856350349/5000000000 : ℝ)] ![(6581317404619/20000000000000 : ℝ), (40075885006691/100000000000000 : ℝ), (2701752795797/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310495899/10000000000 : ℝ)|^527 ≤ (6581317404619/20000000000000 : ℝ)^399
        have hw : |(4310495899/10000000000 : ℝ)|=(4310495899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251055469/2500000000 : ℝ)|^527 ≤ (40075885006691/100000000000000 : ℝ)^399
        have hw : |(1251055469/2500000000 : ℝ)|=(1251055469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1856350349/5000000000 : ℝ)|^527 ≤ (2701752795797/10000000000000 : ℝ)^399
        have hw : |(1856350349/5000000000 : ℝ)|=(1856350349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27447/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (403/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (247/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27447/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (403/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27447/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (403/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27447/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (403/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27447/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (403/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27447/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (403/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27447/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (403/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (403/50000 : ℝ) ^ (8431/2048 : ℝ) ≤ (240442426577/100000000000000000000 : ℝ) := by
    have hpowers : (403/50000 : ℝ)^8431 ≤ (240442426577/100000000000000000000 : ℝ)^2048 := by
      have hnat : (403 : ℕ)^8431*100000000000000000000^2048 ≤ 240442426577^2048*50000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        403 50000 240442426577 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (403/50000 : ℝ)) (X := (240442426577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27447/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (244018259450964529/50000000000000000000 : ℝ) := by
    have hpowers : (27447/100000 : ℝ)^8431 ≤ (244018259450964529/50000000000000000000 : ℝ)^2048 := by
      have hnat : (27447 : ℕ)^8431*50000000000000000000^2048 ≤ 244018259450964529^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27447 100000 244018259450964529 50000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27447/100000 : ℝ)) (X := (244018259450964529/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000240442426577/50000000000000000000 : ℝ) ≤ (5000000005840661/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50000000240442426577/50000000000000000000 : ℝ)^2048 ≤ (5000000005840661/5000000000000000 : ℝ)^8431 := by
      have hnat : (50000000240442426577 : ℕ)^2048*5000000000000000^8431 ≤ 5000000005840661^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000240442426577 50000000000000000000 5000000005840661 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000005840661/5000000000000000 : ℝ)) (X := (50000000240442426577/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20097607351868871127/20000000000000000000 : ℝ) ≤ (10011833211211873/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (20097607351868871127/20000000000000000000 : ℝ)^2048 ≤ (10011833211211873/10000000000000000 : ℝ)^8431 := by
      have hnat : (20097607351868871127 : ℕ)^2048*10000000000000000^8431 ≤ 10011833211211873^8431*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20097607351868871127 20000000000000000000 10011833211211873 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011833211211873/10000000000000000 : ℝ)) (X := (20097607351868871127/20000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25244018259450964529/25000000000000000000 : ℝ) ≤ (1252958301342803/1250000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (25244018259450964529/25000000000000000000 : ℝ)^2048 ≤ (1252958301342803/1250000000000000 : ℝ)^8431 := by
      have hnat : (25244018259450964529 : ℕ)^2048*1250000000000000^8431 ≤ 1252958301342803^8431*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25244018259450964529 25000000000000000000 1252958301342803 1250000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252958301342803/1250000000000000 : ℝ)) (X := (25244018259450964529/25000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(240442426577/100000000000000000000 : ℝ) ≤ ((26639092519355885119/26641000000000000000 : ℝ)+2*(11833199530551/2664100000000000 : ℝ)*(403/50000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (26639092519355885119/26641000000000000000 : ℝ)+2*(11833199530551/2664100000000000 : ℝ)*(403/50000 : ℝ)=(5000000005840661/5000000000000000 : ℝ) by norm_num, show 1+2*(240442426577/100000000000000000000 : ℝ)=(50000000240442426577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(244018259450964529/50000000000000000000 : ℝ)+(240442426577/100000000000000000000 : ℝ) ≤ ((26639092519355885119/26641000000000000000 : ℝ)+(11833199530551/2664100000000000 : ℝ)*((27447/100000 : ℝ)+(403/50000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (26639092519355885119/26641000000000000000 : ℝ)+(11833199530551/2664100000000000 : ℝ)*((27447/100000 : ℝ)+(403/50000 : ℝ))=(10011833211211873/10000000000000000 : ℝ) by norm_num, show 1+(244018259450964529/50000000000000000000 : ℝ)+(240442426577/100000000000000000000 : ℝ)=(20097607351868871127/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(244018259450964529/50000000000000000000 : ℝ) ≤ ((26639092519355885119/26641000000000000000 : ℝ)+2*(11833199530551/2664100000000000 : ℝ)*(27447/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (26639092519355885119/26641000000000000000 : ℝ)+2*(11833199530551/2664100000000000 : ℝ)*(27447/100000 : ℝ)=(1252958301342803/1250000000000000 : ℝ) by norm_num, show 1+2*(244018259450964529/50000000000000000000 : ℝ)=(25244018259450964529/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26639092519355885119/26641000000000000000 : ℝ)*(X 1 0+X 2 0)+(11833199530551/2664100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (403/50000 : ℝ)) (hi := (27447/100000 : ℝ)) (c := (26639092519355885119/26641000000000000000 : ℝ)) (alpha := (11833199530551/2664100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26639092519355885119/26641000000000000000 : ℝ)*(X 0 1+X 2 1)+(11833199530551/2664100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (403/50000 : ℝ)) (hi := (27447/100000 : ℝ)) (c := (26639092519355885119/26641000000000000000 : ℝ)) (alpha := (11833199530551/2664100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26639092519355885119/26641000000000000000 : ℝ)*(X 0 2+X 1 2)+(11833199530551/2664100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (403/50000 : ℝ)) (hi := (27447/100000 : ℝ)) (c := (26639092519355885119/26641000000000000000 : ℝ)) (alpha := (11833199530551/2664100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2059119337/10000000000 : ℝ)*X 0 0+(5676350441/10000000000 : ℝ)*X 0 1+(1255484963/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5413818829/10000000000 : ℝ)*X 1 0+(-482116199/2000000000 : ℝ)*X 1 1+(2510969963/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706909447/5000000000 : ℝ)*X 2 0+(2510969943/5000000000 : ℝ)*X 2 1+(-1205290481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154558947/5000000000 : ℝ)*X 0 0+(1847460189/5000000000 : ℝ)*X 0 1+(200866791/400000000 : ℝ)*X 0 2+(2154558947/5000000000 : ℝ)*X 1 0+(1847460189/5000000000 : ℝ)*X 1 1+(200866791/400000000 : ℝ)*X 1 2+(2154558947/5000000000 : ℝ)*X 2 0+(1847460189/5000000000 : ℝ)*X 2 1+(200866791/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-257474979/1250000000 : ℝ)*X 0 0+(628818287/1250000000 : ℝ)*X 0 1+(2833789817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622623797/5000000000 : ℝ)*X 1 0+(-1764940769/10000000000 : ℝ)*X 1 1+(2833789891/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327827997/625000000 : ℝ)*X 2 0+(113351611/200000000 : ℝ)*X 2 1+(-352987829/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310495899/10000000000 : ℝ)*X 0 0+(1251055469/2500000000 : ℝ)*X 0 1+(1856350349/5000000000 : ℝ)*X 0 2+(4310495899/10000000000 : ℝ)*X 1 0+(1251055469/2500000000 : ℝ)*X 1 1+(1856350349/5000000000 : ℝ)*X 1 2+(4310495899/10000000000 : ℝ)*X 2 0+(1251055469/2500000000 : ℝ)*X 2 1+(1856350349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11704405179287607279628134519/1332050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23434469/25000000000000 : ℝ)*(base1) + (1893831181/100000000000000 : ℝ)*(base19) + (1912178169/100000000000000 : ℝ)*(base23) + (51494609/25000000000000 : ℝ)*(upper3) + (223188273/100000000000000 : ℝ)*(upper5) + (1140923307839133/100000000000000 : ℝ)*(major0) + (1140923307839133/100000000000000 : ℝ)*(major1) + (1140923307839133/100000000000000 : ℝ)*(major2) + (382025746384643/25000000000000 : ℝ)*(sp0) + (1528111855657759/100000000000000 : ℝ)*(sp1) + (1528111837310771/100000000000000 : ℝ)*(sp2) + (376863559516037/50000000000000 : ℝ)*(sp3) + (2171537649/20000000000000 : ℝ)*(sp4) + (1340131833/25000000000000 : ℝ)*(sp7) + (753732573297283/100000000000000 : ℝ)*(f.failure) + (76405687474447/5000000000000 : ℝ)*(f.sum) + (535800733778183/133205000000000000000000000000 : ℝ)*base65 + (14027629803418208173/2664100000000000000000000000000000 : ℝ)*base68 + (7512294013112608173/2664100000000000000000000000000000 : ℝ)*base70 + (10244004217779891827/2664100000000000000000000000000000 : ℝ)*base71 + (21373567084689/16650625000000000000000000000 : ℝ)*base74 + (6286113131431391827/2664100000000000000000000000000000 : ℝ)*base75 + (9350563481641591827/2664100000000000000000000000000000 : ℝ)*base77 + (12453227591672391827/2664100000000000000000000000000000 : ℝ)*base79 + (82517790406563/133205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (569913/625000000000000000000 : ℝ)*base89 + (569913/625000000000000000000 : ℝ)*base91 + (569913/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1354759887660506121612340407/1332050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (863683869/100000000000000 : ℝ)*(base19) + (21695773/1562500000000 : ℝ)*(base23) + (119664441/100000000000000 : ℝ)*(upper2) + (21339893/12500000000000 : ℝ)*(upper3) + (4282289/12500000000000 : ℝ)*(upper5) + (1172028262296783/100000000000000 : ℝ)*(major0) + (1172028262296783/100000000000000 : ℝ)*(major1) + (1172028262296783/100000000000000 : ℝ)*(major2) + (3511209361/100000000000000 : ℝ)*(sp1) + (147027369/1562500000000 : ℝ)*(sp2) + (1569774931144153/100000000000000 : ℝ)*(sp4) + (1569770556250923/100000000000000 : ℝ)*(sp5) + (313952826572613/20000000000000 : ℝ)*(sp6) + (774281559547781/100000000000000 : ℝ)*(sp7) + (774281559547781/100000000000000 : ℝ)*(f.failure) + (1569774931144153/100000000000000 : ℝ)*(f.sum) + (88912377077359/66602500000000000000000000000 : ℝ)*base65 + (31252766110745202177/2664100000000000000000000000000000 : ℝ)*base67 + (5987862485931602177/2664100000000000000000000000000000 : ℝ)*base69 + (3413525312640602177/2664100000000000000000000000000000 : ℝ)*base71 + (300331347824763/133205000000000000000000000000 : ℝ)*base73 + (7044161964844602177/2664100000000000000000000000000000 : ℝ)*base75 + (10162654875643302177/2664100000000000000000000000000000 : ℝ)*base77 + (13044883447289402177/2664100000000000000000000000000000 : ℝ)*base79 + (11612103671343/33301250000000000000000000000 : ℝ)*base82 + (1795809/625000000000000000000 : ℝ)*base90 + (1795809/625000000000000000000 : ℝ)*base92 + (1795809/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1239_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27447/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (403/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (247/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1239_s2_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-526827983/2500000000 : ℝ)*x 0 + (2746648579/5000000000 : ℝ)*x 1 + (5174261157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526827983/2500000000 : ℝ)^527 ≤ (6393662124351/50000000000000 : ℝ)^399 := by
    have hnat : (526827983 : ℕ)^527*50000000000000^399 ≤ 6393662124351^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526827983 2500000000 6393662124351 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746648579/5000000000 : ℝ)^527 ≤ (11332116635283/25000000000000 : ℝ)^399 := by
    have hnat : (2746648579 : ℕ)^527*25000000000000^399 ≤ 11332116635283^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746648579 5000000000 11332116635283 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174261157/10000000000 : ℝ)^527 ≤ (10471052298833/25000000000000 : ℝ)^399 := by
    have hnat : (5174261157 : ℕ)^527*25000000000000^399 ≤ 10471052298833^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174261157 10000000000 10471052298833 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526827983/2500000000 : ℝ), (2746648579/5000000000 : ℝ), (5174261157/10000000000 : ℝ)] ![(6393662124351/50000000000000 : ℝ), (11332116635283/25000000000000 : ℝ), (10471052298833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526827983/2500000000 : ℝ)|^527 ≤ (6393662124351/50000000000000 : ℝ)^399
        have hw : |(-526827983/2500000000 : ℝ)|=(526827983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746648579/5000000000 : ℝ)|^527 ≤ (11332116635283/25000000000000 : ℝ)^399
        have hw : |(2746648579/5000000000 : ℝ)|=(2746648579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174261157/10000000000 : ℝ)|^527 ≤ (10471052298833/25000000000000 : ℝ)^399
        have hw : |(5174261157/10000000000 : ℝ)|=(5174261157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s2_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5369806249/10000000000 : ℝ)*x 0 + (-1136293733/5000000000 : ℝ)*x 1 + (1034852229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369806249/10000000000 : ℝ)^527 ≤ (21993725624709/50000000000000 : ℝ)^399 := by
    have hnat : (5369806249 : ℕ)^527*50000000000000^399 ≤ 21993725624709^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369806249 10000000000 21993725624709 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136293733/5000000000 : ℝ)^527 ≤ (14128339673083/100000000000000 : ℝ)^399 := by
    have hnat : (1136293733 : ℕ)^527*100000000000000^399 ≤ 14128339673083^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136293733 5000000000 14128339673083 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034852229/2000000000 : ℝ)^527 ≤ (20942104533517/50000000000000 : ℝ)^399 := by
    have hnat : (1034852229 : ℕ)^527*50000000000000^399 ≤ 20942104533517^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034852229 2000000000 20942104533517 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369806249/10000000000 : ℝ), (-1136293733/5000000000 : ℝ), (1034852229/2000000000 : ℝ)] ![(21993725624709/50000000000000 : ℝ), (14128339673083/100000000000000 : ℝ), (20942104533517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369806249/10000000000 : ℝ)|^527 ≤ (21993725624709/50000000000000 : ℝ)^399
        have hw : |(5369806249/10000000000 : ℝ)|=(5369806249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136293733/5000000000 : ℝ)|^527 ≤ (14128339673083/100000000000000 : ℝ)^399
        have hw : |(-1136293733/5000000000 : ℝ)|=(1136293733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034852229/2000000000 : ℝ)|^527 ≤ (20942104533517/50000000000000 : ℝ)^399
        have hw : |(1034852229/2000000000 : ℝ)|=(1034852229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s2_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (671225761/1250000000 : ℝ)*x 0 + (2587130639/5000000000 : ℝ)*x 1 + (-454517501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671225761/1250000000 : ℝ)^527 ≤ (1759497980299/4000000000000 : ℝ)^399 := by
    have hnat : (671225761 : ℕ)^527*4000000000000^399 ≤ 1759497980299^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671225761 1250000000 1759497980299 4000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587130639/5000000000 : ℝ)^527 ≤ (41884210489007/100000000000000 : ℝ)^399 := by
    have hnat : (2587130639 : ℕ)^527*100000000000000^399 ≤ 41884210489007^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587130639 5000000000 41884210489007 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454517501/2000000000 : ℝ)^527 ≤ (14128339993321/100000000000000 : ℝ)^399 := by
    have hnat : (454517501 : ℕ)^527*100000000000000^399 ≤ 14128339993321^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454517501 2000000000 14128339993321 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671225761/1250000000 : ℝ), (2587130639/5000000000 : ℝ), (-454517501/2000000000 : ℝ)] ![(1759497980299/4000000000000 : ℝ), (41884210489007/100000000000000 : ℝ), (14128339993321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671225761/1250000000 : ℝ)|^527 ≤ (1759497980299/4000000000000 : ℝ)^399
        have hw : |(671225761/1250000000 : ℝ)|=(671225761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587130639/5000000000 : ℝ)|^527 ≤ (41884210489007/100000000000000 : ℝ)^399
        have hw : |(2587130639/5000000000 : ℝ)|=(2587130639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454517501/2000000000 : ℝ)|^527 ≤ (14128339993321/100000000000000 : ℝ)^399
        have hw : |(-454517501/2000000000 : ℝ)|=(454517501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s2_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4342399129/10000000000 : ℝ)*x 0 + (806133143/2000000000 : ℝ)*x 1 + (2338738959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342399129/10000000000 : ℝ)^527 ≤ (16614325590779/50000000000000 : ℝ)^399 := by
    have hnat : (4342399129 : ℕ)^527*50000000000000^399 ≤ 16614325590779^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342399129 10000000000 16614325590779 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806133143/2000000000 : ℝ)^527 ≤ (30114860895343/100000000000000 : ℝ)^399 := by
    have hnat : (806133143 : ℕ)^527*100000000000000^399 ≤ 30114860895343^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806133143 2000000000 30114860895343 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2338738959/5000000000 : ℝ)^527 ≤ (18328243949789/50000000000000 : ℝ)^399 := by
    have hnat : (2338738959 : ℕ)^527*50000000000000^399 ≤ 18328243949789^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338738959 5000000000 18328243949789 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342399129/10000000000 : ℝ), (806133143/2000000000 : ℝ), (2338738959/5000000000 : ℝ)] ![(16614325590779/50000000000000 : ℝ), (30114860895343/100000000000000 : ℝ), (18328243949789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342399129/10000000000 : ℝ)|^527 ≤ (16614325590779/50000000000000 : ℝ)^399
        have hw : |(4342399129/10000000000 : ℝ)|=(4342399129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806133143/2000000000 : ℝ)|^527 ≤ (30114860895343/100000000000000 : ℝ)^399
        have hw : |(806133143/2000000000 : ℝ)|=(806133143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2338738959/5000000000 : ℝ)|^527 ≤ (18328243949789/50000000000000 : ℝ)^399
        have hw : |(2338738959/5000000000 : ℝ)|=(2338738959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s2_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107390973/10000000000 : ℝ)*x 0 + (2588158157/5000000000 : ℝ)*x 1 + (1372805673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107390973/10000000000 : ℝ)^527 ≤ (12787957744313/100000000000000 : ℝ)^399 := by
    have hnat : (2107390973 : ℕ)^527*100000000000000^399 ≤ 12787957744313^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107390973 10000000000 12787957744313 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588158157/5000000000 : ℝ)^527 ≤ (5238272919937/12500000000000 : ℝ)^399 := by
    have hnat : (2588158157 : ℕ)^527*12500000000000^399 ≤ 5238272919937^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588158157 5000000000 5238272919937 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372805673/2500000000 : ℝ)^527 ≤ (28316161799/62500000000 : ℝ)^399 := by
    have hnat : (1372805673 : ℕ)^527*62500000000^399 ≤ 28316161799^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372805673 2500000000 28316161799 62500000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107390973/10000000000 : ℝ), (2588158157/5000000000 : ℝ), (1372805673/2500000000 : ℝ)] ![(12787957744313/100000000000000 : ℝ), (5238272919937/12500000000000 : ℝ), (28316161799/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107390973/10000000000 : ℝ)|^527 ≤ (12787957744313/100000000000000 : ℝ)^399
        have hw : |(-2107390973/10000000000 : ℝ)|=(2107390973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588158157/5000000000 : ℝ)|^527 ≤ (5238272919937/12500000000000 : ℝ)^399
        have hw : |(2588158157/5000000000 : ℝ)|=(2588158157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372805673/2500000000 : ℝ)|^527 ≤ (28316161799/62500000000 : ℝ)^399
        have hw : |(1372805673/2500000000 : ℝ)|=(1372805673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s2_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1322087069/2500000000 : ℝ)*x 0 + (-1955625707/10000000000 : ℝ)*x 1 + (343201421/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322087069/2500000000 : ℝ)^527 ≤ (4310826716801/10000000000000 : ℝ)^399 := by
    have hnat : (1322087069 : ℕ)^527*10000000000000^399 ≤ 4310826716801^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322087069 2500000000 4310826716801 10000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955625707/10000000000 : ℝ)^527 ≤ (1158587346657/10000000000000 : ℝ)^399 := by
    have hnat : (1955625707 : ℕ)^527*10000000000000^399 ≤ 1158587346657^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955625707 10000000000 1158587346657 10000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343201421/625000000 : ℝ)^527 ≤ (22652929678943/50000000000000 : ℝ)^399 := by
    have hnat : (343201421 : ℕ)^527*50000000000000^399 ≤ 22652929678943^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343201421 625000000 22652929678943 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322087069/2500000000 : ℝ), (-1955625707/10000000000 : ℝ), (343201421/625000000 : ℝ)] ![(4310826716801/10000000000000 : ℝ), (1158587346657/10000000000000 : ℝ), (22652929678943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322087069/2500000000 : ℝ)|^527 ≤ (4310826716801/10000000000000 : ℝ)^399
        have hw : |(1322087069/2500000000 : ℝ)|=(1322087069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955625707/10000000000 : ℝ)|^527 ≤ (1158587346657/10000000000000 : ℝ)^399
        have hw : |(-1955625707/10000000000 : ℝ)|=(1955625707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(343201421/625000000 : ℝ)|^527 ≤ (22652929678943/50000000000000 : ℝ)^399
        have hw : |(343201421/625000000 : ℝ)|=(343201421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s2_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1057669689/2000000000 : ℝ)*x 0 + (1372805703/2500000000 : ℝ)*x 1 + (-1955625367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057669689/2000000000 : ℝ)^527 ≤ (10777067246891/25000000000000 : ℝ)^399 := by
    have hnat : (1057669689 : ℕ)^527*25000000000000^399 ≤ 10777067246891^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057669689 2000000000 10777067246891 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372805703/2500000000 : ℝ)^527 ≤ (45305860186089/100000000000000 : ℝ)^399 := by
    have hnat : (1372805703 : ℕ)^527*100000000000000^399 ≤ 45305860186089^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372805703 2500000000 45305860186089 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1955625367/10000000000 : ℝ)^527 ≤ (2896467701523/25000000000000 : ℝ)^399 := by
    have hnat : (1955625367 : ℕ)^527*25000000000000^399 ≤ 2896467701523^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955625367 10000000000 2896467701523 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057669689/2000000000 : ℝ), (1372805703/2500000000 : ℝ), (-1955625367/10000000000 : ℝ)] ![(10777067246891/25000000000000 : ℝ), (45305860186089/100000000000000 : ℝ), (2896467701523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057669689/2000000000 : ℝ)|^527 ≤ (10777067246891/25000000000000 : ℝ)^399
        have hw : |(1057669689/2000000000 : ℝ)|=(1057669689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372805703/2500000000 : ℝ)|^527 ≤ (45305860186089/100000000000000 : ℝ)^399
        have hw : |(1372805703/2500000000 : ℝ)|=(1372805703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1955625367/10000000000 : ℝ)|^527 ≤ (2896467701523/25000000000000 : ℝ)^399
        have hw : |(-1955625367/10000000000 : ℝ)|=(1955625367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s2_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4342558837/10000000000 : ℝ)*x 0 + (934662307/2000000000 : ℝ)*x 1 + (806974189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342558837/10000000000 : ℝ)^527 ≤ (4153783169249/12500000000000 : ℝ)^399 := by
    have hnat : (4342558837 : ℕ)^527*12500000000000^399 ≤ 4153783169249^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342558837 10000000000 4153783169249 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934662307/2000000000 : ℝ)^527 ≤ (292906947011/800000000000 : ℝ)^399 := by
    have hnat : (934662307 : ℕ)^527*800000000000^399 ≤ 292906947011^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934662307 2000000000 292906947011 800000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806974189/2000000000 : ℝ)^527 ≤ (18847728911/62500000000 : ℝ)^399 := by
    have hnat : (806974189 : ℕ)^527*62500000000^399 ≤ 18847728911^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806974189 2000000000 18847728911 62500000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342558837/10000000000 : ℝ), (934662307/2000000000 : ℝ), (806974189/2000000000 : ℝ)] ![(4153783169249/12500000000000 : ℝ), (292906947011/800000000000 : ℝ), (18847728911/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342558837/10000000000 : ℝ)|^527 ≤ (4153783169249/12500000000000 : ℝ)^399
        have hw : |(4342558837/10000000000 : ℝ)|=(4342558837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(934662307/2000000000 : ℝ)|^527 ≤ (292906947011/800000000000 : ℝ)^399
        have hw : |(934662307/2000000000 : ℝ)|=(934662307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806974189/2000000000 : ℝ)|^527 ≤ (18847728911/62500000000 : ℝ)^399
        have hw : |(806974189/2000000000 : ℝ)|=(806974189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (247/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (9487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16231/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (247/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (247/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (247/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (247/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (247/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (247/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (247/4000 : ℝ) ^ (8431/2048 : ℝ) ≤ (1050548545958207/100000000000000000000 : ℝ) := by
    have hpowers : (247/4000 : ℝ)^8431 ≤ (1050548545958207/100000000000000000000 : ℝ)^2048 := by
      have hnat : (247 : ℕ)^8431*100000000000000000000^2048 ≤ 1050548545958207^2048*4000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        247 4000 1050548545958207 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (247/4000 : ℝ)) (X := (1050548545958207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20011/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (16612836649987301/12500000000000000000 : ℝ) := by
    have hpowers : (20011/100000 : ℝ)^8431 ≤ (16612836649987301/12500000000000000000 : ℝ)^2048 := by
      have hnat : (20011 : ℕ)^8431*12500000000000000000^2048 ≤ 16612836649987301^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011 100000 16612836649987301 12500000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20011/100000 : ℝ)) (X := (16612836649987301/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001050548545958207/50000000000000000000 : ℝ) ≤ (10000051037986243/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50001050548545958207/50000000000000000000 : ℝ)^2048 ≤ (10000051037986243/10000000000000000 : ℝ)^8431 := by
      have hnat : (50001050548545958207 : ℕ)^2048*10000000000000000^8431 ≤ 10000051037986243^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001050548545958207 50000000000000000000 10000051037986243 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000051037986243/10000000000000000 : ℝ)) (X := (50001050548545958207/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20026790648349171323/20000000000000000000 : ℝ) ≤ (5001626125252719/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (20026790648349171323/20000000000000000000 : ℝ)^2048 ≤ (5001626125252719/5000000000000000 : ℝ)^8431 := by
      have hnat : (20026790648349171323 : ℕ)^2048*5000000000000000^8431 ≤ 5001626125252719^8431*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20026790648349171323 20000000000000000000 5001626125252719 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001626125252719/5000000000000000 : ℝ)) (X := (20026790648349171323/20000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6266612836649987301/6250000000000000000 : ℝ) ≤ (10006453463024633/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (6266612836649987301/6250000000000000000 : ℝ)^2048 ≤ (10006453463024633/10000000000000000 : ℝ)^8431 := by
      have hnat : (6266612836649987301 : ℕ)^2048*10000000000000000^8431 ≤ 10006453463024633^8431*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6266612836649987301 6250000000000000000 10006453463024633 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006453463024633/10000000000000000 : ℝ)) (X := (6266612836649987301/6250000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1050548545958207/100000000000000000000 : ℝ) ≤ ((69160585593482799949/69180000000000000000 : ℝ)+2*(640242503839/276720000000000 : ℝ)*(247/4000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (69160585593482799949/69180000000000000000 : ℝ)+2*(640242503839/276720000000000 : ℝ)*(247/4000 : ℝ)=(10000051037986243/10000000000000000 : ℝ) by norm_num, show 1+2*(1050548545958207/100000000000000000000 : ℝ)=(50001050548545958207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16612836649987301/12500000000000000000 : ℝ)+(1050548545958207/100000000000000000000 : ℝ) ≤ ((69160585593482799949/69180000000000000000 : ℝ)+(640242503839/276720000000000 : ℝ)*((20011/100000 : ℝ)+(247/4000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (69160585593482799949/69180000000000000000 : ℝ)+(640242503839/276720000000000 : ℝ)*((20011/100000 : ℝ)+(247/4000 : ℝ))=(5001626125252719/5000000000000000 : ℝ) by norm_num, show 1+(16612836649987301/12500000000000000000 : ℝ)+(1050548545958207/100000000000000000000 : ℝ)=(20026790648349171323/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16612836649987301/12500000000000000000 : ℝ) ≤ ((69160585593482799949/69180000000000000000 : ℝ)+2*(640242503839/276720000000000 : ℝ)*(20011/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (69160585593482799949/69180000000000000000 : ℝ)+2*(640242503839/276720000000000 : ℝ)*(20011/100000 : ℝ)=(10006453463024633/10000000000000000 : ℝ) by norm_num, show 1+2*(16612836649987301/12500000000000000000 : ℝ)=(6266612836649987301/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69160585593482799949/69180000000000000000 : ℝ)*(X 1 0+X 2 0)+(640242503839/276720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (247/4000 : ℝ)) (hi := (20011/100000 : ℝ)) (c := (69160585593482799949/69180000000000000000 : ℝ)) (alpha := (640242503839/276720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69160585593482799949/69180000000000000000 : ℝ)*(X 0 1+X 2 1)+(640242503839/276720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (247/4000 : ℝ)) (hi := (20011/100000 : ℝ)) (c := (69160585593482799949/69180000000000000000 : ℝ)) (alpha := (640242503839/276720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69160585593482799949/69180000000000000000 : ℝ)*(X 0 2+X 1 2)+(640242503839/276720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (247/4000 : ℝ)) (hi := (20011/100000 : ℝ)) (c := (69160585593482799949/69180000000000000000 : ℝ)) (alpha := (640242503839/276720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526827983/2500000000 : ℝ)*X 0 0+(2746648579/5000000000 : ℝ)*X 0 1+(5174261157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369806249/10000000000 : ℝ)*X 1 0+(-1136293733/5000000000 : ℝ)*X 1 1+(1034852229/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671225761/1250000000 : ℝ)*X 2 0+(2587130639/5000000000 : ℝ)*X 2 1+(-454517501/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342399129/10000000000 : ℝ)*X 0 0+(806133143/2000000000 : ℝ)*X 0 1+(2338738959/5000000000 : ℝ)*X 0 2+(4342399129/10000000000 : ℝ)*X 1 0+(806133143/2000000000 : ℝ)*X 1 1+(2338738959/5000000000 : ℝ)*X 1 2+(4342399129/10000000000 : ℝ)*X 2 0+(806133143/2000000000 : ℝ)*X 2 1+(2338738959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107390973/10000000000 : ℝ)*X 0 0+(2588158157/5000000000 : ℝ)*X 0 1+(1372805673/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322087069/2500000000 : ℝ)*X 1 0+(-1955625707/10000000000 : ℝ)*X 1 1+(343201421/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057669689/2000000000 : ℝ)*X 2 0+(1372805703/2500000000 : ℝ)*X 2 1+(-1955625367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342558837/10000000000 : ℝ)*X 0 0+(934662307/2000000000 : ℝ)*X 0 1+(806974189/2000000000 : ℝ)*X 0 2+(4342558837/10000000000 : ℝ)*X 1 0+(934662307/2000000000 : ℝ)*X 1 1+(806974189/2000000000 : ℝ)*X 1 2+(4342558837/10000000000 : ℝ)*X 2 0+(934662307/2000000000 : ℝ)*X 2 1+(806974189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4410087235685268925763484813/576500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (741778127/50000000000000 : ℝ)*(base19) + (321822631/25000000000000 : ℝ)*(base23) + (5492587/10000000000000 : ℝ)*(lower2) + (235989831/100000000000000 : ℝ)*(upper3) + (25724103/25000000000000 : ℝ)*(upper5) + (1170133778301663/50000000000000 : ℝ)*(major0) + (1170133778301663/50000000000000 : ℝ)*(major1) + (1170133778301663/50000000000000 : ℝ)*(major2) + (3134459836588349/100000000000000 : ℝ)*(sp0) + (1567236688063233/50000000000000 : ℝ)*(sp1) + (783618393098049/25000000000000 : ℝ)*(sp2) + (386512814016389/25000000000000 : ℝ)*(sp3) + (15023094371/100000000000000 : ℝ)*(sp4) + (4371233167/50000000000000 : ℝ)*(sp7) + (1546059998531891/100000000000000 : ℝ)*(f.failure) + (19590467873017/625000000000 : ℝ)*(f.sum) + (1660570116067/2306000000000000000000000000 : ℝ)*base66 + (1985563944924421729/1153000000000000000000000000000000 : ℝ)*base67 + (7213002257283421729/1153000000000000000000000000000000 : ℝ)*base69 + (5069325345925578271/1153000000000000000000000000000000 : ℝ)*base72 + (404471707631/92240000000000000000000000 : ℝ)*base73 + (9625266144398421729/1153000000000000000000000000000000 : ℝ)*base75 + (3067029251667578271/1153000000000000000000000000000000 : ℝ)*base78 + (15538265097568421729/1153000000000000000000000000000000 : ℝ)*base79 + (15350916345671/2306000000000000000000000000 : ℝ)*base81 + (4345401/625000000000000000000 : ℝ)*base89 + (4345401/625000000000000000000 : ℝ)*base91 + (4345401/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (802164763284757561078527629/115300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445825853/25000000000000 : ℝ)*(base19) + (204146967/10000000000000 : ℝ)*(base23) + (34425039/100000000000000 : ℝ)*(upper2) + (12145073/5000000000000 : ℝ)*(upper3) + (68418307/50000000000000 : ℝ)*(upper5) + (237093150852107/10000000000000 : ℝ)*(major0) + (237093150852107/10000000000000 : ℝ)*(major1) + (237093150852107/10000000000000 : ℝ)*(major2) + (18144871299/100000000000000 : ℝ)*(sp1) + (752845387/3125000000000 : ℝ)*(sp2) + (3175545141565127/100000000000000 : ℝ)*(sp4) + (198470325836901/6250000000000 : ℝ)*(sp5) + (1587759504521537/50000000000000 : ℝ)*(sp6) + (391579410892613/25000000000000 : ℝ)*(sp7) + (391579410892613/25000000000000 : ℝ)*(f.failure) + (3175545141565127/100000000000000 : ℝ)*(f.sum) + (35042327145389/6918000000000000000000000000 : ℝ)*base66 + (917018851617007457/691800000000000000000000000000000 : ℝ)*base68 + (8656000966543807457/691800000000000000000000000000000 : ℝ)*base70 + (6902962863794407457/691800000000000000000000000000000 : ℝ)*base72 + (29738408588533/6918000000000000000000000000 : ℝ)*base73 + (1493666647538407457/691800000000000000000000000000000 : ℝ)*base76 + (8298021461963407457/691800000000000000000000000000000 : ℝ)*base78 + (9672860931528607457/691800000000000000000000000000000 : ℝ)*base80 + (20605231181051/6918000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2491543/156250000000000000000 : ℝ)*base89 + (2491543/156250000000000000000 : ℝ)*base91 + (2491543/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1239_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (247/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1239_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1239_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1239_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1239_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
