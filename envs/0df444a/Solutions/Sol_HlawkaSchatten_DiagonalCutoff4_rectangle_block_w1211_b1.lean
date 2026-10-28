-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1211_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:12.684788+00:00
-- url     : https://prove2.me/submissions/42e93f9a-c1d8-4567-ae10-3d03bc67c568

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
theorem support_rectangle_w1211_s3_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-426241157/2000000000 : ℝ)*x 0 + (1355612457/2500000000 : ℝ)*x 1 + (2619075251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426241157/2000000000 : ℝ)^2101 ≤ (6475424816613/50000000000000 : ℝ)^1589 := by
    have hnat : (426241157 : ℕ)^2101*50000000000000^1589 ≤ 6475424816613^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426241157 2000000000 6475424816613 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355612457/2500000000 : ℝ)^2101 ≤ (44519399523411/100000000000000 : ℝ)^1589 := by
    have hnat : (1355612457 : ℕ)^2101*100000000000000^1589 ≤ 44519399523411^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355612457 2500000000 44519399523411 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619075251/5000000000 : ℝ)^2101 ≤ (42529750822569/100000000000000 : ℝ)^1589 := by
    have hnat : (2619075251 : ℕ)^2101*100000000000000^1589 ≤ 42529750822569^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619075251 5000000000 42529750822569 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426241157/2000000000 : ℝ), (1355612457/2500000000 : ℝ), (2619075251/5000000000 : ℝ)] ![(6475424816613/50000000000000 : ℝ), (44519399523411/100000000000000 : ℝ), (42529750822569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426241157/2000000000 : ℝ)|^2101 ≤ (6475424816613/50000000000000 : ℝ)^1589
        have hw : |(-426241157/2000000000 : ℝ)|=(426241157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355612457/2500000000 : ℝ)|^2101 ≤ (44519399523411/100000000000000 : ℝ)^1589
        have hw : |(1355612457/2500000000 : ℝ)|=(1355612457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619075251/5000000000 : ℝ)|^2101 ≤ (42529750822569/100000000000000 : ℝ)^1589
        have hw : |(2619075251/5000000000 : ℝ)|=(2619075251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s3_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338046029/2500000000 : ℝ)*x 0 + (-556319779/2500000000 : ℝ)*x 1 + (2619075253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338046029/2500000000 : ℝ)^2101 ≤ (5469777067283/12500000000000 : ℝ)^1589 := by
    have hnat : (1338046029 : ℕ)^2101*12500000000000^1589 ≤ 5469777067283^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338046029 2500000000 5469777067283 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556319779/2500000000 : ℝ)^2101 ≤ (3428008144199/25000000000000 : ℝ)^1589 := by
    have hnat : (556319779 : ℕ)^2101*25000000000000^1589 ≤ 3428008144199^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556319779 2500000000 3428008144199 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619075253/5000000000 : ℝ)^2101 ≤ (4252975086551/10000000000000 : ℝ)^1589 := by
    have hnat : (2619075253 : ℕ)^2101*10000000000000^1589 ≤ 4252975086551^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619075253 5000000000 4252975086551 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338046029/2500000000 : ℝ), (-556319779/2500000000 : ℝ), (2619075253/5000000000 : ℝ)] ![(5469777067283/12500000000000 : ℝ), (3428008144199/25000000000000 : ℝ), (4252975086551/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338046029/2500000000 : ℝ)|^2101 ≤ (5469777067283/12500000000000 : ℝ)^1589
        have hw : |(1338046029/2500000000 : ℝ)|=(1338046029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556319779/2500000000 : ℝ)|^2101 ≤ (3428008144199/25000000000000 : ℝ)^1589
        have hw : |(-556319779/2500000000 : ℝ)|=(556319779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619075253/5000000000 : ℝ)|^2101 ≤ (4252975086551/10000000000000 : ℝ)^1589
        have hw : |(2619075253/5000000000 : ℝ)|=(2619075253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s3_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352184099/10000000000 : ℝ)*x 0 + (654768827/1250000000 : ℝ)*x 1 + (-1112639497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352184099/10000000000 : ℝ)^2101 ≤ (10939554088623/25000000000000 : ℝ)^1589 := by
    have hnat : (5352184099 : ℕ)^2101*25000000000000^1589 ≤ 10939554088623^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352184099 10000000000 10939554088623 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654768827/1250000000 : ℝ)^2101 ≤ (42529752046401/100000000000000 : ℝ)^1589 := by
    have hnat : (654768827 : ℕ)^2101*100000000000000^1589 ≤ 42529752046401^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654768827 1250000000 42529752046401 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112639497/5000000000 : ℝ)^2101 ≤ (3428007895703/25000000000000 : ℝ)^1589 := by
    have hnat : (1112639497 : ℕ)^2101*25000000000000^1589 ≤ 3428007895703^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112639497 5000000000 3428007895703 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352184099/10000000000 : ℝ), (654768827/1250000000 : ℝ), (-1112639497/5000000000 : ℝ)] ![(10939554088623/25000000000000 : ℝ), (42529752046401/100000000000000 : ℝ), (3428007895703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352184099/10000000000 : ℝ)|^2101 ≤ (10939554088623/25000000000000 : ℝ)^1589
        have hw : |(5352184099/10000000000 : ℝ)|=(5352184099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654768827/1250000000 : ℝ)|^2101 ≤ (42529752046401/100000000000000 : ℝ)^1589
        have hw : |(654768827/1250000000 : ℝ)|=(654768827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112639497/5000000000 : ℝ)|^2101 ≤ (3428007895703/25000000000000 : ℝ)^1589
        have hw : |(-1112639497/5000000000 : ℝ)|=(1112639497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s3_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4353186669/10000000000 : ℝ)*x 0 + (417125191/1000000000 : ℝ)*x 1 + (4542879241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353186669/10000000000 : ℝ)^2101 ≤ (16649281759399/50000000000000 : ℝ)^1589 := by
    have hnat : (4353186669 : ℕ)^2101*50000000000000^1589 ≤ 16649281759399^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353186669 10000000000 16649281759399 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417125191/1000000000 : ℝ)^2101 ≤ (31470995099917/100000000000000 : ℝ)^1589 := by
    have hnat : (417125191 : ℕ)^2101*100000000000000^1589 ≤ 31470995099917^1589*1000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417125191 1000000000 31470995099917 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542879241/10000000000 : ℝ)^2101 ≤ (56368706183/160000000000 : ℝ)^1589 := by
    have hnat : (4542879241 : ℕ)^2101*160000000000^1589 ≤ 56368706183^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542879241 10000000000 56368706183 160000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353186669/10000000000 : ℝ), (417125191/1000000000 : ℝ), (4542879241/10000000000 : ℝ)] ![(16649281759399/50000000000000 : ℝ), (31470995099917/100000000000000 : ℝ), (56368706183/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353186669/10000000000 : ℝ)|^2101 ≤ (16649281759399/50000000000000 : ℝ)^1589
        have hw : |(4353186669/10000000000 : ℝ)|=(4353186669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417125191/1000000000 : ℝ)|^2101 ≤ (31470995099917/100000000000000 : ℝ)^1589
        have hw : |(417125191/1000000000 : ℝ)|=(417125191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542879241/10000000000 : ℝ)|^2101 ≤ (56368706183/160000000000 : ℝ)^1589
        have hw : |(4542879241/10000000000 : ℝ)|=(4542879241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s3_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131221113/10000000000 : ℝ)*x 0 + (654854209/1250000000 : ℝ)*x 1 + (2710881427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131221113/10000000000 : ℝ)^2101 ≤ (3237743197693/25000000000000 : ℝ)^1589 := by
    have hnat : (2131221113 : ℕ)^2101*25000000000000^1589 ≤ 3237743197693^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131221113 10000000000 3237743197693 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654854209/1250000000 : ℝ)^2101 ≤ (332320977027/781250000000 : ℝ)^1589 := by
    have hnat : (654854209 : ℕ)^2101*781250000000^1589 ≤ 332320977027^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654854209 1250000000 332320977027 781250000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710881427/5000000000 : ℝ)^2101 ≤ (8902388424997/20000000000000 : ℝ)^1589 := by
    have hnat : (2710881427 : ℕ)^2101*20000000000000^1589 ≤ 8902388424997^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710881427 5000000000 8902388424997 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131221113/10000000000 : ℝ), (654854209/1250000000 : ℝ), (2710881427/5000000000 : ℝ)] ![(3237743197693/25000000000000 : ℝ), (332320977027/781250000000 : ℝ), (8902388424997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131221113/10000000000 : ℝ)|^2101 ≤ (3237743197693/25000000000000 : ℝ)^1589
        have hw : |(-2131221113/10000000000 : ℝ)|=(2131221113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654854209/1250000000 : ℝ)|^2101 ≤ (332320977027/781250000000 : ℝ)^1589
        have hw : |(654854209/1250000000 : ℝ)|=(654854209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710881427/5000000000 : ℝ)|^2101 ≤ (8902388424997/20000000000000 : ℝ)^1589
        have hw : |(2710881427/5000000000 : ℝ)|=(2710881427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s3_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305263279/10000000000 : ℝ)*x 0 + (-408333399/2000000000 : ℝ)*x 1 + (5421763187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305263279/10000000000 : ℝ)^2101 ≤ (432517142267/1000000000000 : ℝ)^1589 := by
    have hnat : (5305263279 : ℕ)^2101*1000000000000^1589 ≤ 432517142267^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305263279 10000000000 432517142267 1000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408333399/2000000000 : ℝ)^2101 ≤ (611817001433/5000000000000 : ℝ)^1589 := by
    have hnat : (408333399 : ℕ)^2101*5000000000000^1589 ≤ 611817001433^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408333399 2000000000 611817001433 5000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421763187/10000000000 : ℝ)^2101 ≤ (4451194573977/10000000000000 : ℝ)^1589 := by
    have hnat : (5421763187 : ℕ)^2101*10000000000000^1589 ≤ 4451194573977^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421763187 10000000000 4451194573977 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305263279/10000000000 : ℝ), (-408333399/2000000000 : ℝ), (5421763187/10000000000 : ℝ)] ![(432517142267/1000000000000 : ℝ), (611817001433/5000000000000 : ℝ), (4451194573977/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305263279/10000000000 : ℝ)|^2101 ≤ (432517142267/1000000000000 : ℝ)^1589
        have hw : |(5305263279/10000000000 : ℝ)|=(5305263279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408333399/2000000000 : ℝ)|^2101 ≤ (611817001433/5000000000000 : ℝ)^1589
        have hw : |(-408333399/2000000000 : ℝ)|=(408333399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421763187/10000000000 : ℝ)|^2101 ≤ (4451194573977/10000000000000 : ℝ)^1589
        have hw : |(5421763187/10000000000 : ℝ)|=(5421763187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s3_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132631617/250000000 : ℝ)*x 0 + (5421762537/10000000000 : ℝ)*x 1 + (-1020832989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132631617/250000000 : ℝ)^2101 ≤ (43251729328777/100000000000000 : ℝ)^1589 := by
    have hnat : (132631617 : ℕ)^2101*100000000000000^1589 ≤ 43251729328777^1589*250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132631617 250000000 43251729328777 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421762537/10000000000 : ℝ)^2101 ≤ (11127984670971/25000000000000 : ℝ)^1589 := by
    have hnat : (5421762537 : ℕ)^2101*25000000000000^1589 ≤ 11127984670971^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421762537 10000000000 11127984670971 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020832989/5000000000 : ℝ)^2101 ≤ (6118165984751/50000000000000 : ℝ)^1589 := by
    have hnat : (1020832989 : ℕ)^2101*50000000000000^1589 ≤ 6118165984751^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020832989 5000000000 6118165984751 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132631617/250000000 : ℝ), (5421762537/10000000000 : ℝ), (-1020832989/5000000000 : ℝ)] ![(43251729328777/100000000000000 : ℝ), (11127984670971/25000000000000 : ℝ), (6118165984751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132631617/250000000 : ℝ)|^2101 ≤ (43251729328777/100000000000000 : ℝ)^1589
        have hw : |(132631617/250000000 : ℝ)|=(132631617/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421762537/10000000000 : ℝ)|^2101 ≤ (11127984670971/25000000000000 : ℝ)^1589
        have hw : |(5421762537/10000000000 : ℝ)|=(5421762537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020832989/5000000000 : ℝ)|^2101 ≤ (6118165984751/50000000000000 : ℝ)^1589
        have hw : |(-1020832989/5000000000 : ℝ)|=(1020832989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s3_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (870643467/2000000000 : ℝ)*x 0 + (4541502419/10000000000 : ℝ)*x 1 + (834527177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870643467/2000000000 : ℝ)^2101 ≤ (33298873673227/100000000000000 : ℝ)^1589 := by
    have hnat : (870643467 : ℕ)^2101*100000000000000^1589 ≤ 33298873673227^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870643467 2000000000 33298873673227 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4541502419/10000000000 : ℝ)^2101 ≤ (17608162129829/50000000000000 : ℝ)^1589 := by
    have hnat : (4541502419 : ℕ)^2101*50000000000000^1589 ≤ 17608162129829^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541502419 10000000000 17608162129829 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834527177/2000000000 : ℝ)^2101 ≤ (31484802047289/100000000000000 : ℝ)^1589 := by
    have hnat : (834527177 : ℕ)^2101*100000000000000^1589 ≤ 31484802047289^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834527177 2000000000 31484802047289 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870643467/2000000000 : ℝ), (4541502419/10000000000 : ℝ), (834527177/2000000000 : ℝ)] ![(33298873673227/100000000000000 : ℝ), (17608162129829/50000000000000 : ℝ), (31484802047289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870643467/2000000000 : ℝ)|^2101 ≤ (33298873673227/100000000000000 : ℝ)^1589
        have hw : |(870643467/2000000000 : ℝ)|=(870643467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4541502419/10000000000 : ℝ)|^2101 ≤ (17608162129829/50000000000000 : ℝ)^1589
        have hw : |(4541502419/10000000000 : ℝ)|=(4541502419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834527177/2000000000 : ℝ)|^2101 ≤ (31484802047289/100000000000000 : ℝ)^1589
        have hw : |(834527177/2000000000 : ℝ)|=(834527177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1083/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9371/100000 : ℝ) ^ (8403/2048 : ℝ) ≤ (755300202089491/12500000000000000000 : ℝ) := by
    have hpowers : (9371/100000 : ℝ)^8403 ≤ (755300202089491/12500000000000000000 : ℝ)^2048 := by
      have hnat : (9371 : ℕ)^8403*12500000000000000000^2048 ≤ 755300202089491^2048*100000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9371 100000 755300202089491 12500000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9371/100000 : ℝ)) (X := (755300202089491/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8153/50000 : ℝ) ^ (8403/2048 : ℝ) ≤ (58646216688255497/100000000000000000000 : ℝ) := by
    have hpowers : (8153/50000 : ℝ)^8403 ≤ (58646216688255497/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8153 : ℕ)^8403*100000000000000000000^2048 ≤ 58646216688255497^2048*50000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8153 50000 58646216688255497 100000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8153/50000 : ℝ)) (X := (58646216688255497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250755300202089491/6250000000000000000 : ℝ) ≤ (5000147260181531/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (6250755300202089491/6250000000000000000 : ℝ)^2048 ≤ (5000147260181531/5000000000000000 : ℝ)^8403 := by
      have hnat : (6250755300202089491 : ℕ)^2048*5000000000000000^8403 ≤ 5000147260181531^8403*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250755300202089491 6250000000000000000 5000147260181531 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000147260181531/5000000000000000 : ℝ)) (X := (6250755300202089491/6250000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002587544732198857/4000000000000000000 : ℝ) ≤ (5000788110768177/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (4002587544732198857/4000000000000000000 : ℝ)^2048 ≤ (5000788110768177/5000000000000000 : ℝ)^8403 := by
      have hnat : (4002587544732198857 : ℕ)^2048*5000000000000000^8403 ≤ 5000788110768177^8403*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002587544732198857 4000000000000000000 5000788110768177 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000788110768177/5000000000000000 : ℝ)) (X := (4002587544732198857/4000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50058646216688255497/50000000000000000000 : ℝ) ≤ (5001428961354823/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (50058646216688255497/50000000000000000000 : ℝ)^2048 ≤ (5001428961354823/5000000000000000 : ℝ)^8403 := by
      have hnat : (50058646216688255497 : ℕ)^2048*5000000000000000^8403 ≤ 5001428961354823^8403*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058646216688255497 50000000000000000000 5001428961354823 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001428961354823/5000000000000000 : ℝ)) (X := (50058646216688255497/50000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(755300202089491/12500000000000000000 : ℝ) ≤ ((34664010427663998153/34675000000000000000 : ℝ)+2*(320425293323/173375000000000 : ℝ)*(9371/100000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (34664010427663998153/34675000000000000000 : ℝ)+2*(320425293323/173375000000000 : ℝ)*(9371/100000 : ℝ)=(5000147260181531/5000000000000000 : ℝ) by norm_num, show 1+2*(755300202089491/12500000000000000000 : ℝ)=(6250755300202089491/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58646216688255497/100000000000000000000 : ℝ)+(755300202089491/12500000000000000000 : ℝ) ≤ ((34664010427663998153/34675000000000000000 : ℝ)+(320425293323/173375000000000 : ℝ)*((8153/50000 : ℝ)+(9371/100000 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (34664010427663998153/34675000000000000000 : ℝ)+(320425293323/173375000000000 : ℝ)*((8153/50000 : ℝ)+(9371/100000 : ℝ))=(5000788110768177/5000000000000000 : ℝ) by norm_num, show 1+(58646216688255497/100000000000000000000 : ℝ)+(755300202089491/12500000000000000000 : ℝ)=(4002587544732198857/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58646216688255497/100000000000000000000 : ℝ) ≤ ((34664010427663998153/34675000000000000000 : ℝ)+2*(320425293323/173375000000000 : ℝ)*(8153/50000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (34664010427663998153/34675000000000000000 : ℝ)+2*(320425293323/173375000000000 : ℝ)*(8153/50000 : ℝ)=(5001428961354823/5000000000000000 : ℝ) by norm_num, show 1+2*(58646216688255497/100000000000000000000 : ℝ)=(50058646216688255497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34664010427663998153/34675000000000000000 : ℝ)*(X 1 0+X 2 0)+(320425293323/173375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (9371/100000 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (34664010427663998153/34675000000000000000 : ℝ)) (alpha := (320425293323/173375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34664010427663998153/34675000000000000000 : ℝ)*(X 0 1+X 2 1)+(320425293323/173375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (9371/100000 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (34664010427663998153/34675000000000000000 : ℝ)) (alpha := (320425293323/173375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34664010427663998153/34675000000000000000 : ℝ)*(X 0 2+X 1 2)+(320425293323/173375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (9371/100000 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (34664010427663998153/34675000000000000000 : ℝ)) (alpha := (320425293323/173375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-426241157/2000000000 : ℝ)*X 0 0+(1355612457/2500000000 : ℝ)*X 0 1+(2619075251/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338046029/2500000000 : ℝ)*X 1 0+(-556319779/2500000000 : ℝ)*X 1 1+(2619075253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352184099/10000000000 : ℝ)*X 2 0+(654768827/1250000000 : ℝ)*X 2 1+(-1112639497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353186669/10000000000 : ℝ)*X 0 0+(417125191/1000000000 : ℝ)*X 0 1+(4542879241/10000000000 : ℝ)*X 0 2+(4353186669/10000000000 : ℝ)*X 1 0+(417125191/1000000000 : ℝ)*X 1 1+(4542879241/10000000000 : ℝ)*X 1 2+(4353186669/10000000000 : ℝ)*X 2 0+(417125191/1000000000 : ℝ)*X 2 1+(4542879241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2131221113/10000000000 : ℝ)*X 0 0+(654854209/1250000000 : ℝ)*X 0 1+(2710881427/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305263279/10000000000 : ℝ)*X 1 0+(-408333399/2000000000 : ℝ)*X 1 1+(5421763187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132631617/250000000 : ℝ)*X 2 0+(5421762537/10000000000 : ℝ)*X 2 1+(-1020832989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870643467/2000000000 : ℝ)*X 0 0+(4541502419/10000000000 : ℝ)*X 0 1+(834527177/2000000000 : ℝ)*X 0 2+(870643467/2000000000 : ℝ)*X 1 0+(4541502419/10000000000 : ℝ)*X 1 1+(834527177/2000000000 : ℝ)*X 1 2+(870643467/2000000000 : ℝ)*X 2 0+(4541502419/10000000000 : ℝ)*X 2 1+(834527177/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357932963431895802158695479/86687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (710935481/100000000000000 : ℝ)*(base19) + (593378437/100000000000000 : ℝ)*(base23) + (26847259/50000000000000 : ℝ)*(lower2) + (32219157/100000000000000 : ℝ)*(upper3) + (45249041/50000000000000 : ℝ)*(upper5) + (202921684809073/5000000000000 : ℝ)*(major0) + (202921684809073/5000000000000 : ℝ)*(major1) + (202921684809073/5000000000000 : ℝ)*(major2) + (2712984766103771/50000000000000 : ℝ)*(sp0) + (5425985622321153/100000000000000 : ℝ)*(sp1) + (5425985739878197/100000000000000 : ℝ)*(sp2) + (672718639379489/25000000000000 : ℝ)*(sp3) + (4200262273/25000000000000 : ℝ)*(sp4) + (6363954881/100000000000000 : ℝ)*(sp7) + (1345440460736419/50000000000000 : ℝ)*(f.failure) + (2712993166628317/50000000000000 : ℝ)*(f.sum) + (16634687936409/6935000000000000000000000000 : ℝ)*base65 + (2615128097981317169/173375000000000000000000000000000 : ℝ)*base67 + (1154983086711567169/173375000000000000000000000000000 : ℝ)*base69 + (2325121178546817169/173375000000000000000000000000000 : ℝ)*base71 + (44976427359079/6935000000000000000000000000 : ℝ)*base73 + (1857162453156317169/173375000000000000000000000000000 : ℝ)*base75 + (1277453545023692169/173375000000000000000000000000000 : ℝ)*base77 + (1105432213853317169/173375000000000000000000000000000 : ℝ)*base79 + (46368629219359/6935000000000000000000000000 : ℝ)*base81 + (9253/20000000000000000000 : ℝ)*base89 + (9253/20000000000000000000 : ℝ)*base91 + (9253/20000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8511733648255420362753/6935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74534189/50000000000000 : ℝ)*(base19) + (254735273/12500000000000 : ℝ)*(base23) + (6464923/20000000000000 : ℝ)*(upper2) + (179114317/100000000000000 : ℝ)*(upper3) + (102220321558117/2500000000000 : ℝ)*(major0) + (102220321558117/2500000000000 : ℝ)*(major1) + (102220321558117/2500000000000 : ℝ)*(major2) + (1938062629/50000000000000 : ℝ)*(sp1) + (9465472759/20000000000000 : ℝ)*(sp2) + (3455315651/100000000000000 : ℝ)*(sp3) + (5466602331784057/100000000000000 : ℝ)*(sp4) + (5466598306590421/100000000000000 : ℝ)*(sp5) + (5466552966538077/100000000000000 : ℝ)*(sp6) + (542203979327537/20000000000000 : ℝ)*(sp7) + (338877918994167/12500000000000 : ℝ)*(f.failure) + (5466602331784057/100000000000000 : ℝ)*(f.sum) + (15556897695743/6935000000000000000000000000 : ℝ)*base66 + (573960993491829599/86687500000000000000000000000000 : ℝ)*base68 + (113717556939017099/86687500000000000000000000000000 : ℝ)*base70 + (33795736925420401/86687500000000000000000000000000 : ℝ)*base71 + (6644597322779/3467500000000000000000000000 : ℝ)*base74 + (598446816871045401/86687500000000000000000000000000 : ℝ)*base75 + (74742533161204599/86687500000000000000000000000000 : ℝ)*base78 + (877742403504732901/86687500000000000000000000000000 : ℝ)*base79 + (11173106983247/1733750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (26929/5000000000000000000 : ℝ)*base89 + (26929/5000000000000000000 : ℝ)*base91 + (26929/5000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1211_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1211_s4_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133699577/10000000000 : ℝ)*x 0 + (539877509/1000000000 : ℝ)*x 1 + (1052038381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133699577/10000000000 : ℝ)^2101 ≤ (3242722631909/25000000000000 : ℝ)^1589 := by
    have hnat : (2133699577 : ℕ)^2101*25000000000000^1589 ≤ 3242722631909^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133699577 10000000000 3242722631909 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539877509/1000000000 : ℝ)^2101 ≤ (11065643941189/25000000000000 : ℝ)^1589 := by
    have hnat : (539877509 : ℕ)^2101*25000000000000^1589 ≤ 11065643941189^1589*1000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539877509 1000000000 11065643941189 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052038381/2000000000 : ℝ)^2101 ≤ (21383266849877/50000000000000 : ℝ)^1589 := by
    have hnat : (1052038381 : ℕ)^2101*50000000000000^1589 ≤ 21383266849877^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052038381 2000000000 21383266849877 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133699577/10000000000 : ℝ), (539877509/1000000000 : ℝ), (1052038381/2000000000 : ℝ)] ![(3242722631909/25000000000000 : ℝ), (11065643941189/25000000000000 : ℝ), (21383266849877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133699577/10000000000 : ℝ)|^2101 ≤ (3242722631909/25000000000000 : ℝ)^1589
        have hw : |(-2133699577/10000000000 : ℝ)|=(2133699577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539877509/1000000000 : ℝ)|^2101 ≤ (11065643941189/25000000000000 : ℝ)^1589
        have hw : |(539877509/1000000000 : ℝ)|=(539877509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052038381/2000000000 : ℝ)|^2101 ≤ (21383266849877/50000000000000 : ℝ)^1589
        have hw : |(1052038381/2000000000 : ℝ)|=(1052038381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s4_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673116253/5000000000 : ℝ)*x 0 + (-2204079427/10000000000 : ℝ)*x 1 + (5260191919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673116253/5000000000 : ℝ)^2101 ≤ (21846945209071/50000000000000 : ℝ)^1589 := by
    have hnat : (2673116253 : ℕ)^2101*50000000000000^1589 ≤ 21846945209071^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673116253 5000000000 21846945209071 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204079427/10000000000 : ℝ)^2101 ≤ (1692446965061/12500000000000 : ℝ)^1589 := by
    have hnat : (2204079427 : ℕ)^2101*12500000000000^1589 ≤ 1692446965061^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204079427 10000000000 1692446965061 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260191919/10000000000 : ℝ)^2101 ≤ (42766533850253/100000000000000 : ℝ)^1589 := by
    have hnat : (5260191919 : ℕ)^2101*100000000000000^1589 ≤ 42766533850253^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260191919 10000000000 42766533850253 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673116253/5000000000 : ℝ), (-2204079427/10000000000 : ℝ), (5260191919/10000000000 : ℝ)] ![(21846945209071/50000000000000 : ℝ), (1692446965061/12500000000000 : ℝ), (42766533850253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673116253/5000000000 : ℝ)|^2101 ≤ (21846945209071/50000000000000 : ℝ)^1589
        have hw : |(2673116253/5000000000 : ℝ)|=(2673116253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2204079427/10000000000 : ℝ)|^2101 ≤ (1692446965061/12500000000000 : ℝ)^1589
        have hw : |(-2204079427/10000000000 : ℝ)|=(2204079427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260191919/10000000000 : ℝ)|^2101 ≤ (42766533850253/100000000000000 : ℝ)^1589
        have hw : |(5260191919/10000000000 : ℝ)|=(5260191919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s4_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069246491/2000000000 : ℝ)*x 0 + (5260191981/10000000000 : ℝ)*x 1 + (-2204079413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069246491/2000000000 : ℝ)^2101 ≤ (43693889867023/100000000000000 : ℝ)^1589 := by
    have hnat : (1069246491 : ℕ)^2101*100000000000000^1589 ≤ 43693889867023^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069246491 2000000000 43693889867023 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260191981/10000000000 : ℝ)^2101 ≤ (42766534516747/100000000000000 : ℝ)^1589 := by
    have hnat : (5260191981 : ℕ)^2101*100000000000000^1589 ≤ 42766534516747^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260191981 10000000000 42766534516747 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204079413/10000000000 : ℝ)^2101 ≤ (541583024271/4000000000000 : ℝ)^1589 := by
    have hnat : (2204079413 : ℕ)^2101*4000000000000^1589 ≤ 541583024271^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204079413 10000000000 541583024271 4000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069246491/2000000000 : ℝ), (5260191981/10000000000 : ℝ), (-2204079413/10000000000 : ℝ)] ![(43693889867023/100000000000000 : ℝ), (42766534516747/100000000000000 : ℝ), (541583024271/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069246491/2000000000 : ℝ)|^2101 ≤ (43693889867023/100000000000000 : ℝ)^1589
        have hw : |(1069246491/2000000000 : ℝ)|=(1069246491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260191981/10000000000 : ℝ)|^2101 ≤ (42766534516747/100000000000000 : ℝ)^1589
        have hw : |(5260191981/10000000000 : ℝ)|=(5260191981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204079413/10000000000 : ℝ)|^2101 ≤ (541583024271/4000000000000 : ℝ)^1589
        have hw : |(-2204079413/10000000000 : ℝ)|=(2204079413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s4_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4354679761/10000000000 : ℝ)*x 0 + (421715223/1000000000 : ℝ)*x 1 + (281037253/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354679761/10000000000 : ℝ)^2101 ≤ (16656832697879/50000000000000 : ℝ)^1589 := by
    have hnat : (4354679761 : ℕ)^2101*50000000000000^1589 ≤ 16656832697879^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354679761 10000000000 16656832697879 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421715223/1000000000 : ℝ)^2101 ≤ (31929695658387/100000000000000 : ℝ)^1589 := by
    have hnat : (421715223 : ℕ)^2101*100000000000000^1589 ≤ 31929695658387^1589*1000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421715223 1000000000 31929695658387 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281037253/625000000 : ℝ)^2101 ≤ (8689159733991/25000000000000 : ℝ)^1589 := by
    have hnat : (281037253 : ℕ)^2101*25000000000000^1589 ≤ 8689159733991^1589*625000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281037253 625000000 8689159733991 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354679761/10000000000 : ℝ), (421715223/1000000000 : ℝ), (281037253/625000000 : ℝ)] ![(16656832697879/50000000000000 : ℝ), (31929695658387/100000000000000 : ℝ), (8689159733991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354679761/10000000000 : ℝ)|^2101 ≤ (16656832697879/50000000000000 : ℝ)^1589
        have hw : |(4354679761/10000000000 : ℝ)|=(4354679761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(421715223/1000000000 : ℝ)|^2101 ≤ (31929695658387/100000000000000 : ℝ)^1589
        have hw : |(421715223/1000000000 : ℝ)|=(421715223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281037253/625000000 : ℝ)|^2101 ≤ (8689159733991/25000000000000 : ℝ)^1589
        have hw : |(281037253/625000000 : ℝ)|=(281037253/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s4_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133705703/10000000000 : ℝ)*x 0 + (5260578581/10000000000 : ℝ)*x 1 + (337399193/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133705703/10000000000 : ℝ)^2101 ≤ (1297093976739/10000000000000 : ℝ)^1589 := by
    have hnat : (2133705703 : ℕ)^2101*10000000000000^1589 ≤ 1297093976739^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133705703 10000000000 1297093976739 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260578581/10000000000 : ℝ)^2101 ≤ (668292038737/1562500000000 : ℝ)^1589 := by
    have hnat : (5260578581 : ℕ)^2101*1562500000000^1589 ≤ 668292038737^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260578581 10000000000 668292038737 1562500000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337399193/625000000 : ℝ)^2101 ≤ (8851673946617/20000000000000 : ℝ)^1589 := by
    have hnat : (337399193 : ℕ)^2101*20000000000000^1589 ≤ 8851673946617^1589*625000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337399193 625000000 8851673946617 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133705703/10000000000 : ℝ), (5260578581/10000000000 : ℝ), (337399193/625000000 : ℝ)] ![(1297093976739/10000000000000 : ℝ), (668292038737/1562500000000 : ℝ), (8851673946617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133705703/10000000000 : ℝ)|^2101 ≤ (1297093976739/10000000000000 : ℝ)^1589
        have hw : |(-2133705703/10000000000 : ℝ)|=(2133705703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260578581/10000000000 : ℝ)|^2101 ≤ (668292038737/1562500000000 : ℝ)^1589
        have hw : |(5260578581/10000000000 : ℝ)|=(5260578581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337399193/625000000 : ℝ)|^2101 ≤ (8851673946617/20000000000000 : ℝ)^1589
        have hw : |(337399193/625000000 : ℝ)|=(337399193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s4_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310949039/10000000000 : ℝ)*x 0 + (-1032942459/5000000000 : ℝ)*x 1 + (134959669/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310949039/10000000000 : ℝ)^2101 ≤ (21656507222741/50000000000000 : ℝ)^1589 := by
    have hnat : (5310949039 : ℕ)^2101*50000000000000^1589 ≤ 21656507222741^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310949039 10000000000 21656507222741 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032942459/5000000000 : ℝ)^2101 ≤ (1553577421359/12500000000000 : ℝ)^1589 := by
    have hnat : (1032942459 : ℕ)^2101*12500000000000^1589 ≤ 1553577421359^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032942459 5000000000 1553577421359 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134959669/250000000 : ℝ)^2101 ≤ (4425836617753/10000000000000 : ℝ)^1589 := by
    have hnat : (134959669 : ℕ)^2101*10000000000000^1589 ≤ 4425836617753^1589*250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134959669 250000000 4425836617753 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310949039/10000000000 : ℝ), (-1032942459/5000000000 : ℝ), (134959669/250000000 : ℝ)] ![(21656507222741/50000000000000 : ℝ), (1553577421359/12500000000000 : ℝ), (4425836617753/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310949039/10000000000 : ℝ)|^2101 ≤ (21656507222741/50000000000000 : ℝ)^1589
        have hw : |(5310949039/10000000000 : ℝ)|=(5310949039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1032942459/5000000000 : ℝ)|^2101 ≤ (1553577421359/12500000000000 : ℝ)^1589
        have hw : |(-1032942459/5000000000 : ℝ)|=(1032942459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134959669/250000000 : ℝ)|^2101 ≤ (4425836617753/10000000000000 : ℝ)^1589
        have hw : |(134959669/250000000 : ℝ)|=(134959669/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s4_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062189931/2000000000 : ℝ)*x 0 + (1349596571/2500000000 : ℝ)*x 1 + (-2065884731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062189931/2000000000 : ℝ)^2101 ≤ (8662604217589/20000000000000 : ℝ)^1589 := by
    have hnat : (1062189931 : ℕ)^2101*20000000000000^1589 ≤ 8662604217589^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062189931 2000000000 8662604217589 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349596571/2500000000 : ℝ)^2101 ≤ (44258361017639/100000000000000 : ℝ)^1589 := by
    have hnat : (1349596571 : ℕ)^2101*100000000000000^1589 ≤ 44258361017639^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349596571 2500000000 44258361017639 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065884731/10000000000 : ℝ)^2101 ≤ (77678861771/625000000000 : ℝ)^1589 := by
    have hnat : (2065884731 : ℕ)^2101*625000000000^1589 ≤ 77678861771^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065884731 10000000000 77678861771 625000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062189931/2000000000 : ℝ), (1349596571/2500000000 : ℝ), (-2065884731/10000000000 : ℝ)] ![(8662604217589/20000000000000 : ℝ), (44258361017639/100000000000000 : ℝ), (77678861771/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062189931/2000000000 : ℝ)|^2101 ≤ (8662604217589/20000000000000 : ℝ)^1589
        have hw : |(1062189931/2000000000 : ℝ)|=(1062189931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349596571/2500000000 : ℝ)|^2101 ≤ (44258361017639/100000000000000 : ℝ)^1589
        have hw : |(1349596571/2500000000 : ℝ)|=(1349596571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065884731/10000000000 : ℝ)|^2101 ≤ (77678861771/625000000000 : ℝ)^1589
        have hw : |(-2065884731/10000000000 : ℝ)|=(2065884731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s4_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4354692767/10000000000 : ℝ)*x 0 + (4495815903/10000000000 : ℝ)*x 1 + (1054483871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354692767/10000000000 : ℝ)^2101 ≤ (16656898476129/50000000000000 : ℝ)^1589 := by
    have hnat : (4354692767 : ℕ)^2101*50000000000000^1589 ≤ 16656898476129^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354692767 10000000000 16656898476129 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495815903/10000000000 : ℝ)^2101 ≤ (6949733196451/20000000000000 : ℝ)^1589 := by
    have hnat : (4495815903 : ℕ)^2101*20000000000000^1589 ≤ 6949733196451^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495815903 10000000000 6949733196451 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054483871/2500000000 : ℝ)^2101 ≤ (3193753705231/10000000000000 : ℝ)^1589 := by
    have hnat : (1054483871 : ℕ)^2101*10000000000000^1589 ≤ 3193753705231^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054483871 2500000000 3193753705231 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354692767/10000000000 : ℝ), (4495815903/10000000000 : ℝ), (1054483871/2500000000 : ℝ)] ![(16656898476129/50000000000000 : ℝ), (6949733196451/20000000000000 : ℝ), (3193753705231/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354692767/10000000000 : ℝ)|^2101 ≤ (16656898476129/50000000000000 : ℝ)^1589
        have hw : |(4354692767/10000000000 : ℝ)|=(4354692767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495815903/10000000000 : ℝ)|^2101 ≤ (6949733196451/20000000000000 : ℝ)^1589
        have hw : |(4495815903/10000000000 : ℝ)|=(4495815903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054483871/2500000000 : ℝ)|^2101 ≤ (3193753705231/10000000000000 : ℝ)^1589
        have hw : |(1054483871/2500000000 : ℝ)|=(1054483871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1083/10000 : ℝ) ^ (8403/2048 : ℝ) ≤ (2735232003876407/25000000000000000000 : ℝ) := by
    have hpowers : (1083/10000 : ℝ)^8403 ≤ (2735232003876407/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1083 : ℕ)^8403*25000000000000000000^2048 ≤ 2735232003876407^2048*10000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1083 10000 2735232003876407 25000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1083/10000 : ℝ)) (X := (2735232003876407/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1473/10000 : ℝ) ^ (8403/2048 : ℝ) ≤ (7729352635118097/20000000000000000000 : ℝ) := by
    have hpowers : (1473/10000 : ℝ)^8403 ≤ (7729352635118097/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1473 : ℕ)^8403*20000000000000000000^2048 ≤ 7729352635118097^2048*10000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 10000 7729352635118097 20000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/10000 : ℝ)) (X := (7729352635118097/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502735232003876407/12500000000000000000 : ℝ) ≤ (25001333164749/25000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (12502735232003876407/12500000000000000000 : ℝ)^2048 ≤ (25001333164749/25000000000000 : ℝ)^8403 := by
      have hnat : (12502735232003876407 : ℕ)^2048*25000000000000^8403 ≤ 25001333164749^8403*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502735232003876407 12500000000000000000 25001333164749 25000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25001333164749/25000000000000 : ℝ)) (X := (12502735232003876407/12500000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049587691191096113/100000000000000000000 : ℝ) ≤ (1000120833695547/1000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (100049587691191096113/100000000000000000000 : ℝ)^2048 ≤ (1000120833695547/1000000000000000 : ℝ)^8403 := by
      have hnat : (100049587691191096113 : ℕ)^2048*1000000000000000^8403 ≤ 1000120833695547^8403*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049587691191096113 100000000000000000000 1000120833695547 1000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000120833695547/1000000000000000 : ℝ)) (X := (100049587691191096113/100000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007729352635118097/10000000000000000000 : ℝ) ≤ (500094170400567/500000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (10007729352635118097/10000000000000000000 : ℝ)^2048 ≤ (500094170400567/500000000000000 : ℝ)^8403 := by
      have hnat : (10007729352635118097 : ℕ)^2048*500000000000000^8403 ≤ 500094170400567^8403*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007729352635118097 10000000000000000000 500094170400567 500000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500094170400567/500000000000000 : ℝ)) (X := (10007729352635118097/10000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2735232003876407/25000000000000000000 : ℝ) ≤ ((64979096163230493/65000000000000000 : ℝ)+2*(22502368529/13000000000000 : ℝ)*(1083/10000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (64979096163230493/65000000000000000 : ℝ)+2*(22502368529/13000000000000 : ℝ)*(1083/10000 : ℝ)=(25001333164749/25000000000000 : ℝ) by norm_num, show 1+2*(2735232003876407/25000000000000000000 : ℝ)=(12502735232003876407/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7729352635118097/20000000000000000000 : ℝ)+(2735232003876407/25000000000000000000 : ℝ) ≤ ((64979096163230493/65000000000000000 : ℝ)+(22502368529/13000000000000 : ℝ)*((1473/10000 : ℝ)+(1083/10000 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (64979096163230493/65000000000000000 : ℝ)+(22502368529/13000000000000 : ℝ)*((1473/10000 : ℝ)+(1083/10000 : ℝ))=(1000120833695547/1000000000000000 : ℝ) by norm_num, show 1+(7729352635118097/20000000000000000000 : ℝ)+(2735232003876407/25000000000000000000 : ℝ)=(100049587691191096113/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7729352635118097/20000000000000000000 : ℝ) ≤ ((64979096163230493/65000000000000000 : ℝ)+2*(22502368529/13000000000000 : ℝ)*(1473/10000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (64979096163230493/65000000000000000 : ℝ)+2*(22502368529/13000000000000 : ℝ)*(1473/10000 : ℝ)=(500094170400567/500000000000000 : ℝ) by norm_num, show 1+2*(7729352635118097/20000000000000000000 : ℝ)=(10007729352635118097/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64979096163230493/65000000000000000 : ℝ)*(X 1 0+X 2 0)+(22502368529/13000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (64979096163230493/65000000000000000 : ℝ)) (alpha := (22502368529/13000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64979096163230493/65000000000000000 : ℝ)*(X 0 1+X 2 1)+(22502368529/13000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (64979096163230493/65000000000000000 : ℝ)) (alpha := (22502368529/13000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64979096163230493/65000000000000000 : ℝ)*(X 0 2+X 1 2)+(22502368529/13000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (64979096163230493/65000000000000000 : ℝ)) (alpha := (22502368529/13000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2133699577/10000000000 : ℝ)*X 0 0+(539877509/1000000000 : ℝ)*X 0 1+(1052038381/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673116253/5000000000 : ℝ)*X 1 0+(-2204079427/10000000000 : ℝ)*X 1 1+(5260191919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069246491/2000000000 : ℝ)*X 2 0+(5260191981/10000000000 : ℝ)*X 2 1+(-2204079413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354679761/10000000000 : ℝ)*X 0 0+(421715223/1000000000 : ℝ)*X 0 1+(281037253/625000000 : ℝ)*X 0 2+(4354679761/10000000000 : ℝ)*X 1 0+(421715223/1000000000 : ℝ)*X 1 1+(281037253/625000000 : ℝ)*X 1 2+(4354679761/10000000000 : ℝ)*X 2 0+(421715223/1000000000 : ℝ)*X 2 1+(281037253/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133705703/10000000000 : ℝ)*X 0 0+(5260578581/10000000000 : ℝ)*X 0 1+(337399193/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310949039/10000000000 : ℝ)*X 1 0+(-1032942459/5000000000 : ℝ)*X 1 1+(134959669/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062189931/2000000000 : ℝ)*X 2 0+(1349596571/2500000000 : ℝ)*X 2 1+(-2065884731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354692767/10000000000 : ℝ)*X 0 0+(4495815903/10000000000 : ℝ)*X 0 1+(1054483871/2500000000 : ℝ)*X 0 2+(4354692767/10000000000 : ℝ)*X 1 0+(4495815903/10000000000 : ℝ)*X 1 1+(1054483871/2500000000 : ℝ)*X 1 2+(4354692767/10000000000 : ℝ)*X 2 0+(4495815903/10000000000 : ℝ)*X 2 1+(1054483871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3934226517737845932081/650000000000000000000000000 : ℝ) := by norm_num
    linear_combination (598743757/50000000000000 : ℝ)*(base19) + (558929/62500000000 : ℝ)*(base23) + (125297043/100000000000000 : ℝ)*(lower2) + (171024993/100000000000000 : ℝ)*(upper3) + (543043/12500000000000 : ℝ)*(upper5) + (5397256384186779/100000000000000 : ℝ)*(major0) + (5397256384186779/100000000000000 : ℝ)*(major1) + (5397256384186779/100000000000000 : ℝ)*(major2) + (7215916796368059/100000000000000 : ℝ)*(sp0) + (450996564101551/6250000000000 : ℝ)*(sp1) + (721594532882593/10000000000000 : ℝ)*(sp2) + (447318697760663/12500000000000 : ℝ)*(sp3) + (2942674427/10000000000000 : ℝ)*(sp4) + (4190355177/25000000000000 : ℝ)*(sp7) + (894641585876503/25000000000000 : ℝ)*(f.failure) + (721594622311233/10000000000000 : ℝ)*(f.sum) + (1239677935541/650000000000000000000000000 : ℝ)*base65 + (50968116974707047/6500000000000000000000000000000 : ℝ)*base67 + (29996864492792953/6500000000000000000000000000000 : ℝ)*base70 + (75574894936707047/6500000000000000000000000000000 : ℝ)*base71 + (2593161050291/650000000000000000000000000 : ℝ)*base73 + (86226503861292953/6500000000000000000000000000000 : ℝ)*base76 + (12186314785707047/6500000000000000000000000000000 : ℝ)*base77 + (146654868000292953/6500000000000000000000000000000 : ℝ)*base80 + (3002781064991/650000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (34639/10000000000000000000 : ℝ)*base90 + (34639/10000000000000000000 : ℝ)*base92 + (34639/10000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2540246349023572171287/325000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32369769/100000000000000 : ℝ)*(base19) + (896107951/50000000000000 : ℝ)*(base23) + (18670891/5000000000000 : ℝ)*(lower4) + (2082547/6250000000000 : ℝ)*(upper5) + (2713789235221201/50000000000000 : ℝ)*(major0) + (2713789235221201/50000000000000 : ℝ)*(major1) + (2713789235221201/50000000000000 : ℝ)*(major2) + (19191528993/100000000000000 : ℝ)*(sp0) + (3046442893/100000000000000 : ℝ)*(sp1) + (17710752497/50000000000000 : ℝ)*(sp2) + (7256466560757003/100000000000000 : ℝ)*(sp4) + (3628241336736667/50000000000000 : ℝ)*(sp5) + (7256448538565101/100000000000000 : ℝ)*(sp6) + (899667732015177/25000000000000 : ℝ)*(sp7) + (899667732015177/25000000000000 : ℝ)*(f.failure) + (7256485752285997/100000000000000 : ℝ)*(f.sum) + (784398380621/325000000000000000000000000 : ℝ)*base66 + (45981352099677093/3250000000000000000000000000000 : ℝ)*base67 + (10799284683322907/3250000000000000000000000000000 : ℝ)*base70 + (22683309529927093/3250000000000000000000000000000 : ℝ)*base71 + (178186036749/81250000000000000000000000 : ℝ)*base74 + (13659481561822907/3250000000000000000000000000000 : ℝ)*base76 + (6466899771677093/3250000000000000000000000000000 : ℝ)*base77 + (16161867626572907/3250000000000000000000000000000 : ℝ)*base80 + (387309027327/162500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (113201/10000000000000000000 : ℝ)*base90 + (113201/10000000000000000000 : ℝ)*base92 + (113201/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1211_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1211_s5_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067099859/5000000000 : ℝ)*x 0 + (5393161989/10000000000 : ℝ)*x 1 + (5265476457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067099859/5000000000 : ℝ)^2101 ≤ (3243727681623/25000000000000 : ℝ)^1589 := by
    have hnat : (1067099859 : ℕ)^2101*25000000000000^1589 ≤ 3243727681623^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067099859 5000000000 3243727681623 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393161989/10000000000 : ℝ)^2101 ≤ (8840347587629/20000000000000 : ℝ)^1589 := by
    have hnat : (5393161989 : ℕ)^2101*20000000000000^1589 ≤ 8840347587629^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393161989 10000000000 8840347587629 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265476457/10000000000 : ℝ)^2101 ≤ (8564670264641/20000000000000 : ℝ)^1589 := by
    have hnat : (5265476457 : ℕ)^2101*20000000000000^1589 ≤ 8564670264641^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265476457 10000000000 8564670264641 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067099859/5000000000 : ℝ), (5393161989/10000000000 : ℝ), (5265476457/10000000000 : ℝ)] ![(3243727681623/25000000000000 : ℝ), (8840347587629/20000000000000 : ℝ), (8564670264641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067099859/5000000000 : ℝ)|^2101 ≤ (3243727681623/25000000000000 : ℝ)^1589
        have hw : |(-1067099859/5000000000 : ℝ)|=(1067099859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393161989/10000000000 : ℝ)|^2101 ≤ (8840347587629/20000000000000 : ℝ)^1589
        have hw : |(5393161989/10000000000 : ℝ)|=(5393161989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265476457/10000000000 : ℝ)|^2101 ≤ (8564670264641/20000000000000 : ℝ)^1589
        have hw : |(5265476457/10000000000 : ℝ)|=(5265476457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s5_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672408121/5000000000 : ℝ)*x 0 + (-1099483229/5000000000 : ℝ)*x 1 + (658184557/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672408121/5000000000 : ℝ)^2101 ≤ (4367858656789/10000000000000 : ℝ)^1589 := by
    have hnat : (2672408121 : ℕ)^2101*10000000000000^1589 ≤ 4367858656789^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672408121 5000000000 4367858656789 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099483229/5000000000 : ℝ)^2101 ≤ (6749031045569/50000000000000 : ℝ)^1589 := by
    have hnat : (1099483229 : ℕ)^2101*50000000000000^1589 ≤ 6749031045569^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099483229 5000000000 6749031045569 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658184557/1250000000 : ℝ)^2101 ≤ (42823351312451/100000000000000 : ℝ)^1589 := by
    have hnat : (658184557 : ℕ)^2101*100000000000000^1589 ≤ 42823351312451^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658184557 1250000000 42823351312451 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672408121/5000000000 : ℝ), (-1099483229/5000000000 : ℝ), (658184557/1250000000 : ℝ)] ![(4367858656789/10000000000000 : ℝ), (6749031045569/50000000000000 : ℝ), (42823351312451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672408121/5000000000 : ℝ)|^2101 ≤ (4367858656789/10000000000000 : ℝ)^1589
        have hw : |(2672408121/5000000000 : ℝ)|=(2672408121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1099483229/5000000000 : ℝ)|^2101 ≤ (6749031045569/50000000000000 : ℝ)^1589
        have hw : |(-1099483229/5000000000 : ℝ)|=(1099483229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658184557/1250000000 : ℝ)|^2101 ≤ (42823351312451/100000000000000 : ℝ)^1589
        have hw : |(658184557/1250000000 : ℝ)|=(658184557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s5_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668102031/1250000000 : ℝ)*x 0 + (1316369113/2500000000 : ℝ)*x 1 + (-2198966457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668102031/1250000000 : ℝ)^2101 ≤ (21839293316361/50000000000000 : ℝ)^1589 := by
    have hnat : (668102031 : ℕ)^2101*50000000000000^1589 ≤ 21839293316361^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668102031 1250000000 21839293316361 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316369113/2500000000 : ℝ)^2101 ≤ (21411675634719/50000000000000 : ℝ)^1589 := by
    have hnat : (1316369113 : ℕ)^2101*50000000000000^1589 ≤ 21411675634719^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316369113 2500000000 21411675634719 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198966457/10000000000 : ℝ)^2101 ≤ (6749031041511/50000000000000 : ℝ)^1589 := by
    have hnat : (2198966457 : ℕ)^2101*50000000000000^1589 ≤ 6749031041511^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198966457 10000000000 6749031041511 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668102031/1250000000 : ℝ), (1316369113/2500000000 : ℝ), (-2198966457/10000000000 : ℝ)] ![(21839293316361/50000000000000 : ℝ), (21411675634719/50000000000000 : ℝ), (6749031041511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668102031/1250000000 : ℝ)|^2101 ≤ (21839293316361/50000000000000 : ℝ)^1589
        have hw : |(668102031/1250000000 : ℝ)|=(668102031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316369113/2500000000 : ℝ)|^2101 ≤ (21411675634719/50000000000000 : ℝ)^1589
        have hw : |(1316369113/2500000000 : ℝ)|=(1316369113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198966457/10000000000 : ℝ)|^2101 ≤ (6749031041511/50000000000000 : ℝ)^1589
        have hw : |(-2198966457/10000000000 : ℝ)|=(2198966457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s5_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1088743331/2500000000 : ℝ)*x 0 + (2114050831/5000000000 : ℝ)*x 1 + (2242785633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088743331/2500000000 : ℝ)^2101 ≤ (33316634834603/100000000000000 : ℝ)^1589 := by
    have hnat : (1088743331 : ℕ)^2101*100000000000000^1589 ≤ 33316634834603^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088743331 2500000000 33316634834603 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114050831/5000000000 : ℝ)^2101 ≤ (32039356296287/100000000000000 : ℝ)^1589 := by
    have hnat : (2114050831 : ℕ)^2101*100000000000000^1589 ≤ 32039356296287^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114050831 5000000000 32039356296287 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242785633/5000000000 : ℝ)^2101 ≤ (8661002214397/25000000000000 : ℝ)^1589 := by
    have hnat : (2242785633 : ℕ)^2101*25000000000000^1589 ≤ 8661002214397^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242785633 5000000000 8661002214397 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088743331/2500000000 : ℝ), (2114050831/5000000000 : ℝ), (2242785633/5000000000 : ℝ)] ![(33316634834603/100000000000000 : ℝ), (32039356296287/100000000000000 : ℝ), (8661002214397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088743331/2500000000 : ℝ)|^2101 ≤ (33316634834603/100000000000000 : ℝ)^1589
        have hw : |(1088743331/2500000000 : ℝ)|=(1088743331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114050831/5000000000 : ℝ)|^2101 ≤ (32039356296287/100000000000000 : ℝ)^1589
        have hw : |(2114050831/5000000000 : ℝ)|=(2114050831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242785633/5000000000 : ℝ)|^2101 ≤ (8661002214397/25000000000000 : ℝ)^1589
        have hw : |(2242785633/5000000000 : ℝ)|=(2242785633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s5_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-213420407/1000000000 : ℝ)*x 0 + (5265805349/10000000000 : ℝ)*x 1 + (674104049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213420407/1000000000 : ℝ)^2101 ≤ (1297494570977/10000000000000 : ℝ)^1589 := by
    have hnat : (213420407 : ℕ)^2101*10000000000000^1589 ≤ 1297494570977^1589*1000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213420407 1000000000 1297494570977 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265805349/10000000000 : ℝ)^2101 ≤ (42826888060579/100000000000000 : ℝ)^1589 := by
    have hnat : (5265805349 : ℕ)^2101*100000000000000^1589 ≤ 42826888060579^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265805349 10000000000 42826888060579 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674104049/1250000000 : ℝ)^2101 ≤ (22099083110701/50000000000000 : ℝ)^1589 := by
    have hnat : (674104049 : ℕ)^2101*50000000000000^1589 ≤ 22099083110701^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674104049 1250000000 22099083110701 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213420407/1000000000 : ℝ), (5265805349/10000000000 : ℝ), (674104049/1250000000 : ℝ)] ![(1297494570977/10000000000000 : ℝ), (42826888060579/100000000000000 : ℝ), (22099083110701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213420407/1000000000 : ℝ)|^2101 ≤ (1297494570977/10000000000000 : ℝ)^1589
        have hw : |(-213420407/1000000000 : ℝ)|=(213420407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265805349/10000000000 : ℝ)|^2101 ≤ (42826888060579/100000000000000 : ℝ)^1589
        have hw : |(5265805349/10000000000 : ℝ)|=(5265805349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674104049/1250000000 : ℝ)|^2101 ≤ (22099083110701/50000000000000 : ℝ)^1589
        have hw : |(674104049/1250000000 : ℝ)|=(674104049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s5_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312306059/10000000000 : ℝ)*x 0 + (-414322149/2000000000 : ℝ)*x 1 + (5392832323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312306059/10000000000 : ℝ)^2101 ≤ (2166382404593/5000000000000 : ℝ)^1589 := by
    have hnat : (5312306059 : ℕ)^2101*5000000000000^1589 ≤ 2166382404593^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312306059 10000000000 2166382404593 5000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414322149/2000000000 : ℝ)^2101 ≤ (12474186419467/100000000000000 : ℝ)^1589 := by
    have hnat : (414322149 : ℕ)^2101*100000000000000^1589 ≤ 12474186419467^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414322149 2000000000 12474186419467 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392832323/10000000000 : ℝ)^2101 ≤ (44198165473683/100000000000000 : ℝ)^1589 := by
    have hnat : (5392832323 : ℕ)^2101*100000000000000^1589 ≤ 44198165473683^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392832323 10000000000 44198165473683 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312306059/10000000000 : ℝ), (-414322149/2000000000 : ℝ), (5392832323/10000000000 : ℝ)] ![(2166382404593/5000000000000 : ℝ), (12474186419467/100000000000000 : ℝ), (44198165473683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312306059/10000000000 : ℝ)|^2101 ≤ (2166382404593/5000000000000 : ℝ)^1589
        have hw : |(5312306059/10000000000 : ℝ)|=(5312306059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414322149/2000000000 : ℝ)|^2101 ≤ (12474186419467/100000000000000 : ℝ)^1589
        have hw : |(-414322149/2000000000 : ℝ)|=(414322149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392832323/10000000000 : ℝ)|^2101 ≤ (44198165473683/100000000000000 : ℝ)^1589
        have hw : |(5392832323/10000000000 : ℝ)|=(5392832323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s5_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062461261/2000000000 : ℝ)*x 0 + (5392832299/10000000000 : ℝ)*x 1 + (-414322089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062461261/2000000000 : ℝ)^2101 ≤ (173310602979/400000000000 : ℝ)^1589 := by
    have hnat : (1062461261 : ℕ)^2101*400000000000^1589 ≤ 173310602979^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062461261 2000000000 173310602979 400000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392832299/10000000000 : ℝ)^2101 ≤ (22099082606803/50000000000000 : ℝ)^1589 := by
    have hnat : (5392832299 : ℕ)^2101*50000000000000^1589 ≤ 22099082606803^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392832299 10000000000 22099082606803 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414322089/2000000000 : ℝ)^2101 ≤ (2494836806191/20000000000000 : ℝ)^1589 := by
    have hnat : (414322089 : ℕ)^2101*20000000000000^1589 ≤ 2494836806191^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414322089 2000000000 2494836806191 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062461261/2000000000 : ℝ), (5392832299/10000000000 : ℝ), (-414322089/2000000000 : ℝ)] ![(173310602979/400000000000 : ℝ), (22099082606803/50000000000000 : ℝ), (2494836806191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062461261/2000000000 : ℝ)|^2101 ≤ (173310602979/400000000000 : ℝ)^1589
        have hw : |(1062461261/2000000000 : ℝ)|=(1062461261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392832299/10000000000 : ℝ)|^2101 ≤ (22099082606803/50000000000000 : ℝ)^1589
        have hw : |(5392832299/10000000000 : ℝ)|=(5392832299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414322089/2000000000 : ℝ)|^2101 ≤ (2494836806191/20000000000000 : ℝ)^1589
        have hw : |(-414322089/2000000000 : ℝ)|=(414322089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s5_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4354983169/10000000000 : ℝ)*x 0 + (4484908931/10000000000 : ℝ)*x 1 + (4228766761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354983169/10000000000 : ℝ)^2101 ≤ (16658367209771/50000000000000 : ℝ)^1589 := by
    have hnat : (4354983169 : ℕ)^2101*50000000000000^1589 ≤ 16658367209771^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354983169 10000000000 16658367209771 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484908931/10000000000 : ℝ)^2101 ≤ (692744904531/2000000000000 : ℝ)^1589 := by
    have hnat : (4484908931 : ℕ)^2101*2000000000000^1589 ≤ 692744904531^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484908931 10000000000 692744904531 2000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228766761/10000000000 : ℝ)^2101 ≤ (32046020339687/100000000000000 : ℝ)^1589 := by
    have hnat : (4228766761 : ℕ)^2101*100000000000000^1589 ≤ 32046020339687^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228766761 10000000000 32046020339687 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354983169/10000000000 : ℝ), (4484908931/10000000000 : ℝ), (4228766761/10000000000 : ℝ)] ![(16658367209771/50000000000000 : ℝ), (692744904531/2000000000000 : ℝ), (32046020339687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354983169/10000000000 : ℝ)|^2101 ≤ (16658367209771/50000000000000 : ℝ)^1589
        have hw : |(4354983169/10000000000 : ℝ)|=(4354983169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484908931/10000000000 : ℝ)|^2101 ≤ (692744904531/2000000000000 : ℝ)^1589
        have hw : |(4484908931/10000000000 : ℝ)|=(4484908931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228766761/10000000000 : ℝ)|^2101 ≤ (32046020339687/100000000000000 : ℝ)^1589
        have hw : |(4228766761/10000000000 : ℝ)|=(4228766761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (11413/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (113/1000 : ℝ) ^ (8403/2048 : ℝ) ≤ (1302431709658759/10000000000000000000 : ℝ) := by
    have hpowers : (113/1000 : ℝ)^8403 ≤ (1302431709658759/10000000000000000000 : ℝ)^2048 := by
      have hnat : (113 : ℕ)^8403*10000000000000000000^2048 ≤ 1302431709658759^2048*1000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1000 1302431709658759 10000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1000 : ℝ)) (X := (1302431709658759/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8403/2048 : ℝ) ≤ (16794711945856417/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8403 ≤ (16794711945856417/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8403*50000000000000000000^2048 ≤ 16794711945856417^2048*20000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 16794711945856417 50000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (16794711945856417/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001302431709658759/5000000000000000000 : ℝ) ≤ (2000126960249651/2000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (5001302431709658759/5000000000000000000 : ℝ)^2048 ≤ (2000126960249651/2000000000000000 : ℝ)^8403 := by
      have hnat : (5001302431709658759 : ℕ)^2048*2000000000000000^8403 ≤ 2000126960249651^8403*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001302431709658759 5000000000000000000 2000126960249651 2000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000126960249651/2000000000000000 : ℝ)) (X := (5001302431709658759/5000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505826717623537553/12500000000000000000 : ℝ) ≤ (10001135881459511/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (12505826717623537553/12500000000000000000 : ℝ)^2048 ≤ (10001135881459511/10000000000000000 : ℝ)^8403 := by
      have hnat : (12505826717623537553 : ℕ)^2048*10000000000000000^8403 ≤ 10001135881459511^8403*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505826717623537553 12500000000000000000 10001135881459511 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001135881459511/10000000000000000 : ℝ)) (X := (12505826717623537553/12500000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016794711945856417/25000000000000000000 : ℝ) ≤ (10001636961670767/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (25016794711945856417/25000000000000000000 : ℝ)^2048 ≤ (10001636961670767/10000000000000000 : ℝ)^8403 := by
      have hnat : (25016794711945856417 : ℕ)^2048*10000000000000000^8403 ≤ 10001636961670767^8403*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016794711945856417 25000000000000000000 10001636961670767 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001636961670767/10000000000000000 : ℝ)) (X := (25016794711945856417/25000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1302431709658759/10000000000000000000 : ℝ) ≤ ((1173621549155569713/1174000000000000000 : ℝ)+2*(62635026407/36687500000000 : ℝ)*(113/1000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (1173621549155569713/1174000000000000000 : ℝ)+2*(62635026407/36687500000000 : ℝ)*(113/1000 : ℝ)=(2000126960249651/2000000000000000 : ℝ) by norm_num, show 1+2*(1302431709658759/10000000000000000000 : ℝ)=(5001302431709658759/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16794711945856417/50000000000000000000 : ℝ)+(1302431709658759/10000000000000000000 : ℝ) ≤ ((1173621549155569713/1174000000000000000 : ℝ)+(62635026407/36687500000000 : ℝ)*((2847/20000 : ℝ)+(113/1000 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (1173621549155569713/1174000000000000000 : ℝ)+(62635026407/36687500000000 : ℝ)*((2847/20000 : ℝ)+(113/1000 : ℝ))=(10001135881459511/10000000000000000 : ℝ) by norm_num, show 1+(16794711945856417/50000000000000000000 : ℝ)+(1302431709658759/10000000000000000000 : ℝ)=(12505826717623537553/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16794711945856417/50000000000000000000 : ℝ) ≤ ((1173621549155569713/1174000000000000000 : ℝ)+2*(62635026407/36687500000000 : ℝ)*(2847/20000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (1173621549155569713/1174000000000000000 : ℝ)+2*(62635026407/36687500000000 : ℝ)*(2847/20000 : ℝ)=(10001636961670767/10000000000000000 : ℝ) by norm_num, show 1+2*(16794711945856417/50000000000000000000 : ℝ)=(25016794711945856417/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1173621549155569713/1174000000000000000 : ℝ)*(X 1 0+X 2 0)+(62635026407/36687500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1173621549155569713/1174000000000000000 : ℝ)) (alpha := (62635026407/36687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1173621549155569713/1174000000000000000 : ℝ)*(X 0 1+X 2 1)+(62635026407/36687500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1173621549155569713/1174000000000000000 : ℝ)) (alpha := (62635026407/36687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1173621549155569713/1174000000000000000 : ℝ)*(X 0 2+X 1 2)+(62635026407/36687500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1173621549155569713/1174000000000000000 : ℝ)) (alpha := (62635026407/36687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1067099859/5000000000 : ℝ)*X 0 0+(5393161989/10000000000 : ℝ)*X 0 1+(5265476457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672408121/5000000000 : ℝ)*X 1 0+(-1099483229/5000000000 : ℝ)*X 1 1+(658184557/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668102031/1250000000 : ℝ)*X 2 0+(1316369113/2500000000 : ℝ)*X 2 1+(-2198966457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088743331/2500000000 : ℝ)*X 0 0+(2114050831/5000000000 : ℝ)*X 0 1+(2242785633/5000000000 : ℝ)*X 0 2+(1088743331/2500000000 : ℝ)*X 1 0+(2114050831/5000000000 : ℝ)*X 1 1+(2242785633/5000000000 : ℝ)*X 1 2+(1088743331/2500000000 : ℝ)*X 2 0+(2114050831/5000000000 : ℝ)*X 2 1+(2242785633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213420407/1000000000 : ℝ)*X 0 0+(5265805349/10000000000 : ℝ)*X 0 1+(674104049/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312306059/10000000000 : ℝ)*X 1 0+(-414322149/2000000000 : ℝ)*X 1 1+(5392832323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062461261/2000000000 : ℝ)*X 2 0+(5392832299/10000000000 : ℝ)*X 2 1+(-414322089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354983169/10000000000 : ℝ)*X 0 0+(4484908931/10000000000 : ℝ)*X 0 1+(4228766761/10000000000 : ℝ)*X 0 2+(4354983169/10000000000 : ℝ)*X 1 0+(4484908931/10000000000 : ℝ)*X 1 1+(4228766761/10000000000 : ℝ)*X 1 2+(4354983169/10000000000 : ℝ)*X 2 0+(4484908931/10000000000 : ℝ)*X 2 1+(4228766761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16012615927774187051320659/7337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104894513/25000000000000 : ℝ)*(base19) + (101830619/25000000000000 : ℝ)*(base23) + (11249441/100000000000000 : ℝ)*(lower2) + (24870361/50000000000000 : ℝ)*(upper3) + (964391/2500000000000 : ℝ)*(upper5) + (1464466249632819/25000000000000 : ℝ)*(major0) + (1464466249632819/25000000000000 : ℝ)*(major1) + (1464466249632819/25000000000000 : ℝ)*(major2) + (3915876309844329/50000000000000 : ℝ)*(sp0) + (3915881915501491/50000000000000 : ℝ)*(sp1) + (3915881921629279/50000000000000 : ℝ)*(sp2) + (242747465635377/6250000000000 : ℝ)*(sp3) + (11630892377/100000000000000 : ℝ)*(sp4) + (622357219/10000000000000 : ℝ)*(sp7) + (1941982836869111/50000000000000 : ℝ)*(f.failure) + (3915882125290517/50000000000000 : ℝ)*(f.sum) + (485148141739/3668750000000000000000000000 : ℝ)*base65 + (51161923595716947/29350000000000000000000000000000 : ℝ)*base67 + (282366719324666947/29350000000000000000000000000000 : ℝ)*base69 + (139587093230833053/29350000000000000000000000000000 : ℝ)*base72 + (31701893861997/7337500000000000000000000000 : ℝ)*base74 + (204108134610966947/29350000000000000000000000000000 : ℝ)*base75 + (602398025450166947/29350000000000000000000000000000 : ℝ)*base77 + (629165242238366947/29350000000000000000000000000000 : ℝ)*base79 + (884095198173/114648437500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (167857/20000000000000000000 : ℝ)*base89 + (167857/20000000000000000000 : ℝ)*base91 + (167857/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152807605000131441195869901/29350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1413361/800000000000 : ℝ)*(base8) + (277569259/100000000000000 : ℝ)*(lower2) + (5389539/25000000000000 : ℝ)*(lower3) + (33737929/100000000000000 : ℝ)*(lower4) + (4717679/2500000000000 : ℝ)*(lower5) + (2944108380508453/50000000000000 : ℝ)*(major0) + (2944108380508453/50000000000000 : ℝ)*(major1) + (2944108380508453/50000000000000 : ℝ)*(major2) + (4908625323/100000000000000 : ℝ)*(sp1) + (4068276673/20000000000000 : ℝ)*(sp2) + (7872343237164671/100000000000000 : ℝ)*(sp4) + (7872338505209473/100000000000000 : ℝ)*(sp5) + (7872323072451431/100000000000000 : ℝ)*(sp6) + (3904089934652599/100000000000000 : ℝ)*(sp7) + (3904089934652599/100000000000000 : ℝ)*(f.failure) + (1574468682766959/20000000000000 : ℝ)*(f.sum) + (99126985461239/14675000000000000000000000000 : ℝ)*base66 + (203334171162444011/58700000000000000000000000000000 : ℝ)*base68 + (941615695112544011/58700000000000000000000000000000 : ℝ)*base70 + (233800202329644011/58700000000000000000000000000000 : ℝ)*base72 + (6716870603843/7337500000000000000000000000 : ℝ)*base73 + (1144439928767044011/58700000000000000000000000000000 : ℝ)*base76 + (5282674894377044011/58700000000000000000000000000000 : ℝ)*base78 + (413008555991444011/58700000000000000000000000000000 : ℝ)*base80 + (33194880988389/14675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (92913/40000000000000000000 : ℝ)*base89 + (92913/40000000000000000000 : ℝ)*base91 + (92913/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1211_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1211_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1211_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1211_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1211_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1211_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
