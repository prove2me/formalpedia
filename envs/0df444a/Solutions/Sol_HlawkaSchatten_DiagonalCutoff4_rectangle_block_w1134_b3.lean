-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:02.276715+00:00
-- url     : https://prove2.me/submissions/f43213cd-a0bd-4def-8f3b-e0afea13bebf

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
theorem support_rectangle_w1134_s9_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085361079/5000000000 : ℝ)*x 0 + (5393125999/10000000000 : ℝ)*x 1 + (5265658423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085361079/5000000000 : ℝ)^8327 ≤ (2637890136497/20000000000000 : ℝ)^6279 := by
    have hnat : (1085361079 : ℕ)^8327*20000000000000^6279 ≤ 2637890136497^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085361079 5000000000 2637890136497 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393125999/10000000000 : ℝ)^8327 ≤ (8818727343307/20000000000000 : ℝ)^6279 := by
    have hnat : (5393125999 : ℕ)^8327*20000000000000^6279 ≤ 8818727343307^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393125999 10000000000 8818727343307 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265658423/10000000000 : ℝ)^8327 ≤ (42716912581123/100000000000000 : ℝ)^6279 := by
    have hnat : (5265658423 : ℕ)^8327*100000000000000^6279 ≤ 42716912581123^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265658423 10000000000 42716912581123 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085361079/5000000000 : ℝ), (5393125999/10000000000 : ℝ), (5265658423/10000000000 : ℝ)] ![(2637890136497/20000000000000 : ℝ), (8818727343307/20000000000000 : ℝ), (42716912581123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085361079/5000000000 : ℝ)|^8327 ≤ (2637890136497/20000000000000 : ℝ)^6279
        have hw : |(-1085361079/5000000000 : ℝ)|=(1085361079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393125999/10000000000 : ℝ)|^8327 ≤ (8818727343307/20000000000000 : ℝ)^6279
        have hw : |(5393125999/10000000000 : ℝ)|=(5393125999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265658423/10000000000 : ℝ)|^8327 ≤ (42716912581123/100000000000000 : ℝ)^6279
        have hw : |(5265658423/10000000000 : ℝ)|=(5265658423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s9_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344773723/10000000000 : ℝ)*x 0 + (-2235377227/10000000000 : ℝ)*x 1 + (1316414603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344773723/10000000000 : ℝ)^8327 ≤ (21785070211403/50000000000000 : ℝ)^6279 := by
    have hnat : (5344773723 : ℕ)^8327*50000000000000^6279 ≤ 21785070211403^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344773723 10000000000 21785070211403 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235377227/10000000000 : ℝ)^8327 ≤ (13712947096943/100000000000000 : ℝ)^6279 := by
    have hnat : (2235377227 : ℕ)^8327*100000000000000^6279 ≤ 13712947096943^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235377227 10000000000 13712947096943 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316414603/2500000000 : ℝ)^8327 ≤ (42716912462781/100000000000000 : ℝ)^6279 := by
    have hnat : (1316414603 : ℕ)^8327*100000000000000^6279 ≤ 42716912462781^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316414603 2500000000 42716912462781 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344773723/10000000000 : ℝ), (-2235377227/10000000000 : ℝ), (1316414603/2500000000 : ℝ)] ![(21785070211403/50000000000000 : ℝ), (13712947096943/100000000000000 : ℝ), (42716912462781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344773723/10000000000 : ℝ)|^8327 ≤ (21785070211403/50000000000000 : ℝ)^6279
        have hw : |(5344773723/10000000000 : ℝ)|=(5344773723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235377227/10000000000 : ℝ)|^8327 ≤ (13712947096943/100000000000000 : ℝ)^6279
        have hw : |(-2235377227/10000000000 : ℝ)|=(2235377227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316414603/2500000000 : ℝ)|^8327 ≤ (42716912462781/100000000000000 : ℝ)^6279
        have hw : |(1316414603/2500000000 : ℝ)|=(1316414603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s9_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344773743/10000000000 : ℝ)*x 0 + (1316414599/2500000000 : ℝ)*x 1 + (-1117688611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344773743/10000000000 : ℝ)^8327 ≤ (21785070319511/50000000000000 : ℝ)^6279 := by
    have hnat : (5344773743 : ℕ)^8327*50000000000000^6279 ≤ 21785070319511^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344773743 10000000000 21785070319511 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316414599/2500000000 : ℝ)^8327 ≤ (5339614036331/12500000000000 : ℝ)^6279 := by
    have hnat : (1316414599 : ℕ)^8327*12500000000000^6279 ≤ 5339614036331^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316414599 2500000000 5339614036331 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117688611/5000000000 : ℝ)^8327 ≤ (6856473528133/50000000000000 : ℝ)^6279 := by
    have hnat : (1117688611 : ℕ)^8327*50000000000000^6279 ≤ 6856473528133^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117688611 5000000000 6856473528133 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344773743/10000000000 : ℝ), (1316414599/2500000000 : ℝ), (-1117688611/5000000000 : ℝ)] ![(21785070319511/50000000000000 : ℝ), (5339614036331/12500000000000 : ℝ), (6856473528133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344773743/10000000000 : ℝ)|^8327 ≤ (21785070319511/50000000000000 : ℝ)^6279
        have hw : |(5344773743/10000000000 : ℝ)|=(5344773743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316414599/2500000000 : ℝ)|^8327 ≤ (5339614036331/12500000000000 : ℝ)^6279
        have hw : |(1316414599/2500000000 : ℝ)|=(1316414599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117688611/5000000000 : ℝ)|^8327 ≤ (6856473528133/50000000000000 : ℝ)^6279
        have hw : |(-1117688611/5000000000 : ℝ)|=(1117688611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s9_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873160779/2000000000 : ℝ)*x 0 + (1060259021/2500000000 : ℝ)*x 1 + (4494231677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873160779/2000000000 : ℝ)^8327 ≤ (6663389437047/20000000000000 : ℝ)^6279 := by
    have hnat : (873160779 : ℕ)^8327*20000000000000^6279 ≤ 6663389437047^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873160779 2000000000 6663389437047 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060259021/2500000000 : ℝ)^8327 ≤ (8015041573357/25000000000000 : ℝ)^6279 := by
    have hnat : (1060259021 : ℕ)^8327*25000000000000^6279 ≤ 8015041573357^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060259021 2500000000 8015041573357 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494231677/10000000000 : ℝ)^8327 ≤ (1384915460443/4000000000000 : ℝ)^6279 := by
    have hnat : (4494231677 : ℕ)^8327*4000000000000^6279 ≤ 1384915460443^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494231677 10000000000 1384915460443 4000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873160779/2000000000 : ℝ), (1060259021/2500000000 : ℝ), (4494231677/10000000000 : ℝ)] ![(6663389437047/20000000000000 : ℝ), (8015041573357/25000000000000 : ℝ), (1384915460443/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873160779/2000000000 : ℝ)|^8327 ≤ (6663389437047/20000000000000 : ℝ)^6279
        have hw : |(873160779/2000000000 : ℝ)|=(873160779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060259021/2500000000 : ℝ)|^8327 ≤ (8015041573357/25000000000000 : ℝ)^6279
        have hw : |(1060259021/2500000000 : ℝ)|=(1060259021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494231677/10000000000 : ℝ)|^8327 ≤ (1384915460443/4000000000000 : ℝ)^6279
        have hw : |(4494231677/10000000000 : ℝ)|=(4494231677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s9_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170727237/10000000000 : ℝ)*x 0 + (2632989321/5000000000 : ℝ)*x 1 + (674100561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170727237/10000000000 : ℝ)^8327 ≤ (263789832169/2000000000000 : ℝ)^6279 := by
    have hnat : (2170727237 : ℕ)^8327*2000000000000^6279 ≤ 263789832169^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170727237 10000000000 263789832169 2000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632989321/5000000000 : ℝ)^8327 ≤ (10680089410019/25000000000000 : ℝ)^6279 := by
    have hnat : (2632989321 : ℕ)^8327*25000000000000^6279 ≤ 10680089410019^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632989321 5000000000 10680089410019 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674100561/1250000000 : ℝ)^8327 ≤ (44090150735273/100000000000000 : ℝ)^6279 := by
    have hnat : (674100561 : ℕ)^8327*100000000000000^6279 ≤ 44090150735273^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674100561 1250000000 44090150735273 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170727237/10000000000 : ℝ), (2632989321/5000000000 : ℝ), (674100561/1250000000 : ℝ)] ![(263789832169/2000000000000 : ℝ), (10680089410019/25000000000000 : ℝ), (44090150735273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170727237/10000000000 : ℝ)|^8327 ≤ (263789832169/2000000000000 : ℝ)^6279
        have hw : |(-2170727237/10000000000 : ℝ)|=(2170727237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632989321/5000000000 : ℝ)|^8327 ≤ (10680089410019/25000000000000 : ℝ)^6279
        have hw : |(2632989321/5000000000 : ℝ)|=(2632989321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674100561/1250000000 : ℝ)|^8327 ≤ (44090150735273/100000000000000 : ℝ)^6279
        have hw : |(674100561/1250000000 : ℝ)|=(674100561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s9_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272863333/625000000 : ℝ)*x 0 + (4493596421/10000000000 : ℝ)*x 1 + (1060418479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272863333/625000000 : ℝ)^8327 ≤ (6663408530261/20000000000000 : ℝ)^6279 := by
    have hnat : (272863333 : ℕ)^8327*20000000000000^6279 ≤ 6663408530261^6279*625000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272863333 625000000 6663408530261 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493596421/10000000000 : ℝ)^8327 ≤ (6923279302321/20000000000000 : ℝ)^6279 := by
    have hnat : (4493596421 : ℕ)^8327*20000000000000^6279 ≤ 6923279302321^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493596421 10000000000 6923279302321 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060418479/2500000000 : ℝ)^8327 ≤ (16033280413267/50000000000000 : ℝ)^6279 := by
    have hnat : (1060418479 : ℕ)^8327*50000000000000^6279 ≤ 16033280413267^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060418479 2500000000 16033280413267 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272863333/625000000 : ℝ), (4493596421/10000000000 : ℝ), (1060418479/2500000000 : ℝ)] ![(6663408530261/20000000000000 : ℝ), (6923279302321/20000000000000 : ℝ), (16033280413267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272863333/625000000 : ℝ)|^8327 ≤ (6663408530261/20000000000000 : ℝ)^6279
        have hw : |(272863333/625000000 : ℝ)|=(272863333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493596421/10000000000 : ℝ)|^8327 ≤ (6923279302321/20000000000000 : ℝ)^6279
        have hw : |(4493596421/10000000000 : ℝ)|=(4493596421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060418479/2500000000 : ℝ)|^8327 ≤ (16033280413267/50000000000000 : ℝ)^6279
        have hw : |(1060418479/2500000000 : ℝ)|=(1060418479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (709/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3511/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11343/100000 : ℝ) ^ (4163/1024 : ℝ) ≤ (2871394525167119/20000000000000000000 : ℝ) := by
    have hpowers : (11343/100000 : ℝ)^4163 ≤ (2871394525167119/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11343 : ℕ)^4163*20000000000000000000^1024 ≤ 2871394525167119^1024*100000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11343 100000 2871394525167119 20000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11343/100000 : ℝ)) (X := (2871394525167119/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3511/25000 : ℝ) ^ (4163/1024 : ℝ) ≤ (2138276639415669/6250000000000000000 : ℝ) := by
    have hpowers : (3511/25000 : ℝ)^4163 ≤ (2138276639415669/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3511 : ℕ)^4163*6250000000000000000^1024 ≤ 2138276639415669^1024*25000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3511 25000 2138276639415669 6250000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3511/25000 : ℝ)) (X := (2138276639415669/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002871394525167119/10000000000000000000 : ℝ) ≤ (10000706219011361/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (10002871394525167119/10000000000000000000 : ℝ)^1024 ≤ (10000706219011361/10000000000000000 : ℝ)^4163 := by
      have hnat : (10002871394525167119 : ℕ)^1024*10000000000000000^4163 ≤ 10000706219011361^4163*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002871394525167119 10000000000000000000 10000706219011361 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706219011361/10000000000000000 : ℝ)) (X := (10002871394525167119/10000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048569398856486299/100000000000000000000 : ℝ) ≤ (1000119447417511/1000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (100048569398856486299/100000000000000000000 : ℝ)^1024 ≤ (1000119447417511/1000000000000000 : ℝ)^4163 := by
      have hnat : (100048569398856486299 : ℕ)^1024*1000000000000000^4163 ≤ 1000119447417511^4163*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048569398856486299 100000000000000000000 1000119447417511 1000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000119447417511/1000000000000000 : ℝ)) (X := (100048569398856486299/100000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127138276639415669/3125000000000000000 : ℝ) ≤ (10001682729338859/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (3127138276639415669/3125000000000000000 : ℝ)^1024 ≤ (10001682729338859/10000000000000000 : ℝ)^4163 := by
      have hnat : (3127138276639415669 : ℕ)^1024*10000000000000000^4163 ≤ 10001682729338859^4163*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127138276639415669 3125000000000000000 10001682729338859 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001682729338859/10000000000000000 : ℝ)) (X := (3127138276639415669/3125000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2871394525167119/20000000000000000000 : ℝ) ≤ ((27000830940904876247/27010000000000000000 : ℝ)+2*(488255163749/270100000000000 : ℝ)*(11343/100000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (27000830940904876247/27010000000000000000 : ℝ)+2*(488255163749/270100000000000 : ℝ)*(11343/100000 : ℝ)=(10000706219011361/10000000000000000 : ℝ) by norm_num, show 1+2*(2871394525167119/20000000000000000000 : ℝ)=(10002871394525167119/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2138276639415669/6250000000000000000 : ℝ)+(2871394525167119/20000000000000000000 : ℝ) ≤ ((27000830940904876247/27010000000000000000 : ℝ)+(488255163749/270100000000000 : ℝ)*((3511/25000 : ℝ)+(11343/100000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (27000830940904876247/27010000000000000000 : ℝ)+(488255163749/270100000000000 : ℝ)*((3511/25000 : ℝ)+(11343/100000 : ℝ))=(1000119447417511/1000000000000000 : ℝ) by norm_num, show 1+(2138276639415669/6250000000000000000 : ℝ)+(2871394525167119/20000000000000000000 : ℝ)=(100048569398856486299/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2138276639415669/6250000000000000000 : ℝ) ≤ ((27000830940904876247/27010000000000000000 : ℝ)+2*(488255163749/270100000000000 : ℝ)*(3511/25000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (27000830940904876247/27010000000000000000 : ℝ)+2*(488255163749/270100000000000 : ℝ)*(3511/25000 : ℝ)=(10001682729338859/10000000000000000 : ℝ) by norm_num, show 1+2*(2138276639415669/6250000000000000000 : ℝ)=(3127138276639415669/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27000830940904876247/27010000000000000000 : ℝ)*(X 1 0+X 2 0)+(488255163749/270100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (27000830940904876247/27010000000000000000 : ℝ)) (alpha := (488255163749/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27000830940904876247/27010000000000000000 : ℝ)*(X 0 1+X 2 1)+(488255163749/270100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (27000830940904876247/27010000000000000000 : ℝ)) (alpha := (488255163749/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27000830940904876247/27010000000000000000 : ℝ)*(X 0 2+X 1 2)+(488255163749/270100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (27000830940904876247/27010000000000000000 : ℝ)) (alpha := (488255163749/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1085361079/5000000000 : ℝ)*X 0 0+(5393125999/10000000000 : ℝ)*X 0 1+(5265658423/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344773723/10000000000 : ℝ)*X 1 0+(-2235377227/10000000000 : ℝ)*X 1 1+(1316414603/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344773743/10000000000 : ℝ)*X 2 0+(1316414599/2500000000 : ℝ)*X 2 1+(-1117688611/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873160779/2000000000 : ℝ)*X 0 0+(1060259021/2500000000 : ℝ)*X 0 1+(4494231677/10000000000 : ℝ)*X 0 2+(873160779/2000000000 : ℝ)*X 1 0+(1060259021/2500000000 : ℝ)*X 1 1+(4494231677/10000000000 : ℝ)*X 1 2+(873160779/2000000000 : ℝ)*X 2 0+(1060259021/2500000000 : ℝ)*X 2 1+(4494231677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2170727237/10000000000 : ℝ)*X 0 0+(2632989321/5000000000 : ℝ)*X 0 1+(674100561/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((272863333/625000000 : ℝ)*X 0 0+(4493596421/10000000000 : ℝ)*X 0 1+(1060418479/2500000000 : ℝ)*X 0 2+(272863333/625000000 : ℝ)*X 1 0+(4493596421/10000000000 : ℝ)*X 1 1+(1060418479/2500000000 : ℝ)*X 1 2+(272863333/625000000 : ℝ)*X 2 0+(4493596421/10000000000 : ℝ)*X 2 1+(1060418479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (407573238493849567677026289/168812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225306227/50000000000000 : ℝ)*(base19) + (18464611/4000000000000 : ℝ)*(base23) + (9809553/100000000000000 : ℝ)*(lower2) + (44277173/100000000000000 : ℝ)*(upper3) + (44453639/100000000000000 : ℝ)*(upper5) + (1474335674236671/25000000000000 : ℝ)*(major0) + (1474335674236671/25000000000000 : ℝ)*(major1) + (1474335674236671/25000000000000 : ℝ)*(major2) + (3922572141202243/50000000000000 : ℝ)*(sp0) + (7845156449444077/100000000000000 : ℝ)*(sp1) + (980644554805157/12500000000000 : ℝ)*(sp2) + (1974760988870093/50000000000000 : ℝ)*(sp3) + (6308826023/50000000000000 : ℝ)*(sp4) + (6435618153/100000000000000 : ℝ)*(sp5) + (1974764206679169/50000000000000 : ℝ)*(f.failure) + (7845156900056531/100000000000000 : ℝ)*(f.sum) + (3386869934547/422031250000000000000000000 : ℝ)*base66 + (2033032757606403737/675250000000000000000000000000000 : ℝ)*base67 + (12813870323328153737/675250000000000000000000000000000 : ℝ)*base69 + (2591382638945903737/675250000000000000000000000000000 : ℝ)*base71 + (75847060906237/6752500000000000000000000000 : ℝ)*base74 + (4245921737753653737/675250000000000000000000000000000 : ℝ)*base75 + (4302347611663346263/675250000000000000000000000000000 : ℝ)*base78 + (2907648746773903737/675250000000000000000000000000000 : ℝ)*base79 + (12071931322937/6752500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (17200251/2500000000000000000000 : ℝ)*base90 + (17200251/2500000000000000000000 : ℝ)*base92 + (17200251/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1134_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1134_box_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043560779/10000000000 : ℝ)*x 0 + (2688212223/5000000000 : ℝ)*x 1 + (672053043/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043560779/10000000000 : ℝ)^8327 ≤ (608736057077/5000000000000 : ℝ)^6279 := by
    have hnat : (2043560779 : ℕ)^8327*5000000000000^6279 ≤ 608736057077^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043560779 10000000000 608736057077 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688212223/5000000000 : ℝ)^8327 ≤ (43912639979237/100000000000000 : ℝ)^6279 := by
    have hnat : (2688212223 : ℕ)^8327*100000000000000^6279 ≤ 43912639979237^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688212223 5000000000 43912639979237 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672053043/1250000000 : ℝ)^8327 ≤ (4391263887441/10000000000000 : ℝ)^6279 := by
    have hnat : (672053043 : ℕ)^8327*10000000000000^6279 ≤ 4391263887441^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672053043 1250000000 4391263887441 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043560779/10000000000 : ℝ), (2688212223/5000000000 : ℝ), (672053043/1250000000 : ℝ)] ![(608736057077/5000000000000 : ℝ), (43912639979237/100000000000000 : ℝ), (4391263887441/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043560779/10000000000 : ℝ)|^8327 ≤ (608736057077/5000000000000 : ℝ)^6279
        have hw : |(-2043560779/10000000000 : ℝ)|=(2043560779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688212223/5000000000 : ℝ)|^8327 ≤ (43912639979237/100000000000000 : ℝ)^6279
        have hw : |(2688212223/5000000000 : ℝ)|=(2688212223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672053043/1250000000 : ℝ)|^8327 ≤ (4391263887441/10000000000000 : ℝ)^6279
        have hw : |(672053043/1250000000 : ℝ)|=(672053043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295910273/10000000000 : ℝ)*x 0 + (-215273171/1000000000 : ℝ)*x 1 + (5376424539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295910273/10000000000 : ℝ)^8327 ≤ (8608535360419/20000000000000 : ℝ)^6279 := by
    have hnat : (5295910273 : ℕ)^8327*20000000000000^6279 ≤ 8608535360419^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295910273 10000000000 8608535360419 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215273171/1000000000 : ℝ)^8327 ≤ (130446821931/1000000000000 : ℝ)^6279 := by
    have hnat : (215273171 : ℕ)^8327*1000000000000^6279 ≤ 130446821931^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215273171 1000000000 130446821931 1000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376424539/10000000000 : ℝ)^8327 ≤ (43912640986579/100000000000000 : ℝ)^6279 := by
    have hnat : (5376424539 : ℕ)^8327*100000000000000^6279 ≤ 43912640986579^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376424539 10000000000 43912640986579 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295910273/10000000000 : ℝ), (-215273171/1000000000 : ℝ), (5376424539/10000000000 : ℝ)] ![(8608535360419/20000000000000 : ℝ), (130446821931/1000000000000 : ℝ), (43912640986579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295910273/10000000000 : ℝ)|^8327 ≤ (8608535360419/20000000000000 : ℝ)^6279
        have hw : |(5295910273/10000000000 : ℝ)|=(5295910273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215273171/1000000000 : ℝ)|^8327 ≤ (130446821931/1000000000000 : ℝ)^6279
        have hw : |(-215273171/1000000000 : ℝ)|=(215273171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376424539/10000000000 : ℝ)|^8327 ≤ (43912640986579/100000000000000 : ℝ)^6279
        have hw : |(5376424539/10000000000 : ℝ)|=(5376424539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059182169/2000000000 : ℝ)*x 0 + (5376424311/10000000000 : ℝ)*x 1 + (-538182813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059182169/2000000000 : ℝ)^8327 ≤ (21521341483687/50000000000000 : ℝ)^6279 := by
    have hnat : (1059182169 : ℕ)^8327*50000000000000^6279 ≤ 21521341483687^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059182169 2000000000 21521341483687 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376424311/10000000000 : ℝ)^8327 ≤ (21956319258483/50000000000000 : ℝ)^6279 := by
    have hnat : (5376424311 : ℕ)^8327*50000000000000^6279 ≤ 21956319258483^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376424311 10000000000 21956319258483 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538182813/2500000000 : ℝ)^8327 ≤ (13044678512597/100000000000000 : ℝ)^6279 := by
    have hnat : (538182813 : ℕ)^8327*100000000000000^6279 ≤ 13044678512597^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538182813 2500000000 13044678512597 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059182169/2000000000 : ℝ), (5376424311/10000000000 : ℝ), (-538182813/2500000000 : ℝ)] ![(21521341483687/50000000000000 : ℝ), (21956319258483/50000000000000 : ℝ), (13044678512597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059182169/2000000000 : ℝ)|^8327 ≤ (21521341483687/50000000000000 : ℝ)^6279
        have hw : |(1059182169/2000000000 : ℝ)|=(1059182169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376424311/10000000000 : ℝ)|^8327 ≤ (21956319258483/50000000000000 : ℝ)^6279
        have hw : |(5376424311/10000000000 : ℝ)|=(5376424311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538182813/2500000000 : ℝ)|^8327 ≤ (13044678512597/100000000000000 : ℝ)^6279
        have hw : |(-538182813/2500000000 : ℝ)|=(538182813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4473433949/10000000000 : ℝ)*x 0 + (4314102381/10000000000 : ℝ)*x 1 + (4314102109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4473433949/10000000000 : ℝ)^8327 ≤ (4301320651219/12500000000000 : ℝ)^6279 := by
    have hnat : (4473433949 : ℕ)^8327*12500000000000^6279 ≤ 4301320651219^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473433949 10000000000 4301320651219 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314102381/10000000000 : ℝ)^8327 ≤ (16397359377699/50000000000000 : ℝ)^6279 := by
    have hnat : (4314102381 : ℕ)^8327*50000000000000^6279 ≤ 16397359377699^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314102381 10000000000 16397359377699 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314102109/10000000000 : ℝ)^8327 ≤ (8198679003329/25000000000000 : ℝ)^6279 := by
    have hnat : (4314102109 : ℕ)^8327*25000000000000^6279 ≤ 8198679003329^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314102109 10000000000 8198679003329 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4473433949/10000000000 : ℝ), (4314102381/10000000000 : ℝ), (4314102109/10000000000 : ℝ)] ![(4301320651219/12500000000000 : ℝ), (16397359377699/50000000000000 : ℝ), (8198679003329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4473433949/10000000000 : ℝ)|^8327 ≤ (4301320651219/12500000000000 : ℝ)^6279
        have hw : |(4473433949/10000000000 : ℝ)|=(4473433949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314102381/10000000000 : ℝ)|^8327 ≤ (16397359377699/50000000000000 : ℝ)^6279
        have hw : |(4314102381/10000000000 : ℝ)|=(4314102381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4314102109/10000000000 : ℝ)|^8327 ≤ (8198679003329/25000000000000 : ℝ)^6279
        have hw : |(4314102109/10000000000 : ℝ)|=(4314102109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-459852269/2000000000 : ℝ)*x 0 + (2640519473/5000000000 : ℝ)*x 1 + (2640519643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459852269/2000000000 : ℝ)^8327 ≤ (1779384479513/12500000000000 : ℝ)^6279 := by
    have hnat : (459852269 : ℕ)^8327*12500000000000^6279 ≤ 1779384479513^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459852269 2000000000 1779384479513 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640519473/5000000000 : ℝ)^8327 ≤ (8576492048481/20000000000000 : ℝ)^6279 := by
    have hnat : (2640519473 : ℕ)^8327*20000000000000^6279 ≤ 8576492048481^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640519473 5000000000 8576492048481 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640519643/5000000000 : ℝ)^8327 ≤ (21441231951861/50000000000000 : ℝ)^6279 := by
    have hnat : (2640519643 : ℕ)^8327*50000000000000^6279 ≤ 21441231951861^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640519643 5000000000 21441231951861 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-459852269/2000000000 : ℝ), (2640519473/5000000000 : ℝ), (2640519643/5000000000 : ℝ)] ![(1779384479513/12500000000000 : ℝ), (8576492048481/20000000000000 : ℝ), (21441231951861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-459852269/2000000000 : ℝ)|^8327 ≤ (1779384479513/12500000000000 : ℝ)^6279
        have hw : |(-459852269/2000000000 : ℝ)|=(459852269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640519473/5000000000 : ℝ)|^8327 ≤ (8576492048481/20000000000000 : ℝ)^6279
        have hw : |(2640519473/5000000000 : ℝ)|=(2640519473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640519643/5000000000 : ℝ)|^8327 ≤ (21441231951861/50000000000000 : ℝ)^6279
        have hw : |(2640519643/5000000000 : ℝ)|=(2640519643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1047522/1953125 : ℝ)*x 0 + (-2190228827/10000000000 : ℝ)*x 1 + (1056207839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047522/1953125 : ℝ)^8327 ≤ (21885337088747/50000000000000 : ℝ)^6279 := by
    have hnat : (1047522 : ℕ)^8327*50000000000000^6279 ≤ 21885337088747^6279*1953125^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047522 1953125 21885337088747 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190228827/10000000000 : ℝ)^8327 ≤ (3336715720159/25000000000000 : ℝ)^6279 := by
    have hnat : (2190228827 : ℕ)^8327*25000000000000^6279 ≤ 3336715720159^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190228827 10000000000 3336715720159 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056207839/2000000000 : ℝ)^8327 ≤ (21441231461891/50000000000000 : ℝ)^6279 := by
    have hnat : (1056207839 : ℕ)^8327*50000000000000^6279 ≤ 21441231461891^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056207839 2000000000 21441231461891 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047522/1953125 : ℝ), (-2190228827/10000000000 : ℝ), (1056207839/2000000000 : ℝ)] ![(21885337088747/50000000000000 : ℝ), (3336715720159/25000000000000 : ℝ), (21441231461891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047522/1953125 : ℝ)|^8327 ≤ (21885337088747/50000000000000 : ℝ)^6279
        have hw : |(1047522/1953125 : ℝ)|=(1047522/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190228827/10000000000 : ℝ)|^8327 ≤ (3336715720159/25000000000000 : ℝ)^6279
        have hw : |(-2190228827/10000000000 : ℝ)|=(2190228827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056207839/2000000000 : ℝ)|^8327 ≤ (21441231461891/50000000000000 : ℝ)^6279
        have hw : |(1056207839/2000000000 : ℝ)|=(1056207839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (670414113/1250000000 : ℝ)*x 0 + (1320259677/2500000000 : ℝ)*x 1 + (-2190229123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670414113/1250000000 : ℝ)^8327 ≤ (43770677034769/100000000000000 : ℝ)^6279 := by
    have hnat : (670414113 : ℕ)^8327*100000000000000^6279 ≤ 43770677034769^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670414113 1250000000 43770677034769 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320259677/2500000000 : ℝ)^8327 ≤ (10720614419871/25000000000000 : ℝ)^6279 := by
    have hnat : (1320259677 : ℕ)^8327*25000000000000^6279 ≤ 10720614419871^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320259677 2500000000 10720614419871 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190229123/10000000000 : ℝ)^8327 ≤ (13346865272737/100000000000000 : ℝ)^6279 := by
    have hnat : (2190229123 : ℕ)^8327*100000000000000^6279 ≤ 13346865272737^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190229123 10000000000 13346865272737 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670414113/1250000000 : ℝ), (1320259677/2500000000 : ℝ), (-2190229123/10000000000 : ℝ)] ![(43770677034769/100000000000000 : ℝ), (10720614419871/25000000000000 : ℝ), (13346865272737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670414113/1250000000 : ℝ)|^8327 ≤ (43770677034769/100000000000000 : ℝ)^6279
        have hw : |(670414113/1250000000 : ℝ)|=(670414113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320259677/2500000000 : ℝ)|^8327 ≤ (10720614419871/25000000000000 : ℝ)^6279
        have hw : |(1320259677/2500000000 : ℝ)|=(1320259677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190229123/10000000000 : ℝ)|^8327 ≤ (13346865272737/100000000000000 : ℝ)^6279
        have hw : |(-2190229123/10000000000 : ℝ)|=(2190229123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4257816097/10000000000 : ℝ)*x 0 + (4421890229/10000000000 : ℝ)*x 1 + (2210945157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257816097/10000000000 : ℝ)^8327 ≤ (32228497279879/100000000000000 : ℝ)^6279 := by
    have hnat : (4257816097 : ℕ)^8327*100000000000000^6279 ≤ 32228497279879^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257816097 10000000000 32228497279879 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4421890229/10000000000 : ℝ)^8327 ≤ (3388575091999/10000000000000 : ℝ)^6279 := by
    have hnat : (4421890229 : ℕ)^8327*10000000000000^6279 ≤ 3388575091999^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421890229 10000000000 3388575091999 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210945157/5000000000 : ℝ)^8327 ≤ (4235718972977/12500000000000 : ℝ)^6279 := by
    have hnat : (2210945157 : ℕ)^8327*12500000000000^6279 ≤ 4235718972977^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210945157 5000000000 4235718972977 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257816097/10000000000 : ℝ), (4421890229/10000000000 : ℝ), (2210945157/5000000000 : ℝ)] ![(32228497279879/100000000000000 : ℝ), (3388575091999/10000000000000 : ℝ), (4235718972977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257816097/10000000000 : ℝ)|^8327 ≤ (32228497279879/100000000000000 : ℝ)^6279
        have hw : |(4257816097/10000000000 : ℝ)|=(4257816097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4421890229/10000000000 : ℝ)|^8327 ≤ (3388575091999/10000000000000 : ℝ)^6279
        have hw : |(4421890229/10000000000 : ℝ)|=(4421890229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210945157/5000000000 : ℝ)|^8327 ≤ (4235718972977/12500000000000 : ℝ)^6279
        have hw : |(2210945157/5000000000 : ℝ)|=(2210945157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_8 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1122899773/5000000000 : ℝ)*x 0 + (1304045777/2500000000 : ℝ)*x 1 + (2154413/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1122899773/5000000000 : ℝ)^8327 ≤ (13797801068521/100000000000000 : ℝ)^6279 := by
    have hnat : (1122899773 : ℕ)^8327*100000000000000^6279 ≤ 13797801068521^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122899773 5000000000 13797801068521 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304045777/2500000000 : ℝ)^8327 ≤ (1687418306653/4000000000000 : ℝ)^6279 := by
    have hnat : (1304045777 : ℕ)^8327*4000000000000^6279 ≤ 1687418306653^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304045777 2500000000 1687418306653 4000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154413/4000000 : ℝ)^8327 ≤ (44016741247171/100000000000000 : ℝ)^6279 := by
    have hnat : (2154413 : ℕ)^8327*100000000000000^6279 ≤ 44016741247171^6279*4000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154413 4000000 44016741247171 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1122899773/5000000000 : ℝ), (1304045777/2500000000 : ℝ), (2154413/4000000 : ℝ)] ![(13797801068521/100000000000000 : ℝ), (1687418306653/4000000000000 : ℝ), (44016741247171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1122899773/5000000000 : ℝ)|^8327 ≤ (13797801068521/100000000000000 : ℝ)^6279
        have hw : |(-1122899773/5000000000 : ℝ)|=(1122899773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304045777/2500000000 : ℝ)|^8327 ≤ (1687418306653/4000000000000 : ℝ)^6279
        have hw : |(1304045777/2500000000 : ℝ)|=(1304045777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2154413/4000000 : ℝ)|^8327 ≤ (44016741247171/100000000000000 : ℝ)^6279
        have hw : |(2154413/4000000 : ℝ)|=(2154413/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_9 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289117839/10000000000 : ℝ)*x 0 + (-2148884993/10000000000 : ℝ)*x 1 + (215441299/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289117839/10000000000 : ℝ)^8327 ≤ (42969480138379/100000000000000 : ℝ)^6279 := by
    have hnat : (5289117839 : ℕ)^8327*100000000000000^6279 ≤ 42969480138379^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289117839 10000000000 42969480138379 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148884993/10000000000 : ℝ)^8327 ≤ (13013778862741/100000000000000 : ℝ)^6279 := by
    have hnat : (2148884993 : ℕ)^8327*100000000000000^6279 ≤ 13013778862741^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148884993 10000000000 13013778862741 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215441299/400000000 : ℝ)^8327 ≤ (44016740976223/100000000000000 : ℝ)^6279 := by
    have hnat : (215441299 : ℕ)^8327*100000000000000^6279 ≤ 44016740976223^6279*400000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215441299 400000000 44016740976223 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289117839/10000000000 : ℝ), (-2148884993/10000000000 : ℝ), (215441299/400000000 : ℝ)] ![(42969480138379/100000000000000 : ℝ), (13013778862741/100000000000000 : ℝ), (44016740976223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289117839/10000000000 : ℝ)|^8327 ≤ (42969480138379/100000000000000 : ℝ)^6279
        have hw : |(5289117839/10000000000 : ℝ)|=(5289117839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148884993/10000000000 : ℝ)|^8327 ≤ (13013778862741/100000000000000 : ℝ)^6279
        have hw : |(-2148884993/10000000000 : ℝ)|=(2148884993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215441299/400000000 : ℝ)|^8327 ≤ (44016740976223/100000000000000 : ℝ)^6279
        have hw : |(215441299/400000000 : ℝ)|=(215441299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_10 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289117839/10000000000 : ℝ)*x 0 + (5386032529/10000000000 : ℝ)*x 1 + (-2148884921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289117839/10000000000 : ℝ)^8327 ≤ (42969480138379/100000000000000 : ℝ)^6279 := by
    have hnat : (5289117839 : ℕ)^8327*100000000000000^6279 ≤ 42969480138379^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289117839 10000000000 42969480138379 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386032529/10000000000 : ℝ)^8327 ≤ (343880793449/781250000000 : ℝ)^6279 := by
    have hnat : (5386032529 : ℕ)^8327*781250000000^6279 ≤ 343880793449^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386032529 10000000000 343880793449 781250000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148884921/10000000000 : ℝ)^8327 ≤ (3253444571121/25000000000000 : ℝ)^6279 := by
    have hnat : (2148884921 : ℕ)^8327*25000000000000^6279 ≤ 3253444571121^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148884921 10000000000 3253444571121 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289117839/10000000000 : ℝ), (5386032529/10000000000 : ℝ), (-2148884921/10000000000 : ℝ)] ![(42969480138379/100000000000000 : ℝ), (343880793449/781250000000 : ℝ), (3253444571121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289117839/10000000000 : ℝ)|^8327 ≤ (42969480138379/100000000000000 : ℝ)^6279
        have hw : |(5289117839/10000000000 : ℝ)|=(5289117839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386032529/10000000000 : ℝ)|^8327 ≤ (343880793449/781250000000 : ℝ)^6279
        have hw : |(5386032529/10000000000 : ℝ)|=(5386032529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148884921/10000000000 : ℝ)|^8327 ≤ (3253444571121/25000000000000 : ℝ)^6279
        have hw : |(-2148884921/10000000000 : ℝ)|=(2148884921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_11 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4494879791/10000000000 : ℝ)*x 0 + (268952419/625000000 : ℝ)*x 1 + (4303238877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494879791/10000000000 : ℝ)^8327 ≤ (34629508180773/100000000000000 : ℝ)^6279 := by
    have hnat : (4494879791 : ℕ)^8327*100000000000000^6279 ≤ 34629508180773^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494879791 10000000000 34629508180773 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268952419/625000000 : ℝ)^8327 ≤ (4085655628699/12500000000000 : ℝ)^6279 := by
    have hnat : (268952419 : ℕ)^8327*12500000000000^6279 ≤ 4085655628699^6279*625000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268952419 625000000 4085655628699 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4303238877/10000000000 : ℝ)^8327 ≤ (32685246772203/100000000000000 : ℝ)^6279 := by
    have hnat : (4303238877 : ℕ)^8327*100000000000000^6279 ≤ 32685246772203^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303238877 10000000000 32685246772203 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494879791/10000000000 : ℝ), (268952419/625000000 : ℝ), (4303238877/10000000000 : ℝ)] ![(34629508180773/100000000000000 : ℝ), (4085655628699/12500000000000 : ℝ), (32685246772203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494879791/10000000000 : ℝ)|^8327 ≤ (34629508180773/100000000000000 : ℝ)^6279
        have hw : |(4494879791/10000000000 : ℝ)|=(4494879791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268952419/625000000 : ℝ)|^8327 ≤ (4085655628699/12500000000000 : ℝ)^6279
        have hw : |(268952419/625000000 : ℝ)|=(268952419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4303238877/10000000000 : ℝ)|^8327 ≤ (32685246772203/100000000000000 : ℝ)^6279
        have hw : |(4303238877/10000000000 : ℝ)|=(4303238877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_12 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097346099/10000000000 : ℝ)*x 0 + (679999623/1250000000 : ℝ)*x 1 + (1054600879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097346099/10000000000 : ℝ)^8327 ≤ (12601480017459/100000000000000 : ℝ)^6279 := by
    have hnat : (2097346099 : ℕ)^8327*100000000000000^6279 ≤ 12601480017459^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097346099 10000000000 12601480017459 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679999623/1250000000 : ℝ)^8327 ≤ (44602558950583/100000000000000 : ℝ)^6279 := by
    have hnat : (679999623 : ℕ)^8327*100000000000000^6279 ≤ 44602558950583^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679999623 1250000000 44602558950583 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054600879/2000000000 : ℝ)^8327 ≤ (5349495127287/12500000000000 : ℝ)^6279 := by
    have hnat : (1054600879 : ℕ)^8327*12500000000000^6279 ≤ 5349495127287^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054600879 2000000000 5349495127287 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097346099/10000000000 : ℝ), (679999623/1250000000 : ℝ), (1054600879/2000000000 : ℝ)] ![(12601480017459/100000000000000 : ℝ), (44602558950583/100000000000000 : ℝ), (5349495127287/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097346099/10000000000 : ℝ)|^8327 ≤ (12601480017459/100000000000000 : ℝ)^6279
        have hw : |(-2097346099/10000000000 : ℝ)|=(2097346099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679999623/1250000000 : ℝ)|^8327 ≤ (44602558950583/100000000000000 : ℝ)^6279
        have hw : |(679999623/1250000000 : ℝ)|=(679999623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054600879/2000000000 : ℝ)|^8327 ≤ (5349495127287/12500000000000 : ℝ)^6279
        have hw : |(1054600879/2000000000 : ℝ)|=(1054600879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_13 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073797419/2000000000 : ℝ)*x 0 + (-2193330103/10000000000 : ℝ)*x 1 + (1318251287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073797419/2000000000 : ℝ)^8327 ≤ (10958024868827/25000000000000 : ℝ)^6279 := by
    have hnat : (1073797419 : ℕ)^8327*25000000000000^6279 ≤ 10958024868827^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073797419 2000000000 10958024868827 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193330103/10000000000 : ℝ)^8327 ≤ (2674386277319/20000000000000 : ℝ)^6279 := by
    have hnat : (2193330103 : ℕ)^8327*20000000000000^6279 ≤ 2674386277319^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193330103 10000000000 2674386277319 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318251287/2500000000 : ℝ)^8327 ≤ (42795969123011/100000000000000 : ℝ)^6279 := by
    have hnat : (1318251287 : ℕ)^8327*100000000000000^6279 ≤ 42795969123011^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318251287 2500000000 42795969123011 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073797419/2000000000 : ℝ), (-2193330103/10000000000 : ℝ), (1318251287/2500000000 : ℝ)] ![(10958024868827/25000000000000 : ℝ), (2674386277319/20000000000000 : ℝ), (42795969123011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073797419/2000000000 : ℝ)|^8327 ≤ (10958024868827/25000000000000 : ℝ)^6279
        have hw : |(1073797419/2000000000 : ℝ)|=(1073797419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193330103/10000000000 : ℝ)|^8327 ≤ (2674386277319/20000000000000 : ℝ)^6279
        have hw : |(-2193330103/10000000000 : ℝ)|=(2193330103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318251287/2500000000 : ℝ)|^8327 ≤ (42795969123011/100000000000000 : ℝ)^6279
        have hw : |(1318251287/2500000000 : ℝ)|=(1318251287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_14 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342246879/2500000000 : ℝ)*x 0 + (5273004733/10000000000 : ℝ)*x 1 + (-548332523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342246879/2500000000 : ℝ)^8327 ≤ (43832104033369/100000000000000 : ℝ)^6279 := by
    have hnat : (1342246879 : ℕ)^8327*100000000000000^6279 ≤ 43832104033369^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342246879 2500000000 43832104033369 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273004733/10000000000 : ℝ)^8327 ≤ (42795964656269/100000000000000 : ℝ)^6279 := by
    have hnat : (5273004733 : ℕ)^8327*100000000000000^6279 ≤ 42795964656269^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273004733 10000000000 42795964656269 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548332523/2500000000 : ℝ)^8327 ≤ (6685965648829/50000000000000 : ℝ)^6279 := by
    have hnat : (548332523 : ℕ)^8327*50000000000000^6279 ≤ 6685965648829^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548332523 2500000000 6685965648829 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342246879/2500000000 : ℝ), (5273004733/10000000000 : ℝ), (-548332523/2500000000 : ℝ)] ![(43832104033369/100000000000000 : ℝ), (42795964656269/100000000000000 : ℝ), (6685965648829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342246879/2500000000 : ℝ)|^8327 ≤ (43832104033369/100000000000000 : ℝ)^6279
        have hw : |(1342246879/2500000000 : ℝ)|=(1342246879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273004733/10000000000 : ℝ)|^8327 ≤ (42795964656269/100000000000000 : ℝ)^6279
        have hw : |(5273004733/10000000000 : ℝ)|=(5273004733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548332523/2500000000 : ℝ)|^8327 ≤ (6685965648829/50000000000000 : ℝ)^6279
        have hw : |(-548332523/2500000000 : ℝ)|=(548332523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_box_15 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4239421483/10000000000 : ℝ)*x 0 + (1107741321/2500000000 : ℝ)*x 1 + (2215482763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239421483/10000000000 : ℝ)^8327 ≤ (32043980643817/100000000000000 : ℝ)^6279 := by
    have hnat : (4239421483 : ℕ)^8327*100000000000000^6279 ≤ 32043980643817^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239421483 10000000000 32043980643817 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107741321/2500000000 : ℝ)^8327 ≤ (6795601687733/20000000000000 : ℝ)^6279 := by
    have hnat : (1107741321 : ℕ)^8327*20000000000000^6279 ≤ 6795601687733^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107741321 2500000000 6795601687733 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215482763/5000000000 : ℝ)^8327 ≤ (33978010899673/100000000000000 : ℝ)^6279 := by
    have hnat : (2215482763 : ℕ)^8327*100000000000000^6279 ≤ 33978010899673^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215482763 5000000000 33978010899673 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239421483/10000000000 : ℝ), (1107741321/2500000000 : ℝ), (2215482763/5000000000 : ℝ)] ![(32043980643817/100000000000000 : ℝ), (6795601687733/20000000000000 : ℝ), (33978010899673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239421483/10000000000 : ℝ)|^8327 ≤ (32043980643817/100000000000000 : ℝ)^6279
        have hw : |(4239421483/10000000000 : ℝ)|=(4239421483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107741321/2500000000 : ℝ)|^8327 ≤ (6795601687733/20000000000000 : ℝ)^6279
        have hw : |(1107741321/2500000000 : ℝ)|=(1107741321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2215482763/5000000000 : ℝ)|^8327 ≤ (33978010899673/100000000000000 : ℝ)^6279
        have hw : |(2215482763/5000000000 : ℝ)|=(2215482763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(6223/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14823/25000 : ℝ) ∧ (9973/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83107/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (709/6250 : ℝ) ^ (4163/1024 : ℝ) ≤ (14362118984827877/100000000000000000000 : ℝ) := by
    have hpowers : (709/6250 : ℝ)^4163 ≤ (14362118984827877/100000000000000000000 : ℝ)^1024 := by
      have hnat : (709 : ℕ)^4163*100000000000000000000^1024 ≤ 14362118984827877^1024*6250^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        709 6250 14362118984827877 100000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (709/6250 : ℝ)) (X := (14362118984827877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3511/25000 : ℝ) ^ (4163/1024 : ℝ) ≤ (2138276639415669/6250000000000000000 : ℝ) := by
    have hpowers : (3511/25000 : ℝ)^4163 ≤ (2138276639415669/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3511 : ℕ)^4163*6250000000000000000^1024 ≤ 2138276639415669^1024*25000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3511 25000 2138276639415669 6250000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3511/25000 : ℝ)) (X := (2138276639415669/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014362118984827877/50000000000000000000 : ℝ) ≤ (5000353236066591/5000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50014362118984827877/50000000000000000000 : ℝ)^1024 ≤ (5000353236066591/5000000000000000 : ℝ)^4163 := by
      have hnat : (50014362118984827877 : ℕ)^1024*5000000000000000^4163 ≤ 5000353236066591^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014362118984827877 50000000000000000000 5000353236066591 5000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000353236066591/5000000000000000 : ℝ)) (X := (50014362118984827877/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048574545215478581/100000000000000000000 : ℝ) ≤ (2500298650179271/2500000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (100048574545215478581/100000000000000000000 : ℝ)^1024 ≤ (2500298650179271/2500000000000000 : ℝ)^4163 := by
      have hnat : (100048574545215478581 : ℕ)^1024*2500000000000000^4163 ≤ 2500298650179271^4163*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048574545215478581 100000000000000000000 2500298650179271 2500000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500298650179271/2500000000000000 : ℝ)) (X := (100048574545215478581/100000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127138276639415669/3125000000000000000 : ℝ) ≤ (5000841364650493/5000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (3127138276639415669/3125000000000000000 : ℝ)^1024 ≤ (5000841364650493/5000000000000000 : ℝ)^4163 := by
      have hnat : (3127138276639415669 : ℕ)^1024*5000000000000000^4163 ≤ 5000841364650493^4163*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127138276639415669 3125000000000000000 5000841364650493 5000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000841364650493/5000000000000000 : ℝ)) (X := (3127138276639415669/3125000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14362118984827877/100000000000000000000 : ℝ) ≤ ((3373854101681002853/3375000000000000000 : ℝ)+2*(244064291951/135000000000000 : ℝ)*(709/6250 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (3373854101681002853/3375000000000000000 : ℝ)+2*(244064291951/135000000000000 : ℝ)*(709/6250 : ℝ)=(5000353236066591/5000000000000000 : ℝ) by norm_num, show 1+2*(14362118984827877/100000000000000000000 : ℝ)=(50014362118984827877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2138276639415669/6250000000000000000 : ℝ)+(14362118984827877/100000000000000000000 : ℝ) ≤ ((3373854101681002853/3375000000000000000 : ℝ)+(244064291951/135000000000000 : ℝ)*((3511/25000 : ℝ)+(709/6250 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (3373854101681002853/3375000000000000000 : ℝ)+(244064291951/135000000000000 : ℝ)*((3511/25000 : ℝ)+(709/6250 : ℝ))=(2500298650179271/2500000000000000 : ℝ) by norm_num, show 1+(2138276639415669/6250000000000000000 : ℝ)+(14362118984827877/100000000000000000000 : ℝ)=(100048574545215478581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2138276639415669/6250000000000000000 : ℝ) ≤ ((3373854101681002853/3375000000000000000 : ℝ)+2*(244064291951/135000000000000 : ℝ)*(3511/25000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (3373854101681002853/3375000000000000000 : ℝ)+2*(244064291951/135000000000000 : ℝ)*(3511/25000 : ℝ)=(5000841364650493/5000000000000000 : ℝ) by norm_num, show 1+2*(2138276639415669/6250000000000000000 : ℝ)=(3127138276639415669/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3373854101681002853/3375000000000000000 : ℝ)*(X 1 0+X 2 0)+(244064291951/135000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (3373854101681002853/3375000000000000000 : ℝ)) (alpha := (244064291951/135000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3373854101681002853/3375000000000000000 : ℝ)*(X 0 1+X 2 1)+(244064291951/135000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (3373854101681002853/3375000000000000000 : ℝ)) (alpha := (244064291951/135000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3373854101681002853/3375000000000000000 : ℝ)*(X 0 2+X 1 2)+(244064291951/135000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (3373854101681002853/3375000000000000000 : ℝ)) (alpha := (244064291951/135000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2043560779/10000000000 : ℝ)*X 0 0+(2688212223/5000000000 : ℝ)*X 0 1+(672053043/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295910273/10000000000 : ℝ)*X 1 0+(-215273171/1000000000 : ℝ)*X 1 1+(5376424539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1059182169/2000000000 : ℝ)*X 2 0+(5376424311/10000000000 : ℝ)*X 2 1+(-538182813/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4473433949/10000000000 : ℝ)*X 0 0+(4314102381/10000000000 : ℝ)*X 0 1+(4314102109/10000000000 : ℝ)*X 0 2+(4473433949/10000000000 : ℝ)*X 1 0+(4314102381/10000000000 : ℝ)*X 1 1+(4314102109/10000000000 : ℝ)*X 1 2+(4473433949/10000000000 : ℝ)*X 2 0+(4314102381/10000000000 : ℝ)*X 2 1+(4314102109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-459852269/2000000000 : ℝ)*X 0 0+(2640519473/5000000000 : ℝ)*X 0 1+(2640519643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1047522/1953125 : ℝ)*X 1 0+(-2190228827/10000000000 : ℝ)*X 1 1+(1056207839/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((670414113/1250000000 : ℝ)*X 2 0+(1320259677/2500000000 : ℝ)*X 2 1+(-2190229123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4257816097/10000000000 : ℝ)*X 0 0+(4421890229/10000000000 : ℝ)*X 0 1+(2210945157/5000000000 : ℝ)*X 0 2+(4257816097/10000000000 : ℝ)*X 1 0+(4421890229/10000000000 : ℝ)*X 1 1+(2210945157/5000000000 : ℝ)*X 1 2+(4257816097/10000000000 : ℝ)*X 2 0+(4421890229/10000000000 : ℝ)*X 2 1+(2210945157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1122899773/5000000000 : ℝ)*X 0 0+(1304045777/2500000000 : ℝ)*X 0 1+(2154413/4000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289117839/10000000000 : ℝ)*X 1 0+(-2148884993/10000000000 : ℝ)*X 1 1+(215441299/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289117839/10000000000 : ℝ)*X 2 0+(5386032529/10000000000 : ℝ)*X 2 1+(-2148884921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4494879791/10000000000 : ℝ)*X 0 0+(268952419/625000000 : ℝ)*X 0 1+(4303238877/10000000000 : ℝ)*X 0 2+(4494879791/10000000000 : ℝ)*X 1 0+(268952419/625000000 : ℝ)*X 1 1+(4303238877/10000000000 : ℝ)*X 1 2+(4494879791/10000000000 : ℝ)*X 2 0+(268952419/625000000 : ℝ)*X 2 1+(4303238877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2097346099/10000000000 : ℝ)*X 0 0+(679999623/1250000000 : ℝ)*X 0 1+(1054600879/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073797419/2000000000 : ℝ)*X 1 0+(-2193330103/10000000000 : ℝ)*X 1 1+(1318251287/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342246879/2500000000 : ℝ)*X 2 0+(5273004733/10000000000 : ℝ)*X 2 1+(-548332523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4239421483/10000000000 : ℝ)*X 0 0+(1107741321/2500000000 : ℝ)*X 0 1+(2215482763/5000000000 : ℝ)*X 0 2+(4239421483/10000000000 : ℝ)*X 1 0+(1107741321/2500000000 : ℝ)*X 1 1+(2215482763/5000000000 : ℝ)*X 1 2+(4239421483/10000000000 : ℝ)*X 2 0+(1107741321/2500000000 : ℝ)*X 2 1+(2215482763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6223/10000 : ℝ) ≤ (-155569123958613652177095453/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159867681/100000000000000 : ℝ)*(lower0) + (64205677/50000000000000 : ℝ)*(lower2) + (196771957/100000000000000 : ℝ)*(lower3) + (2373381/800000000000 : ℝ)*(lower4) + (3913802253877941/100000000000000 : ℝ)*(major0) + (3913802253877941/100000000000000 : ℝ)*(major1) + (3913802253877941/100000000000000 : ℝ)*(major2) + (465668353/1562500000000 : ℝ)*(sp2) + (5227221916973603/100000000000000 : ℝ)*(sp4) + (2613518101028419/50000000000000 : ℝ)*(sp5) + (5227192114199011/100000000000000 : ℝ)*(sp6) + (1310527554913209/50000000000000 : ℝ)*(sp7) + (37142983353/20000000000000 : ℝ)*(sp13) + (14006163401/20000000000000 : ℝ)*(sp15) + (1310562570321711/50000000000000 : ℝ)*(f.failure) + (5227221916973603/100000000000000 : ℝ)*(f.sum) + (7771087166401/750000000000000000000000000 : ℝ)*base66 + (97045739199217703/37500000000000000000000000000000 : ℝ)*base68 + (226744794800782297/37500000000000000000000000000000 : ℝ)*base69 + (340116328299217703/37500000000000000000000000000000 : ℝ)*base72 + (4130951212651/750000000000000000000000000 : ℝ)*base74 + (14333388350782297/37500000000000000000000000000000 : ℝ)*base75 + (160298364613282297/37500000000000000000000000000000 : ℝ)*base77 + (70468794024217703/37500000000000000000000000000000 : ℝ)*base80 + (881171230651/750000000000000000000000000 : ℝ)*base82 + (8962731/2500000000000000000000 : ℝ)*base89 + (8962731/2500000000000000000000 : ℝ)*base91 + (8962731/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14823/25000 : ℝ) ≤ (1389720798419037386006960842279/2343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9968251/50000000000000 : ℝ)*(upper0) + (99314421/100000000000000 : ℝ)*(lower1) + (390878589/100000000000000 : ℝ)*(upper4) + (994462632437771/25000000000000 : ℝ)*(major0) + (994462632437771/25000000000000 : ℝ)*(major1) + (994462632437771/25000000000000 : ℝ)*(major2) + (2635953179574841/50000000000000 : ℝ)*(sp0) + (5271909989196293/100000000000000 : ℝ)*(sp1) + (2635952239783673/50000000000000 : ℝ)*(sp2) + (666001719514243/25000000000000 : ℝ)*(sp3) + (2508739133/20000000000000 : ℝ)*(sp6) + (6120080103/50000000000000 : ℝ)*(sp7) + (1066411333/10000000000000 : ℝ)*(sp8) + (7034066719/100000000000000 : ℝ)*(sp9) + (1332009559108589/50000000000000 : ℝ)*(f.failure) + (1317979255815753/25000000000000 : ℝ)*(f.sum) + (5217201512221/1687500000000000000000000000 : ℝ)*base65 + (998102664220235663/84375000000000000000000000000000 : ℝ)*base67 + (1345993536426485663/84375000000000000000000000000000 : ℝ)*base69 + (1163050446426485663/84375000000000000000000000000000 : ℝ)*base71 + (31938622605433/3375000000000000000000000000 : ℝ)*base74 + (678093705838985663/84375000000000000000000000000000 : ℝ)*base75 + (1902064889863985663/84375000000000000000000000000000 : ℝ)*base77 + (1550983671961014337/84375000000000000000000000000000 : ℝ)*base80 + (6466725189433/3375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (34286431/2500000000000000000000 : ℝ)*base90 + (34286431/2500000000000000000000 : ℝ)*base92 + (34286431/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (9973/12500 : ℝ) ≤ (311664738265083482651346324503/390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17658347/50000000000000 : ℝ)*(upper0) + (6146369/12500000000000 : ℝ)*(lower3) + (831331/5000000000000 : ℝ)*(upper4) + (138930707080479/3125000000000 : ℝ)*(major0) + (138930707080479/3125000000000 : ℝ)*(major1) + (138930707080479/3125000000000 : ℝ)*(major2) + (24425641911/50000000000000 : ℝ)*(sp1) + (36661627941/50000000000000 : ℝ)*(sp2) + (11527291287/50000000000000 : ℝ)*(sp3) + (1189026867/100000000000000 : ℝ)*(sp4) + (183986538747667/3125000000000 : ℝ)*(sp8) + (5887521577668389/100000000000000 : ℝ)*(sp9) + (5887497105696329/100000000000000 : ℝ)*(sp10) + (74434409465431/2500000000000 : ℝ)*(sp11) + (1488699716599907/50000000000000 : ℝ)*(f.failure) + (5887570428952211/100000000000000 : ℝ)*(f.sum) + (4706272982887/1125000000000000000000000000 : ℝ)*base66 + (21971819439173029/3515625000000000000000000000000 : ℝ)*base67 + (37263213118860529/3515625000000000000000000000000 : ℝ)*base69 + (9293875697125577/1757812500000000000000000000000 : ℝ)*base71 + (5784090870863/1125000000000000000000000000 : ℝ)*base73 + (13190713036188077/1757812500000000000000000000000 : ℝ)*base75 + (16378284506500577/1757812500000000000000000000000 : ℝ)*base77 + (24237966827804399/878906250000000000000000000000 : ℝ)*base80 + (255949772137/1125000000000000000000000000 : ℝ)*base82 + (14670353/2500000000000000000000 : ℝ)*base90 + (14670353/2500000000000000000000 : ℝ)*base92 + (14670353/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83107/100000 : ℝ) ≤ (-2597001090049901346233945756611/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1594469/4000000000000 : ℝ)*(lower1) + (72900731/100000000000000 : ℝ)*(lower2) + (34317627/25000000000000 : ℝ)*(upper5) + (2240373383428661/50000000000000 : ℝ)*(major0) + (2240373383428661/50000000000000 : ℝ)*(major1) + (2240373383428661/50000000000000 : ℝ)*(major2) + (25642011457/100000000000000 : ℝ)*(sp4) + (78952554999/25000000000000 : ℝ)*(sp6) + (206590926317/50000000000000 : ℝ)*(sp7) + (34545405699/100000000000000 : ℝ)*(sp8) + (1497079827702663/25000000000000 : ℝ)*(sp12) + (187136859319619/3125000000000 : ℝ)*(sp13) + (5988063688007811/100000000000000 : ℝ)*(sp14) + (1500201099297361/50000000000000 : ℝ)*(sp15) + (750203845111839/25000000000000 : ℝ)*(f.failure) + (187136859319619/3125000000000 : ℝ)*(f.sum) + (959778115967/421875000000000000000000000 : ℝ)*base65 + (444568725803244833/168750000000000000000000000000000 : ℝ)*base67 + (2465869898940744833/168750000000000000000000000000000 : ℝ)*base69 + (557826069953244833/168750000000000000000000000000000 : ℝ)*base71 + (13163049973861/3375000000000000000000000000 : ℝ)*base73 + (2048446044353244833/168750000000000000000000000000000 : ℝ)*base75 + (2368011015578244833/168750000000000000000000000000000 : ℝ)*base77 + (1488361008784494833/168750000000000000000000000000000 : ℝ)*base79 + (8836270550611/3375000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12118181/1250000000000000000000 : ℝ)*base90 + (12118181/1250000000000000000000 : ℝ)*base92 + (12118181/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1134_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14823/25000 : ℝ) else (9973/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83107/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1134_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1134_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14823/25000 : ℝ) else (9973/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83107/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1134_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1134_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14823/25000 : ℝ) else (9973/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83107/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
