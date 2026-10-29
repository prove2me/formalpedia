-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1609_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:03.936912+00:00
-- url     : https://prove2.me/submissions/62f9df19-1ac4-4df3-a057-994cf34aca15

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
theorem support_rectangle_w1609_s6_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353687133/10000000000 : ℝ)*x 0 + (2590381567/5000000000 : ℝ)*x 1 + (-1850647979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353687133/10000000000 : ℝ)^4755 ≤ (45100341751609/100000000000000 : ℝ)^3731 := by
    have hnat : (5353687133 : ℕ)^4755*100000000000000^3731 ≤ 45100341751609^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353687133 10000000000 45100341751609 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590381567/5000000000 : ℝ)^4755 ≤ (43252082931559/100000000000000 : ℝ)^3731 := by
    have hnat : (2590381567 : ℕ)^4755*100000000000000^3731 ≤ 43252082931559^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590381567 5000000000 43252082931559 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850647979/10000000000 : ℝ)^4755 ≤ (5823787652723/50000000000000 : ℝ)^3731 := by
    have hnat : (1850647979 : ℕ)^4755*50000000000000^3731 ≤ 5823787652723^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850647979 10000000000 5823787652723 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353687133/10000000000 : ℝ), (2590381567/5000000000 : ℝ), (-1850647979/10000000000 : ℝ)] ![(45100341751609/100000000000000 : ℝ), (43252082931559/100000000000000 : ℝ), (5823787652723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353687133/10000000000 : ℝ)|^4755 ≤ (45100341751609/100000000000000 : ℝ)^3731
        have hw : |(5353687133/10000000000 : ℝ)|=(5353687133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590381567/5000000000 : ℝ)|^4755 ≤ (43252082931559/100000000000000 : ℝ)^3731
        have hw : |(2590381567/5000000000 : ℝ)|=(2590381567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1850647979/10000000000 : ℝ)|^4755 ≤ (5823787652723/50000000000000 : ℝ)^3731
        have hw : |(-1850647979/10000000000 : ℝ)|=(1850647979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s6_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-853441279/5000000000 : ℝ)*x 0 + (5182833601/10000000000 : ℝ)*x 1 + (1091520201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853441279/5000000000 : ℝ)^4755 ≤ (10506942682307/100000000000000 : ℝ)^3731 := by
    have hnat : (853441279 : ℕ)^4755*100000000000000^3731 ≤ 10506942682307^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853441279 5000000000 10506942682307 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182833601/10000000000 : ℝ)^4755 ≤ (10818528438249/25000000000000 : ℝ)^3731 := by
    have hnat : (5182833601 : ℕ)^4755*25000000000000^3731 ≤ 10818528438249^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182833601 10000000000 10818528438249 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091520201/2000000000 : ℝ)^4755 ≤ (46218943549679/100000000000000 : ℝ)^3731 := by
    have hnat : (1091520201 : ℕ)^4755*100000000000000^3731 ≤ 46218943549679^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091520201 2000000000 46218943549679 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-853441279/5000000000 : ℝ), (5182833601/10000000000 : ℝ), (1091520201/2000000000 : ℝ)] ![(10506942682307/100000000000000 : ℝ), (10818528438249/25000000000000 : ℝ), (46218943549679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-853441279/5000000000 : ℝ)|^4755 ≤ (10506942682307/100000000000000 : ℝ)^3731
        have hw : |(-853441279/5000000000 : ℝ)|=(853441279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182833601/10000000000 : ℝ)|^4755 ≤ (10818528438249/25000000000000 : ℝ)^3731
        have hw : |(5182833601/10000000000 : ℝ)|=(5182833601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091520201/2000000000 : ℝ)|^4755 ≤ (46218943549679/100000000000000 : ℝ)^3731
        have hw : |(1091520201/2000000000 : ℝ)|=(1091520201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s6_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319906221/2500000000 : ℝ)*x 0 + (-12590467/80000000 : ℝ)*x 1 + (5457600921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319906221/2500000000 : ℝ)^4755 ≤ (11076676609911/25000000000000 : ℝ)^3731 := by
    have hnat : (1319906221 : ℕ)^4755*25000000000000^3731 ≤ 11076676609911^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319906221 2500000000 11076676609911 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12590467/80000000 : ℝ)^4755 ≤ (9474350902979/100000000000000 : ℝ)^3731 := by
    have hnat : (12590467 : ℕ)^4755*100000000000000^3731 ≤ 9474350902979^3731*80000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12590467 80000000 9474350902979 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457600921/10000000000 : ℝ)^4755 ≤ (5777367830383/12500000000000 : ℝ)^3731 := by
    have hnat : (5457600921 : ℕ)^4755*12500000000000^3731 ≤ 5777367830383^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457600921 10000000000 5777367830383 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319906221/2500000000 : ℝ), (-12590467/80000000 : ℝ), (5457600921/10000000000 : ℝ)] ![(11076676609911/25000000000000 : ℝ), (9474350902979/100000000000000 : ℝ), (5777367830383/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319906221/2500000000 : ℝ)|^4755 ≤ (11076676609911/25000000000000 : ℝ)^3731
        have hw : |(1319906221/2500000000 : ℝ)|=(1319906221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12590467/80000000 : ℝ)|^4755 ≤ (9474350902979/100000000000000 : ℝ)^3731
        have hw : |(-12590467/80000000 : ℝ)|=(12590467/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457600921/10000000000 : ℝ)|^4755 ≤ (5777367830383/12500000000000 : ℝ)^3731
        have hw : |(5457600921/10000000000 : ℝ)|=(5457600921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s6_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263981239/500000000 : ℝ)*x 0 + (1364400251/2500000000 : ℝ)*x 1 + (-1573808403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263981239/500000000 : ℝ)^4755 ≤ (5538338165917/12500000000000 : ℝ)^3731 := by
    have hnat : (263981239 : ℕ)^4755*12500000000000^3731 ≤ 5538338165917^3731*500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263981239 500000000 5538338165917 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364400251/2500000000 : ℝ)^4755 ≤ (23109471769443/50000000000000 : ℝ)^3731 := by
    have hnat : (1364400251 : ℕ)^4755*50000000000000^3731 ≤ 23109471769443^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364400251 2500000000 23109471769443 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1573808403/10000000000 : ℝ)^4755 ≤ (4737175558901/50000000000000 : ℝ)^3731 := by
    have hnat : (1573808403 : ℕ)^4755*50000000000000^3731 ≤ 4737175558901^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573808403 10000000000 4737175558901 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263981239/500000000 : ℝ), (1364400251/2500000000 : ℝ), (-1573808403/10000000000 : ℝ)] ![(5538338165917/12500000000000 : ℝ), (23109471769443/50000000000000 : ℝ), (4737175558901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263981239/500000000 : ℝ)|^4755 ≤ (5538338165917/12500000000000 : ℝ)^3731
        have hw : |(263981239/500000000 : ℝ)|=(263981239/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364400251/2500000000 : ℝ)|^4755 ≤ (23109471769443/50000000000000 : ℝ)^3731
        have hw : |(1364400251/2500000000 : ℝ)|=(1364400251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1573808403/10000000000 : ℝ)|^4755 ≤ (4737175558901/50000000000000 : ℝ)^3731
        have hw : |(-1573808403/10000000000 : ℝ)|=(1573808403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s6_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526693871/1250000000 : ℝ)*x 0 + (4561280669/10000000000 : ℝ)*x 1 + (155478907/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526693871/1250000000 : ℝ)^4755 ≤ (1329505793789/4000000000000 : ℝ)^3731 := by
    have hnat : (526693871 : ℕ)^4755*4000000000000^3731 ≤ 1329505793789^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526693871 1250000000 1329505793789 4000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4561280669/10000000000 : ℝ)^4755 ≤ (36772291664807/100000000000000 : ℝ)^3731 := by
    have hnat : (4561280669 : ℕ)^4755*100000000000000^3731 ≤ 36772291664807^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561280669 10000000000 36772291664807 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155478907/400000000 : ℝ)^4755 ≤ (29990063479557/100000000000000 : ℝ)^3731 := by
    have hnat : (155478907 : ℕ)^4755*100000000000000^3731 ≤ 29990063479557^3731*400000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155478907 400000000 29990063479557 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526693871/1250000000 : ℝ), (4561280669/10000000000 : ℝ), (155478907/400000000 : ℝ)] ![(1329505793789/4000000000000 : ℝ), (36772291664807/100000000000000 : ℝ), (29990063479557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526693871/1250000000 : ℝ)|^4755 ≤ (1329505793789/4000000000000 : ℝ)^3731
        have hw : |(526693871/1250000000 : ℝ)|=(526693871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4561280669/10000000000 : ℝ)|^4755 ≤ (36772291664807/100000000000000 : ℝ)^3731
        have hw : |(4561280669/10000000000 : ℝ)|=(4561280669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(155478907/400000000 : ℝ)|^4755 ≤ (29990063479557/100000000000000 : ℝ)^3731
        have hw : |(155478907/400000000 : ℝ)|=(155478907/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10429/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8171/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10429/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (2786064240436487/100000000000000000000 : ℝ) := by
    have hpowers : (10429/100000 : ℝ)^4751 ≤ (2786064240436487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10429 : ℕ)^4751*100000000000000000000^1024 ≤ 2786064240436487^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10429 100000 2786064240436487 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10429/100000 : ℝ)) (X := (2786064240436487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16343/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (22394224390096773/100000000000000000000 : ℝ) := by
    have hpowers : (16343/100000 : ℝ)^4751 ≤ (22394224390096773/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16343 : ℕ)^4751*100000000000000000000^1024 ≤ 22394224390096773^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16343 100000 22394224390096773 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16343/100000 : ℝ)) (X := (22394224390096773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002786064240436487/50000000000000000000 : ℝ) ≤ (10000120095450701/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50002786064240436487/50000000000000000000 : ℝ)^1024 ≤ (10000120095450701/10000000000000000 : ℝ)^4751 := by
      have hnat : (50002786064240436487 : ℕ)^1024*10000000000000000^4751 ≤ 10000120095450701^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002786064240436487 50000000000000000000 10000120095450701 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000120095450701/10000000000000000 : ℝ)) (X := (50002786064240436487/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001259014431526663/5000000000000000000 : ℝ) ≤ (5000271333080507/5000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (5001259014431526663/5000000000000000000 : ℝ)^1024 ≤ (5000271333080507/5000000000000000 : ℝ)^4751 := by
      have hnat : (5001259014431526663 : ℕ)^1024*5000000000000000^4751 ≤ 5000271333080507^4751*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001259014431526663 5000000000000000000 5000271333080507 5000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000271333080507/5000000000000000 : ℝ)) (X := (5001259014431526663/5000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022394224390096773/50000000000000000000 : ℝ) ≤ (10000965236871327/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50022394224390096773/50000000000000000000 : ℝ)^1024 ≤ (10000965236871327/10000000000000000 : ℝ)^4751 := by
      have hnat : (50022394224390096773 : ℕ)^1024*10000000000000000^4751 ≤ 10000965236871327^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022394224390096773 50000000000000000000 10000965236871327 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000965236871327/10000000000000000 : ℝ)) (X := (50022394224390096773/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2786064240436487/100000000000000000000 : ℝ) ≤ ((1478297406615493429/1478500000000000000 : ℝ)+2*(422570710313/591400000000000 : ℝ)*(10429/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (1478297406615493429/1478500000000000000 : ℝ)+2*(422570710313/591400000000000 : ℝ)*(10429/100000 : ℝ)=(10000120095450701/10000000000000000 : ℝ) by norm_num, show 1+2*(2786064240436487/100000000000000000000 : ℝ)=(50002786064240436487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22394224390096773/100000000000000000000 : ℝ)+(2786064240436487/100000000000000000000 : ℝ) ≤ ((1478297406615493429/1478500000000000000 : ℝ)+(422570710313/591400000000000 : ℝ)*((16343/100000 : ℝ)+(10429/100000 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (1478297406615493429/1478500000000000000 : ℝ)+(422570710313/591400000000000 : ℝ)*((16343/100000 : ℝ)+(10429/100000 : ℝ))=(5000271333080507/5000000000000000 : ℝ) by norm_num, show 1+(22394224390096773/100000000000000000000 : ℝ)+(2786064240436487/100000000000000000000 : ℝ)=(5001259014431526663/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22394224390096773/100000000000000000000 : ℝ) ≤ ((1478297406615493429/1478500000000000000 : ℝ)+2*(422570710313/591400000000000 : ℝ)*(16343/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (1478297406615493429/1478500000000000000 : ℝ)+2*(422570710313/591400000000000 : ℝ)*(16343/100000 : ℝ)=(10000965236871327/10000000000000000 : ℝ) by norm_num, show 1+2*(22394224390096773/100000000000000000000 : ℝ)=(50022394224390096773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1478297406615493429/1478500000000000000 : ℝ)*(X 1 0+X 2 0)+(422570710313/591400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10429/100000 : ℝ)) (hi := (16343/100000 : ℝ)) (c := (1478297406615493429/1478500000000000000 : ℝ)) (alpha := (422570710313/591400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1478297406615493429/1478500000000000000 : ℝ)*(X 0 1+X 2 1)+(422570710313/591400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10429/100000 : ℝ)) (hi := (16343/100000 : ℝ)) (c := (1478297406615493429/1478500000000000000 : ℝ)) (alpha := (422570710313/591400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1478297406615493429/1478500000000000000 : ℝ)*(X 0 2+X 1 2)+(422570710313/591400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10429/100000 : ℝ)) (hi := (16343/100000 : ℝ)) (c := (1478297406615493429/1478500000000000000 : ℝ)) (alpha := (422570710313/591400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5353687133/10000000000 : ℝ)*X 2 0+(2590381567/5000000000 : ℝ)*X 2 1+(-1850647979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-853441279/5000000000 : ℝ)*X 0 0+(5182833601/10000000000 : ℝ)*X 0 1+(1091520201/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1319906221/2500000000 : ℝ)*X 1 0+(-12590467/80000000 : ℝ)*X 1 1+(5457600921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((263981239/500000000 : ℝ)*X 2 0+(1364400251/2500000000 : ℝ)*X 2 1+(-1573808403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((526693871/1250000000 : ℝ)*X 0 0+(4561280669/10000000000 : ℝ)*X 0 1+(155478907/400000000 : ℝ)*X 0 2+(526693871/1250000000 : ℝ)*X 1 0+(4561280669/10000000000 : ℝ)*X 1 1+(155478907/400000000 : ℝ)*X 1 2+(526693871/1250000000 : ℝ)*X 2 0+(4561280669/10000000000 : ℝ)*X 2 1+(155478907/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (197439112731680630765745189/73925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170566883/50000000000000 : ℝ)*(base19) + (187362867/50000000000000 : ℝ)*(base23) + (98730311/100000000000000 : ℝ)*(lower1) + (5130997/20000000000000 : ℝ)*(upper3) + (54926417/100000000000000 : ℝ)*(lower4) + (61404909/100000000000000 : ℝ)*(upper5) + (2561218931984147/100000000000000 : ℝ)*(major0) + (2561218931984147/100000000000000 : ℝ)*(major1) + (2561218931984147/100000000000000 : ℝ)*(major2) + (44492117/50000000000000 : ℝ)*(sp0) + (363943803235451/10000000000000 : ℝ)*(sp1) + (454929711402593/12500000000000 : ℝ)*(sp2) + (1819718784322271/50000000000000 : ℝ)*(sp3) + (1482999742587001/100000000000000 : ℝ)*(sp4) + (1482999742587001/100000000000000 : ℝ)*(f.failure) + (363943803235451/10000000000000 : ℝ)*(f.sum) + (54369669834851/29570000000000000000000000000 : ℝ)*base65 + (3311794686434452437/147850000000000000000000000000000 : ℝ)*base68 + (236766925335552437/147850000000000000000000000000000 : ℝ)*base70 + (5959777316758297563/147850000000000000000000000000000 : ℝ)*base71 + (150918017985681/29570000000000000000000000000 : ℝ)*base73 + (7188788982313547563/147850000000000000000000000000000 : ℝ)*base75 + (723222792041802437/147850000000000000000000000000000 : ℝ)*base78 + (470244691654352437/147850000000000000000000000000000 : ℝ)*base80 + (105631696228101/29570000000000000000000000000 : ℝ)*base81 + (10999943/2000000000000000000000 : ℝ)*base90 + (10999943/2000000000000000000000 : ℝ)*base92 + (10999943/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1609_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1609_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1609_box_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-89570283/625000000 : ℝ)*x 0 + (541835139/1000000000 : ℝ)*x 1 + (5418350721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89570283/625000000 : ℝ)^4755 ≤ (840852725779/10000000000000 : ℝ)^3731 := by
    have hnat : (89570283 : ℕ)^4755*10000000000000^3731 ≤ 840852725779^3731*625000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89570283 625000000 840852725779 10000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541835139/1000000000 : ℝ)^4755 ≤ (45795739967463/100000000000000 : ℝ)^3731 := by
    have hnat : (541835139 : ℕ)^4755*100000000000000^3731 ≤ 45795739967463^3731*1000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541835139 1000000000 45795739967463 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418350721/10000000000 : ℝ)^4755 ≤ (22897866380607/50000000000000 : ℝ)^3731 := by
    have hnat : (5418350721 : ℕ)^4755*50000000000000^3731 ≤ 22897866380607^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418350721 10000000000 22897866380607 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-89570283/625000000 : ℝ), (541835139/1000000000 : ℝ), (5418350721/10000000000 : ℝ)] ![(840852725779/10000000000000 : ℝ), (45795739967463/100000000000000 : ℝ), (22897866380607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-89570283/625000000 : ℝ)|^4755 ≤ (840852725779/10000000000000 : ℝ)^3731
        have hw : |(-89570283/625000000 : ℝ)|=(89570283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541835139/1000000000 : ℝ)|^4755 ≤ (45795739967463/100000000000000 : ℝ)^3731
        have hw : |(541835139/1000000000 : ℝ)|=(541835139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418350721/10000000000 : ℝ)|^4755 ≤ (22897866380607/50000000000000 : ℝ)^3731
        have hw : |(5418350721/10000000000 : ℝ)|=(5418350721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251148009/10000000000 : ℝ)*x 0 + (-16678761/100000000 : ℝ)*x 1 + (541835113/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251148009/10000000000 : ℝ)^4755 ≤ (2200118217839/5000000000000 : ℝ)^3731 := by
    have hnat : (5251148009 : ℕ)^4755*5000000000000^3731 ≤ 2200118217839^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251148009 10000000000 2200118217839 5000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16678761/100000000 : ℝ)^4755 ≤ (10201898468267/100000000000000 : ℝ)^3731 := by
    have hnat : (16678761 : ℕ)^4755*100000000000000^3731 ≤ 10201898468267^3731*100000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16678761 100000000 10201898468267 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541835113/1000000000 : ℝ)^4755 ≤ (11448934291707/25000000000000 : ℝ)^3731 := by
    have hnat : (541835113 : ℕ)^4755*25000000000000^3731 ≤ 11448934291707^3731*1000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541835113 1000000000 11448934291707 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251148009/10000000000 : ℝ), (-16678761/100000000 : ℝ), (541835113/1000000000 : ℝ)] ![(2200118217839/5000000000000 : ℝ), (10201898468267/100000000000000 : ℝ), (11448934291707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251148009/10000000000 : ℝ)|^4755 ≤ (2200118217839/5000000000000 : ℝ)^3731
        have hw : |(5251148009/10000000000 : ℝ)|=(5251148009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16678761/100000000 : ℝ)|^4755 ≤ (10201898468267/100000000000000 : ℝ)^3731
        have hw : |(-16678761/100000000 : ℝ)|=(16678761/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541835113/1000000000 : ℝ)|^4755 ≤ (11448934291707/25000000000000 : ℝ)^3731
        have hw : |(541835113/1000000000 : ℝ)|=(541835113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050229663/2000000000 : ℝ)*x 0 + (5418350707/10000000000 : ℝ)*x 1 + (-333575253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050229663/2000000000 : ℝ)^4755 ≤ (22001183812339/50000000000000 : ℝ)^3731 := by
    have hnat : (1050229663 : ℕ)^4755*50000000000000^3731 ≤ 22001183812339^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050229663 2000000000 22001183812339 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418350707/10000000000 : ℝ)^4755 ≤ (4579573261041/10000000000000 : ℝ)^3731 := by
    have hnat : (5418350707 : ℕ)^4755*10000000000000^3731 ≤ 4579573261041^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418350707 10000000000 4579573261041 10000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333575253/2000000000 : ℝ)^4755 ≤ (255047493863/2500000000000 : ℝ)^3731 := by
    have hnat : (333575253 : ℕ)^4755*2500000000000^3731 ≤ 255047493863^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333575253 2000000000 255047493863 2500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050229663/2000000000 : ℝ), (5418350707/10000000000 : ℝ), (-333575253/2000000000 : ℝ)] ![(22001183812339/50000000000000 : ℝ), (4579573261041/10000000000000 : ℝ), (255047493863/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050229663/2000000000 : ℝ)|^4755 ≤ (22001183812339/50000000000000 : ℝ)^3731
        have hw : |(1050229663/2000000000 : ℝ)|=(1050229663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418350707/10000000000 : ℝ)|^4755 ≤ (4579573261041/10000000000000 : ℝ)^3731
        have hw : |(5418350707/10000000000 : ℝ)|=(5418350707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333575253/2000000000 : ℝ)|^4755 ≤ (255047493863/2500000000000 : ℝ)^3731
        have hw : |(-333575253/2000000000 : ℝ)|=(333575253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4493317903/10000000000 : ℝ)*x 0 + (4086157793/10000000000 : ℝ)*x 1 + (2043078697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493317903/10000000000 : ℝ)^4755 ≤ (36075443628259/100000000000000 : ℝ)^3731 := by
    have hnat : (4493317903 : ℕ)^4755*100000000000000^3731 ≤ 36075443628259^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493317903 10000000000 36075443628259 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4086157793/10000000000 : ℝ)^4755 ≤ (15981140081093/50000000000000 : ℝ)^3731 := by
    have hnat : (4086157793 : ℕ)^4755*50000000000000^3731 ≤ 15981140081093^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4086157793 10000000000 15981140081093 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043078697/5000000000 : ℝ)^4755 ≤ (31962276184589/100000000000000 : ℝ)^3731 := by
    have hnat : (2043078697 : ℕ)^4755*100000000000000^3731 ≤ 31962276184589^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043078697 5000000000 31962276184589 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493317903/10000000000 : ℝ), (4086157793/10000000000 : ℝ), (2043078697/5000000000 : ℝ)] ![(36075443628259/100000000000000 : ℝ), (15981140081093/50000000000000 : ℝ), (31962276184589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493317903/10000000000 : ℝ)|^4755 ≤ (36075443628259/100000000000000 : ℝ)^3731
        have hw : |(4493317903/10000000000 : ℝ)|=(4493317903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4086157793/10000000000 : ℝ)|^4755 ≤ (15981140081093/50000000000000 : ℝ)^3731
        have hw : |(4086157793/10000000000 : ℝ)|=(4086157793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2043078697/5000000000 : ℝ)|^4755 ≤ (31962276184589/100000000000000 : ℝ)^3731
        have hw : |(2043078697/5000000000 : ℝ)|=(2043078697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199125043/1000000000 : ℝ)*x 0 + (5214047321/10000000000 : ℝ)*x 1 + (2607024109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199125043/1000000000 : ℝ)^4755 ≤ (6393459287743/50000000000000 : ℝ)^3731 := by
    have hnat : (199125043 : ℕ)^4755*50000000000000^3731 ≤ 6393459287743^3731*1000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199125043 1000000000 6393459287743 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214047321/10000000000 : ℝ)^4755 ≤ (1744261436849/4000000000000 : ℝ)^3731 := by
    have hnat : (5214047321 : ℕ)^4755*4000000000000^3731 ≤ 1744261436849^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214047321 10000000000 1744261436849 4000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607024109/5000000000 : ℝ)^4755 ≤ (10901636370507/25000000000000 : ℝ)^3731 := by
    have hnat : (2607024109 : ℕ)^4755*25000000000000^3731 ≤ 10901636370507^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607024109 5000000000 10901636370507 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199125043/1000000000 : ℝ), (5214047321/10000000000 : ℝ), (2607024109/5000000000 : ℝ)] ![(6393459287743/50000000000000 : ℝ), (1744261436849/4000000000000 : ℝ), (10901636370507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199125043/1000000000 : ℝ)|^4755 ≤ (6393459287743/50000000000000 : ℝ)^3731
        have hw : |(-199125043/1000000000 : ℝ)|=(199125043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214047321/10000000000 : ℝ)|^4755 ≤ (1744261436849/4000000000000 : ℝ)^3731
        have hw : |(5214047321/10000000000 : ℝ)|=(5214047321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607024109/5000000000 : ℝ)|^4755 ≤ (10901636370507/25000000000000 : ℝ)^3731
        have hw : |(2607024109/5000000000 : ℝ)|=(2607024109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_5 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696086249/5000000000 : ℝ)*x 0 + (-1754194787/10000000000 : ℝ)*x 1 + (1042809717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696086249/5000000000 : ℝ)^4755 ≤ (11378484167963/25000000000000 : ℝ)^3731 := by
    have hnat : (2696086249 : ℕ)^4755*25000000000000^3731 ≤ 11378484167963^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696086249 5000000000 11378484167963 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1754194787/10000000000 : ℝ)^4755 ≤ (1359939240049/12500000000000 : ℝ)^3731 := by
    have hnat : (1754194787 : ℕ)^4755*12500000000000^3731 ≤ 1359939240049^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754194787 10000000000 1359939240049 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042809717/2000000000 : ℝ)^4755 ≤ (6977047903/16000000000 : ℝ)^3731 := by
    have hnat : (1042809717 : ℕ)^4755*16000000000^3731 ≤ 6977047903^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042809717 2000000000 6977047903 16000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696086249/5000000000 : ℝ), (-1754194787/10000000000 : ℝ), (1042809717/2000000000 : ℝ)] ![(11378484167963/25000000000000 : ℝ), (1359939240049/12500000000000 : ℝ), (6977047903/16000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696086249/5000000000 : ℝ)|^4755 ≤ (11378484167963/25000000000000 : ℝ)^3731
        have hw : |(2696086249/5000000000 : ℝ)|=(2696086249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1754194787/10000000000 : ℝ)|^4755 ≤ (1359939240049/12500000000000 : ℝ)^3731
        have hw : |(-1754194787/10000000000 : ℝ)|=(1754194787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042809717/2000000000 : ℝ)|^4755 ≤ (6977047903/16000000000 : ℝ)^3731
        have hw : |(1042809717/2000000000 : ℝ)|=(1042809717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_6 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348043511/2500000000 : ℝ)*x 0 + (260702333/500000000 : ℝ)*x 1 + (-877097639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348043511/2500000000 : ℝ)^4755 ≤ (45513953302739/100000000000000 : ℝ)^3731 := by
    have hnat : (1348043511 : ℕ)^4755*100000000000000^3731 ≤ 45513953302739^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348043511 2500000000 45513953302739 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260702333/500000000 : ℝ)^4755 ≤ (43606528875863/100000000000000 : ℝ)^3731 := by
    have hnat : (260702333 : ℕ)^4755*100000000000000^3731 ≤ 43606528875863^3731*500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260702333 500000000 43606528875863 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877097639/5000000000 : ℝ)^4755 ≤ (5439758900673/50000000000000 : ℝ)^3731 := by
    have hnat : (877097639 : ℕ)^4755*50000000000000^3731 ≤ 5439758900673^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877097639 5000000000 5439758900673 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348043511/2500000000 : ℝ), (260702333/500000000 : ℝ), (-877097639/5000000000 : ℝ)] ![(45513953302739/100000000000000 : ℝ), (43606528875863/100000000000000 : ℝ), (5439758900673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348043511/2500000000 : ℝ)|^4755 ≤ (45513953302739/100000000000000 : ℝ)^3731
        have hw : |(1348043511/2500000000 : ℝ)|=(1348043511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260702333/500000000 : ℝ)|^4755 ≤ (43606528875863/100000000000000 : ℝ)^3731
        have hw : |(260702333/500000000 : ℝ)|=(260702333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-877097639/5000000000 : ℝ)|^4755 ≤ (5439758900673/50000000000000 : ℝ)^3731
        have hw : |(-877097639/5000000000 : ℝ)|=(877097639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_7 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1963790833/5000000000 : ℝ)*x 0 + (546085159/1250000000 : ℝ)*x 1 + (873736431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963790833/5000000000 : ℝ)^4755 ≤ (1519497372821/5000000000000 : ℝ)^3731 := by
    have hnat : (1963790833 : ℕ)^4755*5000000000000^3731 ≤ 1519497372821^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963790833 5000000000 1519497372821 5000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546085159/1250000000 : ℝ)^4755 ≤ (6961004356197/20000000000000 : ℝ)^3731 := by
    have hnat : (546085159 : ℕ)^4755*20000000000000^3731 ≤ 6961004356197^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546085159 1250000000 6961004356197 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873736431/2000000000 : ℝ)^4755 ≤ (34805030746547/100000000000000 : ℝ)^3731 := by
    have hnat : (873736431 : ℕ)^4755*100000000000000^3731 ≤ 34805030746547^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873736431 2000000000 34805030746547 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1963790833/5000000000 : ℝ), (546085159/1250000000 : ℝ), (873736431/2000000000 : ℝ)] ![(1519497372821/5000000000000 : ℝ), (6961004356197/20000000000000 : ℝ), (34805030746547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1963790833/5000000000 : ℝ)|^4755 ≤ (1519497372821/5000000000000 : ℝ)^3731
        have hw : |(1963790833/5000000000 : ℝ)|=(1963790833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546085159/1250000000 : ℝ)|^4755 ≤ (6961004356197/20000000000000 : ℝ)^3731
        have hw : |(546085159/1250000000 : ℝ)|=(546085159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873736431/2000000000 : ℝ)|^4755 ≤ (34805030746547/100000000000000 : ℝ)^3731
        have hw : |(873736431/2000000000 : ℝ)|=(873736431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_8 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872599037/10000000000 : ℝ)*x 0 + (5068143277/10000000000 : ℝ)*x 1 + (340519187/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872599037/10000000000 : ℝ)^4755 ≤ (5911966975471/50000000000000 : ℝ)^3731 := by
    have hnat : (1872599037 : ℕ)^4755*50000000000000^3731 ≤ 5911966975471^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872599037 10000000000 5911966975471 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5068143277/10000000000 : ℝ)^4755 ≤ (657147025249/1562500000000 : ℝ)^3731 := by
    have hnat : (5068143277 : ℕ)^4755*1562500000000^3731 ≤ 657147025249^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5068143277 10000000000 657147025249 1562500000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340519187/625000000 : ℝ)^4755 ≤ (11529664103081/25000000000000 : ℝ)^3731 := by
    have hnat : (340519187 : ℕ)^4755*25000000000000^3731 ≤ 11529664103081^3731*625000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340519187 625000000 11529664103081 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872599037/10000000000 : ℝ), (5068143277/10000000000 : ℝ), (340519187/625000000 : ℝ)] ![(5911966975471/50000000000000 : ℝ), (657147025249/1562500000000 : ℝ), (11529664103081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872599037/10000000000 : ℝ)|^4755 ≤ (5911966975471/50000000000000 : ℝ)^3731
        have hw : |(-1872599037/10000000000 : ℝ)|=(1872599037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5068143277/10000000000 : ℝ)|^4755 ≤ (657147025249/1562500000000 : ℝ)^3731
        have hw : |(5068143277/10000000000 : ℝ)|=(5068143277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340519187/625000000 : ℝ)|^4755 ≤ (11529664103081/25000000000000 : ℝ)^3731
        have hw : |(340519187/625000000 : ℝ)|=(340519187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_9 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209218589/400000000 : ℝ)*x 0 + (-1654756351/10000000000 : ℝ)*x 1 + (5448307959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209218589/400000000 : ℝ)^4755 ≤ (43781598712349/100000000000000 : ℝ)^3731 := by
    have hnat : (209218589 : ℕ)^4755*100000000000000^3731 ≤ 43781598712349^3731*400000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209218589 400000000 43781598712349 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1654756351/10000000000 : ℝ)^4755 ≤ (5049867214217/50000000000000 : ℝ)^3731 := by
    have hnat : (1654756351 : ℕ)^4755*50000000000000^3731 ≤ 5049867214217^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654756351 10000000000 5049867214217 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448307959/10000000000 : ℝ)^4755 ≤ (23059333422153/50000000000000 : ℝ)^3731 := by
    have hnat : (5448307959 : ℕ)^4755*50000000000000^3731 ≤ 23059333422153^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448307959 10000000000 23059333422153 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209218589/400000000 : ℝ), (-1654756351/10000000000 : ℝ), (5448307959/10000000000 : ℝ)] ![(43781598712349/100000000000000 : ℝ), (5049867214217/50000000000000 : ℝ), (23059333422153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209218589/400000000 : ℝ)|^4755 ≤ (43781598712349/100000000000000 : ℝ)^3731
        have hw : |(209218589/400000000 : ℝ)|=(209218589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1654756351/10000000000 : ℝ)|^4755 ≤ (5049867214217/50000000000000 : ℝ)^3731
        have hw : |(-1654756351/10000000000 : ℝ)|=(1654756351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448307959/10000000000 : ℝ)|^4755 ≤ (23059333422153/50000000000000 : ℝ)^3731
        have hw : |(5448307959/10000000000 : ℝ)|=(5448307959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_10 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615232557/5000000000 : ℝ)*x 0 + (2724154197/5000000000 : ℝ)*x 1 + (-827377607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615232557/5000000000 : ℝ)^4755 ≤ (2189080143107/5000000000000 : ℝ)^3731 := by
    have hnat : (2615232557 : ℕ)^4755*5000000000000^3731 ≤ 2189080143107^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615232557 5000000000 2189080143107 5000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724154197/5000000000 : ℝ)^4755 ≤ (1152966788427/2500000000000 : ℝ)^3731 := by
    have hnat : (2724154197 : ℕ)^4755*2500000000000^3731 ≤ 1152966788427^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724154197 5000000000 1152966788427 2500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827377607/5000000000 : ℝ)^4755 ≤ (2524931396043/25000000000000 : ℝ)^3731 := by
    have hnat : (827377607 : ℕ)^4755*25000000000000^3731 ≤ 2524931396043^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827377607 5000000000 2524931396043 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615232557/5000000000 : ℝ), (2724154197/5000000000 : ℝ), (-827377607/5000000000 : ℝ)] ![(2189080143107/5000000000000 : ℝ), (1152966788427/2500000000000 : ℝ), (2524931396043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615232557/5000000000 : ℝ)|^4755 ≤ (2189080143107/5000000000000 : ℝ)^3731
        have hw : |(2615232557/5000000000 : ℝ)|=(2615232557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724154197/5000000000 : ℝ)|^4755 ≤ (1152966788427/2500000000000 : ℝ)^3731
        have hw : |(2724154197/5000000000 : ℝ)|=(2724154197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-827377607/5000000000 : ℝ)|^4755 ≤ (2524931396043/25000000000000 : ℝ)^3731
        have hw : |(-827377607/5000000000 : ℝ)|=(827377607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_11 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4573873501/10000000000 : ℝ)*x 0 + (202232869/500000000 : ℝ)*x 1 + (161786241/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4573873501/10000000000 : ℝ)^4755 ≤ (36901725249231/100000000000000 : ℝ)^3731 := by
    have hnat : (4573873501 : ℕ)^4755*100000000000000^3731 ≤ 36901725249231^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573873501 10000000000 36901725249231 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202232869/500000000 : ℝ)^4755 ≤ (31549144105609/100000000000000 : ℝ)^3731 := by
    have hnat : (202232869 : ℕ)^4755*100000000000000^3731 ≤ 31549144105609^3731*500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202232869 500000000 31549144105609 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161786241/400000000 : ℝ)^4755 ≤ (31549130635523/100000000000000 : ℝ)^3731 := by
    have hnat : (161786241 : ℕ)^4755*100000000000000^3731 ≤ 31549130635523^3731*400000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161786241 400000000 31549130635523 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4573873501/10000000000 : ℝ), (202232869/500000000 : ℝ), (161786241/400000000 : ℝ)] ![(36901725249231/100000000000000 : ℝ), (31549144105609/100000000000000 : ℝ), (31549130635523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4573873501/10000000000 : ℝ)|^4755 ≤ (36901725249231/100000000000000 : ℝ)^3731
        have hw : |(4573873501/10000000000 : ℝ)|=(4573873501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202232869/500000000 : ℝ)|^4755 ≤ (31549144105609/100000000000000 : ℝ)^3731
        have hw : |(202232869/500000000 : ℝ)|=(202232869/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161786241/400000000 : ℝ)|^4755 ≤ (31549130635523/100000000000000 : ℝ)^3731
        have hw : |(161786241/400000000 : ℝ)|=(161786241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_12 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-775284769/5000000000 : ℝ)*x 0 + (2779158737/5000000000 : ℝ)*x 1 + (324636087/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (775284769/5000000000 : ℝ)^4755 ≤ (9296419257287/100000000000000 : ℝ)^3731 := by
    have hnat : (775284769 : ℕ)^4755*100000000000000^3731 ≤ 9296419257287^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775284769 5000000000 9296419257287 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779158737/5000000000 : ℝ)^4755 ≤ (47308720413523/100000000000000 : ℝ)^3731 := by
    have hnat : (2779158737 : ℕ)^4755*100000000000000^3731 ≤ 47308720413523^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779158737 5000000000 47308720413523 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324636087/625000000 : ℝ)^4755 ≤ (43394860310967/100000000000000 : ℝ)^3731 := by
    have hnat : (324636087 : ℕ)^4755*100000000000000^3731 ≤ 43394860310967^3731*625000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324636087 625000000 43394860310967 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-775284769/5000000000 : ℝ), (2779158737/5000000000 : ℝ), (324636087/625000000 : ℝ)] ![(9296419257287/100000000000000 : ℝ), (47308720413523/100000000000000 : ℝ), (43394860310967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-775284769/5000000000 : ℝ)|^4755 ≤ (9296419257287/100000000000000 : ℝ)^3731
        have hw : |(-775284769/5000000000 : ℝ)|=(775284769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779158737/5000000000 : ℝ)|^4755 ≤ (47308720413523/100000000000000 : ℝ)^3731
        have hw : |(2779158737/5000000000 : ℝ)|=(2779158737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324636087/625000000 : ℝ)|^4755 ≤ (43394860310967/100000000000000 : ℝ)^3731
        have hw : |(324636087/625000000 : ℝ)|=(324636087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_13 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84467119/156250000 : ℝ)*x 0 + (-440571813/2500000000 : ℝ)*x 1 + (5194178163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84467119/156250000 : ℝ)^4755 ≤ (45661612784101/100000000000000 : ℝ)^3731 := by
    have hnat : (84467119 : ℕ)^4755*100000000000000^3731 ≤ 45661612784101^3731*156250000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84467119 156250000 45661612784101 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440571813/2500000000 : ℝ)^4755 ≤ (10943518687469/100000000000000 : ℝ)^3731 := by
    have hnat : (440571813 : ℕ)^4755*100000000000000^3731 ≤ 10943518687469^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440571813 2500000000 10943518687469 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194178163/10000000000 : ℝ)^4755 ≤ (43394868520173/100000000000000 : ℝ)^3731 := by
    have hnat : (5194178163 : ℕ)^4755*100000000000000^3731 ≤ 43394868520173^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194178163 10000000000 43394868520173 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84467119/156250000 : ℝ), (-440571813/2500000000 : ℝ), (5194178163/10000000000 : ℝ)] ![(45661612784101/100000000000000 : ℝ), (10943518687469/100000000000000 : ℝ), (43394868520173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84467119/156250000 : ℝ)|^4755 ≤ (45661612784101/100000000000000 : ℝ)^3731
        have hw : |(84467119/156250000 : ℝ)|=(84467119/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440571813/2500000000 : ℝ)|^4755 ≤ (10943518687469/100000000000000 : ℝ)^3731
        have hw : |(-440571813/2500000000 : ℝ)|=(440571813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194178163/10000000000 : ℝ)|^4755 ≤ (43394868520173/100000000000000 : ℝ)^3731
        have hw : |(5194178163/10000000000 : ℝ)|=(5194178163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_14 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405895729/10000000000 : ℝ)*x 0 + (2597088359/5000000000 : ℝ)*x 1 + (-881144521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405895729/10000000000 : ℝ)^4755 ≤ (45661614000531/100000000000000 : ℝ)^3731 := by
    have hnat : (5405895729 : ℕ)^4755*100000000000000^3731 ≤ 45661614000531^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405895729 10000000000 45661614000531 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597088359/5000000000 : ℝ)^4755 ≤ (21697426567283/50000000000000 : ℝ)^3731 := by
    have hnat : (2597088359 : ℕ)^4755*50000000000000^3731 ≤ 21697426567283^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597088359 5000000000 21697426567283 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (881144521/5000000000 : ℝ)^4755 ≤ (5471766426921/50000000000000 : ℝ)^3731 := by
    have hnat : (881144521 : ℕ)^4755*50000000000000^3731 ≤ 5471766426921^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881144521 5000000000 5471766426921 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405895729/10000000000 : ℝ), (2597088359/5000000000 : ℝ), (-881144521/5000000000 : ℝ)] ![(45661614000531/100000000000000 : ℝ), (21697426567283/50000000000000 : ℝ), (5471766426921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405895729/10000000000 : ℝ)|^4755 ≤ (45661614000531/100000000000000 : ℝ)^3731
        have hw : |(5405895729/10000000000 : ℝ)|=(5405895729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597088359/5000000000 : ℝ)|^4755 ≤ (21697426567283/50000000000000 : ℝ)^3731
        have hw : |(2597088359/5000000000 : ℝ)|=(2597088359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-881144521/5000000000 : ℝ)|^4755 ≤ (5471766426921/50000000000000 : ℝ)^3731
        have hw : |(-881144521/5000000000 : ℝ)|=(881144521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_box_15 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3870933847/10000000000 : ℝ)*x 0 + (43961141/100000000 : ℝ)*x 1 + (549513723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3870933847/10000000000 : ℝ)^4755 ≤ (29832441213751/100000000000000 : ℝ)^3731 := by
    have hnat : (3870933847 : ℕ)^4755*100000000000000^3731 ≤ 29832441213751^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870933847 10000000000 29832441213751 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43961141/100000000 : ℝ)^4755 ≤ (35083801331489/100000000000000 : ℝ)^3731 := by
    have hnat : (43961141 : ℕ)^4755*100000000000000^3731 ≤ 35083801331489^3731*100000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43961141 100000000 35083801331489 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549513723/1250000000 : ℝ)^4755 ≤ (35083757433529/100000000000000 : ℝ)^3731 := by
    have hnat : (549513723 : ℕ)^4755*100000000000000^3731 ≤ 35083757433529^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549513723 1250000000 35083757433529 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3870933847/10000000000 : ℝ), (43961141/100000000 : ℝ), (549513723/1250000000 : ℝ)] ![(29832441213751/100000000000000 : ℝ), (35083801331489/100000000000000 : ℝ), (35083757433529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3870933847/10000000000 : ℝ)|^4755 ≤ (29832441213751/100000000000000 : ℝ)^3731
        have hw : |(3870933847/10000000000 : ℝ)|=(3870933847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43961141/100000000 : ℝ)|^4755 ≤ (35083801331489/100000000000000 : ℝ)^3731
        have hw : |(43961141/100000000 : ℝ)|=(43961141/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549513723/1250000000 : ℝ)|^4755 ≤ (35083757433529/100000000000000 : ℝ)^3731
        have hw : |(549513723/1250000000 : ℝ)|=(549513723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16229/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58183/100000 : ℝ) ∧ (40207/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43907/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10429/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (2786064240436487/100000000000000000000 : ℝ) := by
    have hpowers : (10429/100000 : ℝ)^4751 ≤ (2786064240436487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10429 : ℕ)^4751*100000000000000000000^1024 ≤ 2786064240436487^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10429 100000 2786064240436487 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10429/100000 : ℝ)) (X := (2786064240436487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8171/50000 : ℝ) ^ (4751/1024 : ℝ) ≤ (22387867554802619/100000000000000000000 : ℝ) := by
    have hpowers : (8171/50000 : ℝ)^4751 ≤ (22387867554802619/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8171 : ℕ)^4751*100000000000000000000^1024 ≤ 22387867554802619^1024*50000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8171 50000 22387867554802619 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8171/50000 : ℝ)) (X := (22387867554802619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002786064240436487/50000000000000000000 : ℝ) ≤ (10000120095450701/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50002786064240436487/50000000000000000000 : ℝ)^1024 ≤ (10000120095450701/10000000000000000 : ℝ)^4751 := by
      have hnat : (50002786064240436487 : ℕ)^1024*10000000000000000^4751 ≤ 10000120095450701^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002786064240436487 50000000000000000000 10000120095450701 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000120095450701/10000000000000000 : ℝ)) (X := (50002786064240436487/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012586965897619553/50000000000000000000 : ℝ) ≤ (5000271264588463/5000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50012586965897619553/50000000000000000000 : ℝ)^1024 ≤ (5000271264588463/5000000000000000 : ℝ)^4751 := by
      have hnat : (50012586965897619553 : ℕ)^1024*5000000000000000^4751 ≤ 5000271264588463^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012586965897619553 50000000000000000000 5000271264588463 5000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000271264588463/5000000000000000 : ℝ)) (X := (50012586965897619553/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022387867554802619/50000000000000000000 : ℝ) ≤ (10000964962903151/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50022387867554802619/50000000000000000000 : ℝ)^1024 ≤ (10000964962903151/10000000000000000 : ℝ)^4751 := by
      have hnat : (50022387867554802619 : ℕ)^1024*10000000000000000^4751 ≤ 10000964962903151^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022387867554802619 50000000000000000000 10000964962903151 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000964962903151/10000000000000000 : ℝ)) (X := (50022387867554802619/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2786064240436487/100000000000000000000 : ℝ) ≤ ((19707299667246131321/19710000000000000000 : ℝ)+2*(5632449683/7884000000000 : ℝ)*(10429/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (19707299667246131321/19710000000000000000 : ℝ)+2*(5632449683/7884000000000 : ℝ)*(10429/100000 : ℝ)=(10000120095450701/10000000000000000 : ℝ) by norm_num, show 1+2*(2786064240436487/100000000000000000000 : ℝ)=(50002786064240436487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22387867554802619/100000000000000000000 : ℝ)+(2786064240436487/100000000000000000000 : ℝ) ≤ ((19707299667246131321/19710000000000000000 : ℝ)+(5632449683/7884000000000 : ℝ)*((8171/50000 : ℝ)+(10429/100000 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (19707299667246131321/19710000000000000000 : ℝ)+(5632449683/7884000000000 : ℝ)*((8171/50000 : ℝ)+(10429/100000 : ℝ))=(5000271264588463/5000000000000000 : ℝ) by norm_num, show 1+(22387867554802619/100000000000000000000 : ℝ)+(2786064240436487/100000000000000000000 : ℝ)=(50012586965897619553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22387867554802619/100000000000000000000 : ℝ) ≤ ((19707299667246131321/19710000000000000000 : ℝ)+2*(5632449683/7884000000000 : ℝ)*(8171/50000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (19707299667246131321/19710000000000000000 : ℝ)+2*(5632449683/7884000000000 : ℝ)*(8171/50000 : ℝ)=(10000964962903151/10000000000000000 : ℝ) by norm_num, show 1+2*(22387867554802619/100000000000000000000 : ℝ)=(50022387867554802619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19707299667246131321/19710000000000000000 : ℝ)*(X 1 0+X 2 0)+(5632449683/7884000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10429/100000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (19707299667246131321/19710000000000000000 : ℝ)) (alpha := (5632449683/7884000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19707299667246131321/19710000000000000000 : ℝ)*(X 0 1+X 2 1)+(5632449683/7884000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10429/100000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (19707299667246131321/19710000000000000000 : ℝ)) (alpha := (5632449683/7884000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19707299667246131321/19710000000000000000 : ℝ)*(X 0 2+X 1 2)+(5632449683/7884000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10429/100000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (19707299667246131321/19710000000000000000 : ℝ)) (alpha := (5632449683/7884000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-89570283/625000000 : ℝ)*X 0 0+(541835139/1000000000 : ℝ)*X 0 1+(5418350721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251148009/10000000000 : ℝ)*X 1 0+(-16678761/100000000 : ℝ)*X 1 1+(541835113/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1050229663/2000000000 : ℝ)*X 2 0+(5418350707/10000000000 : ℝ)*X 2 1+(-333575253/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4493317903/10000000000 : ℝ)*X 0 0+(4086157793/10000000000 : ℝ)*X 0 1+(2043078697/5000000000 : ℝ)*X 0 2+(4493317903/10000000000 : ℝ)*X 1 0+(4086157793/10000000000 : ℝ)*X 1 1+(2043078697/5000000000 : ℝ)*X 1 2+(4493317903/10000000000 : ℝ)*X 2 0+(4086157793/10000000000 : ℝ)*X 2 1+(2043078697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-199125043/1000000000 : ℝ)*X 0 0+(5214047321/10000000000 : ℝ)*X 0 1+(2607024109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2696086249/5000000000 : ℝ)*X 1 0+(-1754194787/10000000000 : ℝ)*X 1 1+(1042809717/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1348043511/2500000000 : ℝ)*X 2 0+(260702333/500000000 : ℝ)*X 2 1+(-877097639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1963790833/5000000000 : ℝ)*X 0 0+(546085159/1250000000 : ℝ)*X 0 1+(873736431/2000000000 : ℝ)*X 0 2+(1963790833/5000000000 : ℝ)*X 1 0+(546085159/1250000000 : ℝ)*X 1 1+(873736431/2000000000 : ℝ)*X 1 2+(1963790833/5000000000 : ℝ)*X 2 0+(546085159/1250000000 : ℝ)*X 2 1+(873736431/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1872599037/10000000000 : ℝ)*X 0 0+(5068143277/10000000000 : ℝ)*X 0 1+(340519187/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((209218589/400000000 : ℝ)*X 1 0+(-1654756351/10000000000 : ℝ)*X 1 1+(5448307959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615232557/5000000000 : ℝ)*X 2 0+(2724154197/5000000000 : ℝ)*X 2 1+(-827377607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4573873501/10000000000 : ℝ)*X 0 0+(202232869/500000000 : ℝ)*X 0 1+(161786241/400000000 : ℝ)*X 0 2+(4573873501/10000000000 : ℝ)*X 1 0+(202232869/500000000 : ℝ)*X 1 1+(161786241/400000000 : ℝ)*X 1 2+(4573873501/10000000000 : ℝ)*X 2 0+(202232869/500000000 : ℝ)*X 2 1+(161786241/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-775284769/5000000000 : ℝ)*X 0 0+(2779158737/5000000000 : ℝ)*X 0 1+(324636087/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((84467119/156250000 : ℝ)*X 1 0+(-440571813/2500000000 : ℝ)*X 1 1+(5194178163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5405895729/10000000000 : ℝ)*X 2 0+(2597088359/5000000000 : ℝ)*X 2 1+(-881144521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3870933847/10000000000 : ℝ)*X 0 0+(43961141/100000000 : ℝ)*X 0 1+(549513723/1250000000 : ℝ)*X 0 2+(3870933847/10000000000 : ℝ)*X 1 0+(43961141/100000000 : ℝ)*X 1 1+(549513723/1250000000 : ℝ)*X 1 2+(3870933847/10000000000 : ℝ)*X 2 0+(43961141/100000000 : ℝ)*X 2 1+(549513723/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16229/25000 : ℝ) ≤ (-6663763890939182876058140393219/10265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36383/500000000000 : ℝ)*(lower2) + (89118431/50000000000000 : ℝ)*(lower3) + (2159553/25000000000000 : ℝ)*(upper5) + (52493623517261/3125000000000 : ℝ)*(major0) + (52493623517261/3125000000000 : ℝ)*(major1) + (52493623517261/3125000000000 : ℝ)*(major2) + (6289418709/50000000000000 : ℝ)*(sp2) + (2408589847789591/100000000000000 : ℝ)*(sp4) + (481691132452051/20000000000000 : ℝ)*(sp5) + (1204289929165247/50000000000000 : ℝ)*(sp6) + (972616476331801/100000000000000 : ℝ)*(sp7) + (32367229/1250000000000 : ℝ)*(sp12) + (136774907657/100000000000000 : ℝ)*(sp13) + (20784046393/100000000000000 : ℝ)*(sp15) + (486318630189097/50000000000000 : ℝ)*(f.failure) + (301074054645989/12500000000000 : ℝ)*(f.sum) + (4894937015443/1971000000000000000000000000 : ℝ)*base65 + (214380226815200531/61593750000000000000000000000000 : ℝ)*base67 + (326412219544861969/61593750000000000000000000000000 : ℝ)*base70 + (366261065659674469/61593750000000000000000000000000 : ℝ)*base72 + (170136870847/1971000000000000000000000000 : ℝ)*base73 + (421509457961986969/61593750000000000000000000000000 : ℝ)*base76 + (15647919759575531/61593750000000000000000000000000 : ℝ)*base77 + (87257004432455719/61593750000000000000000000000000 : ℝ)*base80 + (639674712427/394200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (255529/1000000000000000000000 : ℝ)*base89 + (255529/1000000000000000000000 : ℝ)*base91 + (255529/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58183/100000 : ℝ) ≤ (23892524360892100227964572370397/41062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (753559/6250000000000 : ℝ)*(lower2) + (2331421/12500000000000 : ℝ)*(upper4) + (54012347/100000000000000 : ℝ)*(lower5) + (1764449066054743/100000000000000 : ℝ)*(major0) + (1764449066054743/100000000000000 : ℝ)*(major1) + (220556133256843/12500000000000 : ℝ)*(major2) + (310980711200831/12500000000000 : ℝ)*(sp0) + (497569057885503/20000000000000 : ℝ)*(sp1) + (1243924255073591/50000000000000 : ℝ)*(sp2) + (204330101330343/20000000000000 : ℝ)*(sp3) + (4394790393/100000000000000 : ℝ)*(sp5) + (587035363/50000000000000 : ℝ)*(sp6) + (1345308557/50000000000000 : ℝ)*(sp7) + (3994611259/100000000000000 : ℝ)*(sp8) + (1021653197268829/100000000000000 : ℝ)*(f.failure) + (621962421054477/25000000000000 : ℝ)*(f.sum) + (4682712954647/1314000000000000000000000000 : ℝ)*base65 + (1454641166449656167/219000000000000000000000000000000 : ℝ)*base67 + (732085727313980701/82125000000000000000000000000000 : ℝ)*base69 + (1109654898538343833/219000000000000000000000000000000 : ℝ)*base72 + (8262817158467/1314000000000000000000000000 : ℝ)*base73 + (172176389141105701/82125000000000000000000000000000 : ℝ)*base75 + (1889171131772405503/1971000000000000000000000000000000 : ℝ)*base77 + (9577844713401594497/1971000000000000000000000000000000 : ℝ)*base80 + (813561503683/1971000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6812253/2000000000000000000000 : ℝ)*base89 + (6812253/2000000000000000000000 : ℝ)*base91 + (13187747/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40207/50000 : ℝ) ≤ (26416721863157864640635017/32850000000000000000000000 : ℝ) := by norm_num
    linear_combination (68100437/100000000000000 : ℝ)*(lower3) + (79930371/25000000000000 : ℝ)*(upper4) + (3353439/6250000000000 : ℝ)*(lower5) + (233753173747057/12500000000000 : ℝ)*(major0) + (233753173747057/12500000000000 : ℝ)*(major1) + (1870025389976457/100000000000000 : ℝ)*(major2) + (9937464283/100000000000000 : ℝ)*(sp0) + (29395215583/25000000000000 : ℝ)*(sp1) + (222689117391/100000000000000 : ℝ)*(sp2) + (79510823799/100000000000000 : ℝ)*(sp3) + (657612832086841/25000000000000 : ℝ)*(sp8) + (657585921237329/25000000000000 : ℝ)*(sp9) + (164389911043391/6250000000000 : ℝ)*(sp10) + (1082704603151901/100000000000000 : ℝ)*(sp11) + (10827841139757/1000000000000 : ℝ)*(f.failure) + (41100957278307/1562500000000 : ℝ)*(f.sum) + (26842270974757/3942000000000000000000000000 : ℝ)*base66 + (332526218183334797/246375000000000000000000000000000 : ℝ)*base67 + (6417754772538309697/1971000000000000000000000000000000 : ℝ)*base69 + (2268024437038040203/246375000000000000000000000000000 : ℝ)*base72 + (3079492383413/3942000000000000000000000000 : ℝ)*base73 + (5507335425344690303/1971000000000000000000000000000000 : ℝ)*base76 + (816974338867852703/246375000000000000000000000000000 : ℝ)*base78 + (29805439155772297/246375000000000000000000000000000 : ℝ)*base79 + (1274309501683/492750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (303149/20000000000000000000 : ℝ)*base89 + (303149/20000000000000000000 : ℝ)*base91 + (103149/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-43907/50000 : ℝ) ≤ (-72115210580368805513525749499411/82125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381340427/100000000000000 : ℝ)*(lower0) + (93315961/100000000000000 : ℝ)*(upper1) + (30166951/10000000000000 : ℝ)*(upper3) + (59244263/20000000000000 : ℝ)*(lower4) + (956004488585291/50000000000000 : ℝ)*(major0) + (956004488585291/50000000000000 : ℝ)*(major1) + (956004488585291/50000000000000 : ℝ)*(major2) + (1700020577/100000000000000 : ℝ)*(sp4) + (238493536047/100000000000000 : ℝ)*(sp6) + (64461862343/100000000000000 : ℝ)*(sp7) + (54923865301583/2000000000000 : ℝ)*(sp12) + (1373097482549863/50000000000000 : ℝ)*(sp13) + (2745956471563679/100000000000000 : ℝ)*(sp14) + (1107029033956607/100000000000000 : ℝ)*(sp15) + (1107093495818951/100000000000000 : ℝ)*(f.failure) + (1373097482549863/50000000000000 : ℝ)*(f.sum) + (12408149956483/1971000000000000000000000000 : ℝ)*base65 + (1834221797484000589/985500000000000000000000000000000 : ℝ)*base68 + (10559228781242999411/985500000000000000000000000000000 : ℝ)*base69 + (11655606258830999411/985500000000000000000000000000000 : ℝ)*base71 + (6155434357403/985500000000000000000000000 : ℝ)*base73 + (885832038146999411/985500000000000000000000000000000 : ℝ)*base75 + (6843222668554499411/985500000000000000000000000000000 : ℝ)*base77 + (8635348592278499411/985500000000000000000000000000000 : ℝ)*base79 + (16195444763131/1971000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8171207/2000000000000000000000 : ℝ)*base89 + (8171207/2000000000000000000000 : ℝ)*base91 + (8171207/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1609_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16229/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58183/100000 : ℝ) else (40207/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43907/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1609_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1609_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16229/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58183/100000 : ℝ) else (40207/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43907/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1609_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1609_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16229/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58183/100000 : ℝ) else (40207/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43907/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1609_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
