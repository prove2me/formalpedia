-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:52:18.017858+00:00
-- url     : https://prove2.me/submissions/1c53fb32-6f89-4af1-89a3-968c4365aa6c

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
theorem support_rectangle_w1188_s6_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145055677/10000000000 : ℝ)*x 0 + (1078493003/2000000000 : ℝ)*x 1 + (5266200261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145055677/10000000000 : ℝ)^8381 ≤ (13038737313241/100000000000000 : ℝ)^6333 := by
    have hnat : (2145055677 : ℕ)^8381*100000000000000^6333 ≤ 13038737313241^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145055677 10000000000 13038737313241 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078493003/2000000000 : ℝ)^8381 ≤ (22081128741769/50000000000000 : ℝ)^6333 := by
    have hnat : (1078493003 : ℕ)^8381*50000000000000^6333 ≤ 22081128741769^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078493003 2000000000 22081128741769 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266200261/10000000000 : ℝ)^8381 ≤ (534987564803/1250000000000 : ℝ)^6333 := by
    have hnat : (5266200261 : ℕ)^8381*1250000000000^6333 ≤ 534987564803^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266200261 10000000000 534987564803 1250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145055677/10000000000 : ℝ), (1078493003/2000000000 : ℝ), (5266200261/10000000000 : ℝ)] ![(13038737313241/100000000000000 : ℝ), (22081128741769/50000000000000 : ℝ), (534987564803/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145055677/10000000000 : ℝ)|^8381 ≤ (13038737313241/100000000000000 : ℝ)^6333
        have hw : |(-2145055677/10000000000 : ℝ)|=(2145055677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078493003/2000000000 : ℝ)|^8381 ≤ (22081128741769/50000000000000 : ℝ)^6333
        have hw : |(1078493003/2000000000 : ℝ)|=(1078493003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266200261/10000000000 : ℝ)|^8381 ≤ (534987564803/1250000000000 : ℝ)^6333
        have hw : |(5266200261/10000000000 : ℝ)|=(5266200261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s6_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267231971/500000000 : ℝ)*x 0 + (-441818359/2000000000 : ℝ)*x 1 + (5266200309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267231971/500000000 : ℝ)^8381 ≤ (43644667139543/100000000000000 : ℝ)^6333 := by
    have hnat : (267231971 : ℕ)^8381*100000000000000^6333 ≤ 43644667139543^6333*500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267231971 500000000 43644667139543 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441818359/2000000000 : ℝ)^8381 ≤ (6778163572427/50000000000000 : ℝ)^6333 := by
    have hnat : (441818359 : ℕ)^8381*50000000000000^6333 ≤ 6778163572427^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441818359 2000000000 6778163572427 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266200309/10000000000 : ℝ)^8381 ≤ (8559801140099/20000000000000 : ℝ)^6333 := by
    have hnat : (5266200309 : ℕ)^8381*20000000000000^6333 ≤ 8559801140099^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266200309 10000000000 8559801140099 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267231971/500000000 : ℝ), (-441818359/2000000000 : ℝ), (5266200309/10000000000 : ℝ)] ![(43644667139543/100000000000000 : ℝ), (6778163572427/50000000000000 : ℝ), (8559801140099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267231971/500000000 : ℝ)|^8381 ≤ (43644667139543/100000000000000 : ℝ)^6333
        have hw : |(267231971/500000000 : ℝ)|=(267231971/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441818359/2000000000 : ℝ)|^8381 ≤ (6778163572427/50000000000000 : ℝ)^6333
        have hw : |(-441818359/2000000000 : ℝ)|=(441818359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266200309/10000000000 : ℝ)|^8381 ≤ (8559801140099/20000000000000 : ℝ)^6333
        have hw : |(5266200309/10000000000 : ℝ)|=(5266200309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s6_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336159877/2500000000 : ℝ)*x 0 + (2633100079/5000000000 : ℝ)*x 1 + (-2209091877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336159877/2500000000 : ℝ)^8381 ≤ (21822334045273/50000000000000 : ℝ)^6333 := by
    have hnat : (1336159877 : ℕ)^8381*50000000000000^6333 ≤ 21822334045273^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336159877 2500000000 21822334045273 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633100079/5000000000 : ℝ)^8381 ≤ (10699751019111/25000000000000 : ℝ)^6333 := by
    have hnat : (2633100079 : ℕ)^8381*25000000000000^6333 ≤ 10699751019111^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633100079 5000000000 10699751019111 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209091877/10000000000 : ℝ)^8381 ≤ (423635244087/3125000000000 : ℝ)^6333 := by
    have hnat : (2209091877 : ℕ)^8381*3125000000000^6333 ≤ 423635244087^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209091877 10000000000 423635244087 3125000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336159877/2500000000 : ℝ), (2633100079/5000000000 : ℝ), (-2209091877/10000000000 : ℝ)] ![(21822334045273/50000000000000 : ℝ), (10699751019111/25000000000000 : ℝ), (423635244087/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336159877/2500000000 : ℝ)|^8381 ≤ (21822334045273/50000000000000 : ℝ)^6333
        have hw : |(1336159877/2500000000 : ℝ)|=(1336159877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633100079/5000000000 : ℝ)|^8381 ≤ (10699751019111/25000000000000 : ℝ)^6333
        have hw : |(2633100079/5000000000 : ℝ)|=(2633100079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2209091877/10000000000 : ℝ)|^8381 ≤ (423635244087/3125000000000 : ℝ)^6333
        have hw : |(-2209091877/10000000000 : ℝ)|=(2209091877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s6_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272388733/625000000 : ℝ)*x 0 + (132290589/312500000 : ℝ)*x 1 + (4486768229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272388733/625000000 : ℝ)^8381 ≤ (33317080914169/100000000000000 : ℝ)^6333 := by
    have hnat : (272388733 : ℕ)^8381*100000000000000^6333 ≤ 33317080914169^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272388733 625000000 33317080914169 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132290589/312500000 : ℝ)^8381 ≤ (32059174019831/100000000000000 : ℝ)^6333 := by
    have hnat : (132290589 : ℕ)^8381*100000000000000^6333 ≤ 32059174019831^6333*312500000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132290589 312500000 32059174019831 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486768229/10000000000 : ℝ)^8381 ≤ (17311872525137/50000000000000 : ℝ)^6333 := by
    have hnat : (4486768229 : ℕ)^8381*50000000000000^6333 ≤ 17311872525137^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486768229 10000000000 17311872525137 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272388733/625000000 : ℝ), (132290589/312500000 : ℝ), (4486768229/10000000000 : ℝ)] ![(33317080914169/100000000000000 : ℝ), (32059174019831/100000000000000 : ℝ), (17311872525137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272388733/625000000 : ℝ)|^8381 ≤ (33317080914169/100000000000000 : ℝ)^6333
        have hw : |(272388733/625000000 : ℝ)|=(272388733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132290589/312500000 : ℝ)|^8381 ≤ (32059174019831/100000000000000 : ℝ)^6333
        have hw : |(132290589/312500000 : ℝ)|=(132290589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486768229/10000000000 : ℝ)|^8381 ≤ (17311872525137/50000000000000 : ℝ)^6333
        have hw : |(4486768229/10000000000 : ℝ)|=(4486768229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s6_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145060591/10000000000 : ℝ)*x 0 + (526651913/1000000000 : ℝ)*x 1 + (5392144927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145060591/10000000000 : ℝ)^8381 ≤ (50932722041/390625000000 : ℝ)^6333 := by
    have hnat : (2145060591 : ℕ)^8381*390625000000^6333 ≤ 50932722041^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145060591 10000000000 50932722041 390625000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526651913/1000000000 : ℝ)^8381 ≤ (42802434750583/100000000000000 : ℝ)^6333 := by
    have hnat : (526651913 : ℕ)^8381*100000000000000^6333 ≤ 42802434750583^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526651913 1000000000 42802434750583 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392144927/10000000000 : ℝ)^8381 ≤ (44158788394021/100000000000000 : ℝ)^6333 := by
    have hnat : (5392144927 : ℕ)^8381*100000000000000^6333 ≤ 44158788394021^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392144927 10000000000 44158788394021 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145060591/10000000000 : ℝ), (526651913/1000000000 : ℝ), (5392144927/10000000000 : ℝ)] ![(50932722041/390625000000 : ℝ), (42802434750583/100000000000000 : ℝ), (44158788394021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145060591/10000000000 : ℝ)|^8381 ≤ (50932722041/390625000000 : ℝ)^6333
        have hw : |(-2145060591/10000000000 : ℝ)|=(2145060591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526651913/1000000000 : ℝ)|^8381 ≤ (42802434750583/100000000000000 : ℝ)^6333
        have hw : |(526651913/1000000000 : ℝ)|=(526651913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392144927/10000000000 : ℝ)|^8381 ≤ (44158788394021/100000000000000 : ℝ)^6333
        have hw : |(5392144927/10000000000 : ℝ)|=(5392144927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s6_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656271387/5000000000 : ℝ)*x 0 + (-2083147183/10000000000 : ℝ)*x 1 + (2696072419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656271387/5000000000 : ℝ)^8381 ≤ (1353066899029/3125000000000 : ℝ)^6333 := by
    have hnat : (2656271387 : ℕ)^8381*3125000000000^6333 ≤ 1353066899029^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656271387 5000000000 1353066899029 3125000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083147183/10000000000 : ℝ)^8381 ≤ (6271535895001/50000000000000 : ℝ)^6333 := by
    have hnat : (2083147183 : ℕ)^8381*50000000000000^6333 ≤ 6271535895001^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083147183 10000000000 6271535895001 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696072419/5000000000 : ℝ)^8381 ≤ (8831757485891/20000000000000 : ℝ)^6333 := by
    have hnat : (2696072419 : ℕ)^8381*20000000000000^6333 ≤ 8831757485891^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696072419 5000000000 8831757485891 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656271387/5000000000 : ℝ), (-2083147183/10000000000 : ℝ), (2696072419/5000000000 : ℝ)] ![(1353066899029/3125000000000 : ℝ), (6271535895001/50000000000000 : ℝ), (8831757485891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656271387/5000000000 : ℝ)|^8381 ≤ (1353066899029/3125000000000 : ℝ)^6333
        have hw : |(2656271387/5000000000 : ℝ)|=(2656271387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2083147183/10000000000 : ℝ)|^8381 ≤ (6271535895001/50000000000000 : ℝ)^6333
        have hw : |(-2083147183/10000000000 : ℝ)|=(2083147183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696072419/5000000000 : ℝ)|^8381 ≤ (8831757485891/20000000000000 : ℝ)^6333
        have hw : |(2696072419/5000000000 : ℝ)|=(2696072419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s6_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656271403/5000000000 : ℝ)*x 0 + (5392144711/10000000000 : ℝ)*x 1 + (-2083147311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656271403/5000000000 : ℝ)^8381 ≤ (21649070557037/50000000000000 : ℝ)^6333 := by
    have hnat : (2656271403 : ℕ)^8381*50000000000000^6333 ≤ 21649070557037^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656271403 5000000000 21649070557037 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392144711/10000000000 : ℝ)^8381 ≤ (11039696513263/25000000000000 : ℝ)^6333 := by
    have hnat : (5392144711 : ℕ)^8381*25000000000000^6333 ≤ 11039696513263^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392144711 10000000000 11039696513263 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083147311/10000000000 : ℝ)^8381 ≤ (3135768202489/25000000000000 : ℝ)^6333 := by
    have hnat : (2083147311 : ℕ)^8381*25000000000000^6333 ≤ 3135768202489^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083147311 10000000000 3135768202489 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656271403/5000000000 : ℝ), (5392144711/10000000000 : ℝ), (-2083147311/10000000000 : ℝ)] ![(21649070557037/50000000000000 : ℝ), (11039696513263/25000000000000 : ℝ), (3135768202489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656271403/5000000000 : ℝ)|^8381 ≤ (21649070557037/50000000000000 : ℝ)^6333
        have hw : |(2656271403/5000000000 : ℝ)|=(2656271403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392144711/10000000000 : ℝ)|^8381 ≤ (11039696513263/25000000000000 : ℝ)^6333
        have hw : |(5392144711/10000000000 : ℝ)|=(5392144711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083147311/10000000000 : ℝ)|^8381 ≤ (3135768202489/25000000000000 : ℝ)^6333
        have hw : |(-2083147311/10000000000 : ℝ)|=(2083147311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s6_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358229107/10000000000 : ℝ)*x 0 + (224306391/500000000 : ℝ)*x 1 + (1058485479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358229107/10000000000 : ℝ)^8381 ≤ (3331717579989/10000000000000 : ℝ)^6333 := by
    have hnat : (4358229107 : ℕ)^8381*10000000000000^6333 ≤ 3331717579989^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358229107 10000000000 3331717579989 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224306391/500000000 : ℝ)^8381 ≤ (17308602552147/50000000000000 : ℝ)^6333 := by
    have hnat : (224306391 : ℕ)^8381*50000000000000^6333 ≤ 17308602552147^6333*500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224306391 500000000 17308602552147 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058485479/2500000000 : ℝ)^8381 ≤ (32065619085087/100000000000000 : ℝ)^6333 := by
    have hnat : (1058485479 : ℕ)^8381*100000000000000^6333 ≤ 32065619085087^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058485479 2500000000 32065619085087 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358229107/10000000000 : ℝ), (224306391/500000000 : ℝ), (1058485479/2500000000 : ℝ)] ![(3331717579989/10000000000000 : ℝ), (17308602552147/50000000000000 : ℝ), (32065619085087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358229107/10000000000 : ℝ)|^8381 ≤ (3331717579989/10000000000000 : ℝ)^6333
        have hw : |(4358229107/10000000000 : ℝ)|=(4358229107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224306391/500000000 : ℝ)|^8381 ≤ (17308602552147/50000000000000 : ℝ)^6333
        have hw : |(224306391/500000000 : ℝ)|=(224306391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058485479/2500000000 : ℝ)|^8381 ≤ (32065619085087/100000000000000 : ℝ)^6333
        have hw : |(1058485479/2500000000 : ℝ)|=(1058485479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5703/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11381/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (13743014530236183/100000000000000000000 : ℝ) := by
    have hpowers : (11381/100000 : ℝ)^2095 ≤ (13743014530236183/100000000000000000000 : ℝ)^512 := by
      have hnat : (11381 : ℕ)^2095*100000000000000000000^512 ≤ 13743014530236183^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11381 100000 13743014530236183 100000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11381/100000 : ℝ)) (X := (13743014530236183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3527/25000 : ℝ) ^ (2095/512 : ℝ) ≤ (16548376555748997/50000000000000000000 : ℝ) := by
    have hpowers : (3527/25000 : ℝ)^2095 ≤ (16548376555748997/50000000000000000000 : ℝ)^512 := by
      have hnat : (3527 : ℕ)^2095*50000000000000000000^512 ≤ 16548376555748997^512*25000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3527 25000 16548376555748997 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3527/25000 : ℝ)) (X := (16548376555748997/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013743014530236183/50000000000000000000 : ℝ) ≤ (10000671665190537/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (50013743014530236183/50000000000000000000 : ℝ)^512 ≤ (10000671665190537/10000000000000000 : ℝ)^2095 := by
      have hnat : (50013743014530236183 : ℕ)^512*10000000000000000^2095 ≤ 10000671665190537^2095*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013743014530236183 50000000000000000000 10000671665190537 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000671665190537/10000000000000000 : ℝ)) (X := (50013743014530236183/50000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046839767641734177/100000000000000000000 : ℝ) ≤ (10001144521159141/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (100046839767641734177/100000000000000000000 : ℝ)^512 ≤ (10001144521159141/10000000000000000 : ℝ)^2095 := by
      have hnat : (100046839767641734177 : ℕ)^512*10000000000000000^2095 ≤ 10001144521159141^2095*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046839767641734177 100000000000000000000 10001144521159141 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001144521159141/10000000000000000 : ℝ)) (X := (100046839767641734177/100000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016548376555748997/25000000000000000000 : ℝ) ≤ (2000323475425549/2000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25016548376555748997/25000000000000000000 : ℝ)^512 ≤ (2000323475425549/2000000000000000 : ℝ)^2095 := by
      have hnat : (25016548376555748997 : ℕ)^512*2000000000000000^2095 ≤ 2000323475425549^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016548376555748997 25000000000000000000 2000323475425549 2000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000323475425549/2000000000000000 : ℝ)) (X := (25016548376555748997/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13743014530236183/100000000000000000000 : ℝ) ≤ ((27261068483417230151/27270000000000000000 : ℝ)+2*(118213992151/68175000000000 : ℝ)*(11381/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (27261068483417230151/27270000000000000000 : ℝ)+2*(118213992151/68175000000000 : ℝ)*(11381/100000 : ℝ)=(10000671665190537/10000000000000000 : ℝ) by norm_num, show 1+2*(13743014530236183/100000000000000000000 : ℝ)=(50013743014530236183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16548376555748997/50000000000000000000 : ℝ)+(13743014530236183/100000000000000000000 : ℝ) ≤ ((27261068483417230151/27270000000000000000 : ℝ)+(118213992151/68175000000000 : ℝ)*((3527/25000 : ℝ)+(11381/100000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (27261068483417230151/27270000000000000000 : ℝ)+(118213992151/68175000000000 : ℝ)*((3527/25000 : ℝ)+(11381/100000 : ℝ))=(10001144521159141/10000000000000000 : ℝ) by norm_num, show 1+(16548376555748997/50000000000000000000 : ℝ)+(13743014530236183/100000000000000000000 : ℝ)=(100046839767641734177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16548376555748997/50000000000000000000 : ℝ) ≤ ((27261068483417230151/27270000000000000000 : ℝ)+2*(118213992151/68175000000000 : ℝ)*(3527/25000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (27261068483417230151/27270000000000000000 : ℝ)+2*(118213992151/68175000000000 : ℝ)*(3527/25000 : ℝ)=(2000323475425549/2000000000000000 : ℝ) by norm_num, show 1+2*(16548376555748997/50000000000000000000 : ℝ)=(25016548376555748997/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27261068483417230151/27270000000000000000 : ℝ)*(X 1 0+X 2 0)+(118213992151/68175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (27261068483417230151/27270000000000000000 : ℝ)) (alpha := (118213992151/68175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27261068483417230151/27270000000000000000 : ℝ)*(X 0 1+X 2 1)+(118213992151/68175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (27261068483417230151/27270000000000000000 : ℝ)) (alpha := (118213992151/68175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27261068483417230151/27270000000000000000 : ℝ)*(X 0 2+X 1 2)+(118213992151/68175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (27261068483417230151/27270000000000000000 : ℝ)) (alpha := (118213992151/68175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2145055677/10000000000 : ℝ)*X 0 0+(1078493003/2000000000 : ℝ)*X 0 1+(5266200261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267231971/500000000 : ℝ)*X 1 0+(-441818359/2000000000 : ℝ)*X 1 1+(5266200309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336159877/2500000000 : ℝ)*X 2 0+(2633100079/5000000000 : ℝ)*X 2 1+(-2209091877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272388733/625000000 : ℝ)*X 0 0+(132290589/312500000 : ℝ)*X 0 1+(4486768229/10000000000 : ℝ)*X 0 2+(272388733/625000000 : ℝ)*X 1 0+(132290589/312500000 : ℝ)*X 1 1+(4486768229/10000000000 : ℝ)*X 1 2+(272388733/625000000 : ℝ)*X 2 0+(132290589/312500000 : ℝ)*X 2 1+(4486768229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2145060591/10000000000 : ℝ)*X 0 0+(526651913/1000000000 : ℝ)*X 0 1+(5392144927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656271387/5000000000 : ℝ)*X 1 0+(-2083147183/10000000000 : ℝ)*X 1 1+(2696072419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656271403/5000000000 : ℝ)*X 2 0+(5392144711/10000000000 : ℝ)*X 2 1+(-2083147311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358229107/10000000000 : ℝ)*X 0 0+(224306391/500000000 : ℝ)*X 0 1+(1058485479/2500000000 : ℝ)*X 0 2+(4358229107/10000000000 : ℝ)*X 1 0+(224306391/500000000 : ℝ)*X 1 1+(1058485479/2500000000 : ℝ)*X 1 2+(4358229107/10000000000 : ℝ)*X 2 0+(224306391/500000000 : ℝ)*X 2 1+(1058485479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (558499455757804517932384773/50500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2077507253/100000000000000 : ℝ)*(base19) + (1857456687/100000000000000 : ℝ)*(base23) + (187304837/100000000000000 : ℝ)*(lower2) + (52753139/12500000000000 : ℝ)*(upper3) + (54124863/100000000000000 : ℝ)*(upper5) + (5932641441183093/100000000000000 : ℝ)*(major0) + (5932641441183093/100000000000000 : ℝ)*(major1) + (5932641441183093/100000000000000 : ℝ)*(major2) + (395996265373307/5000000000000 : ℝ)*(sp0) + (1979992706387393/25000000000000 : ℝ)*(sp1) + (3959985522800069/50000000000000 : ℝ)*(sp2) + (1972637275285213/50000000000000 : ℝ)*(sp3) + (9519118137/20000000000000 : ℝ)*(sp4) + (35060092423/100000000000000 : ℝ)*(sp7) + (78906192213257/2000000000000 : ℝ)*(f.failure) + (316798916122273/4000000000000 : ℝ)*(f.sum) + (40913322617/252500000000000000000000000 : ℝ)*base66 + (532349815364361591/101000000000000000000000000000000 : ℝ)*base68 + (445805662436638409/101000000000000000000000000000000 : ℝ)*base69 + (699751672164638409/101000000000000000000000000000000 : ℝ)*base71 + (178214556199/126250000000000000000000000 : ℝ)*base73 + (470717290923638409/101000000000000000000000000000000 : ℝ)*base75 + (456670438099361591/101000000000000000000000000000000 : ℝ)*base78 + (731056593581638409/101000000000000000000000000000000 : ℝ)*base79 + (2234725459/31562500000000000000000000 : ℝ)*base82 + (540771/50000000000000000000 : ℝ)*base89 + (540771/50000000000000000000 : ℝ)*base91 + (540771/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11876195220802138853909/2272500000000000000000000000 : ℝ) := by norm_num
    linear_combination (870767603/100000000000000 : ℝ)*(base19) + (234764759/25000000000000 : ℝ)*(base23) + (46405927/100000000000000 : ℝ)*(upper2) + (17585573/100000000000000 : ℝ)*(upper3) + (38023841/25000000000000 : ℝ)*(upper5) + (2981369806467409/50000000000000 : ℝ)*(major0) + (2981369806467409/50000000000000 : ℝ)*(major1) + (2981369806467409/50000000000000 : ℝ)*(major2) + (24836820059/100000000000000 : ℝ)*(sp1) + (6872911903/50000000000000 : ℝ)*(sp2) + (398007681698669/5000000000000 : ℝ)*(sp4) + (7960127926385717/100000000000000 : ℝ)*(sp5) + (3980069474545269/50000000000000 : ℝ)*(sp6) + (3965325417694629/100000000000000 : ℝ)*(sp7) + (3965325417694629/100000000000000 : ℝ)*(f.failure) + (398007681698669/5000000000000 : ℝ)*(f.sum) + (11738706634033/13635000000000000000000000000 : ℝ)*base66 + (1166281483234138751/151500000000000000000000000000000 : ℝ)*base67 + (833181314731861249/151500000000000000000000000000000 : ℝ)*base70 + (895090065207361249/151500000000000000000000000000000 : ℝ)*base72 + (10993553625679/1704375000000000000000000000 : ℝ)*base73 + (1987501161992638751/151500000000000000000000000000000 : ℝ)*base75 + (334209365585638751/151500000000000000000000000000000 : ℝ)*base77 + (4598815656364861249/151500000000000000000000000000000 : ℝ)*base80 + (4653407612779/1704375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8919113/2500000000000000000000 : ℝ)*base90 + (8919113/2500000000000000000000 : ℝ)*base92 + (8919113/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1188_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1188_s7_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-536270059/2500000000 : ℝ)*x 0 + (5392208307/10000000000 : ℝ)*x 1 + (1316610143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536270059/2500000000 : ℝ)^8381 ≤ (13038934871323/100000000000000 : ℝ)^6333 := by
    have hnat : (536270059 : ℕ)^8381*100000000000000^6333 ≤ 13038934871323^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536270059 2500000000 13038934871323 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392208307/10000000000 : ℝ)^8381 ≤ (44159475296377/100000000000000 : ℝ)^6333 := by
    have hnat : (5392208307 : ℕ)^8381*100000000000000^6333 ≤ 44159475296377^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392208307 10000000000 44159475296377 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316610143/2500000000 : ℝ)^8381 ≤ (42801589820971/100000000000000 : ℝ)^6333 := by
    have hnat : (1316610143 : ℕ)^8381*100000000000000^6333 ≤ 42801589820971^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316610143 2500000000 42801589820971 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536270059/2500000000 : ℝ), (5392208307/10000000000 : ℝ), (1316610143/2500000000 : ℝ)] ![(13038934871323/100000000000000 : ℝ), (44159475296377/100000000000000 : ℝ), (42801589820971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536270059/2500000000 : ℝ)|^8381 ≤ (13038934871323/100000000000000 : ℝ)^6333
        have hw : |(-536270059/2500000000 : ℝ)|=(536270059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392208307/10000000000 : ℝ)|^8381 ≤ (44159475296377/100000000000000 : ℝ)^6333
        have hw : |(5392208307/10000000000 : ℝ)|=(5392208307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316610143/2500000000 : ℝ)|^8381 ≤ (42801589820971/100000000000000 : ℝ)^6333
        have hw : |(1316610143/2500000000 : ℝ)|=(1316610143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s7_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344573979/10000000000 : ℝ)*x 0 + (-1104430339/5000000000 : ℝ)*x 1 + (5266440571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344573979/10000000000 : ℝ)^8381 ≤ (8728791985973/20000000000000 : ℝ)^6333 := by
    have hnat : (5344573979 : ℕ)^8381*20000000000000^6333 ≤ 8728791985973^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344573979 10000000000 8728791985973 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104430339/5000000000 : ℝ)^8381 ≤ (338861256333/2500000000000 : ℝ)^6333 := by
    have hnat : (1104430339 : ℕ)^8381*2500000000000^6333 ≤ 338861256333^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104430339 5000000000 338861256333 2500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266440571/10000000000 : ℝ)^8381 ≤ (8560317962043/20000000000000 : ℝ)^6333 := by
    have hnat : (5266440571 : ℕ)^8381*20000000000000^6333 ≤ 8560317962043^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266440571 10000000000 8560317962043 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344573979/10000000000 : ℝ), (-1104430339/5000000000 : ℝ), (5266440571/10000000000 : ℝ)] ![(8728791985973/20000000000000 : ℝ), (338861256333/2500000000000 : ℝ), (8560317962043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344573979/10000000000 : ℝ)|^8381 ≤ (8728791985973/20000000000000 : ℝ)^6333
        have hw : |(5344573979/10000000000 : ℝ)|=(5344573979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1104430339/5000000000 : ℝ)|^8381 ≤ (338861256333/2500000000000 : ℝ)^6333
        have hw : |(-1104430339/5000000000 : ℝ)|=(1104430339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266440571/10000000000 : ℝ)|^8381 ≤ (8560317962043/20000000000000 : ℝ)^6333
        have hw : |(5266440571/10000000000 : ℝ)|=(5266440571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s7_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344573977/10000000000 : ℝ)*x 0 + (1316610143/2500000000 : ℝ)*x 1 + (-1104430339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344573977/10000000000 : ℝ)^8381 ≤ (10910989977063/25000000000000 : ℝ)^6333 := by
    have hnat : (5344573977 : ℕ)^8381*25000000000000^6333 ≤ 10910989977063^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344573977 10000000000 10910989977063 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316610143/2500000000 : ℝ)^8381 ≤ (42801589820971/100000000000000 : ℝ)^6333 := by
    have hnat : (1316610143 : ℕ)^8381*100000000000000^6333 ≤ 42801589820971^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316610143 2500000000 42801589820971 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104430339/5000000000 : ℝ)^8381 ≤ (338861256333/2500000000000 : ℝ)^6333 := by
    have hnat : (1104430339 : ℕ)^8381*2500000000000^6333 ≤ 338861256333^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104430339 5000000000 338861256333 2500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344573977/10000000000 : ℝ), (1316610143/2500000000 : ℝ), (-1104430339/5000000000 : ℝ)] ![(10910989977063/25000000000000 : ℝ), (42801589820971/100000000000000 : ℝ), (338861256333/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344573977/10000000000 : ℝ)|^8381 ≤ (10910989977063/25000000000000 : ℝ)^6333
        have hw : |(5344573977/10000000000 : ℝ)|=(5344573977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316610143/2500000000 : ℝ)|^8381 ≤ (42801589820971/100000000000000 : ℝ)^6333
        have hw : |(1316610143/2500000000 : ℝ)|=(1316610143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1104430339/5000000000 : ℝ)|^8381 ≤ (338861256333/2500000000000 : ℝ)^6333
        have hw : |(-1104430339/5000000000 : ℝ)|=(1104430339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s7_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179116087/5000000000 : ℝ)*x 0 + (846759279/2000000000 : ℝ)*x 1 + (4486267603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179116087/5000000000 : ℝ)^8381 ≤ (33317206828213/100000000000000 : ℝ)^6333 := by
    have hnat : (2179116087 : ℕ)^8381*100000000000000^6333 ≤ 33317206828213^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179116087 5000000000 33317206828213 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846759279/2000000000 : ℝ)^8381 ≤ (32064160592107/100000000000000 : ℝ)^6333 := by
    have hnat : (846759279 : ℕ)^8381*100000000000000^6333 ≤ 32064160592107^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846759279 2000000000 32064160592107 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486267603/10000000000 : ℝ)^8381 ≤ (34618632562019/100000000000000 : ℝ)^6333 := by
    have hnat : (4486267603 : ℕ)^8381*100000000000000^6333 ≤ 34618632562019^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486267603 10000000000 34618632562019 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179116087/5000000000 : ℝ), (846759279/2000000000 : ℝ), (4486267603/10000000000 : ℝ)] ![(33317206828213/100000000000000 : ℝ), (32064160592107/100000000000000 : ℝ), (34618632562019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179116087/5000000000 : ℝ)|^8381 ≤ (33317206828213/100000000000000 : ℝ)^6333
        have hw : |(2179116087/5000000000 : ℝ)|=(2179116087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846759279/2000000000 : ℝ)|^8381 ≤ (32064160592107/100000000000000 : ℝ)^6333
        have hw : |(846759279/2000000000 : ℝ)|=(846759279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486267603/10000000000 : ℝ)|^8381 ≤ (34618632562019/100000000000000 : ℝ)^6333
        have hw : |(4486267603/10000000000 : ℝ)|=(4486267603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s7_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145085017/10000000000 : ℝ)*x 0 + (658344643/1250000000 : ℝ)*x 1 + (5391890587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145085017/10000000000 : ℝ)^8381 ≤ (13038973330841/100000000000000 : ℝ)^6333 := by
    have hnat : (2145085017 : ℕ)^8381*100000000000000^6333 ≤ 13038973330841^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145085017 10000000000 13038973330841 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658344643/1250000000 : ℝ)^8381 ≤ (2675312170759/6250000000000 : ℝ)^6333 := by
    have hnat : (658344643 : ℕ)^8381*6250000000000^6333 ≤ 2675312170759^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658344643 1250000000 2675312170759 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391890587/10000000000 : ℝ)^8381 ≤ (22078015961917/50000000000000 : ℝ)^6333 := by
    have hnat : (5391890587 : ℕ)^8381*50000000000000^6333 ≤ 22078015961917^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391890587 10000000000 22078015961917 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145085017/10000000000 : ℝ), (658344643/1250000000 : ℝ), (5391890587/10000000000 : ℝ)] ![(13038973330841/100000000000000 : ℝ), (2675312170759/6250000000000 : ℝ), (22078015961917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145085017/10000000000 : ℝ)|^8381 ≤ (13038973330841/100000000000000 : ℝ)^6333
        have hw : |(-2145085017/10000000000 : ℝ)|=(2145085017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658344643/1250000000 : ℝ)|^8381 ≤ (2675312170759/6250000000000 : ℝ)^6333
        have hw : |(658344643/1250000000 : ℝ)|=(658344643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391890587/10000000000 : ℝ)|^8381 ≤ (22078015961917/50000000000000 : ℝ)^6333
        have hw : |(5391890587/10000000000 : ℝ)|=(5391890587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s7_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531260359/1000000000 : ℝ)*x 0 + (-1041705331/5000000000 : ℝ)*x 1 + (1347972647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531260359/1000000000 : ℝ)^8381 ≤ (541234959007/1250000000000 : ℝ)^6333 := by
    have hnat : (531260359 : ℕ)^8381*1250000000000^6333 ≤ 541234959007^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531260359 1000000000 541234959007 1250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041705331/5000000000 : ℝ)^8381 ≤ (3136292833757/25000000000000 : ℝ)^6333 := by
    have hnat : (1041705331 : ℕ)^8381*25000000000000^6333 ≤ 3136292833757^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041705331 5000000000 3136292833757 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347972647/2500000000 : ℝ)^8381 ≤ (44156031934671/100000000000000 : ℝ)^6333 := by
    have hnat : (1347972647 : ℕ)^8381*100000000000000^6333 ≤ 44156031934671^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347972647 2500000000 44156031934671 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531260359/1000000000 : ℝ), (-1041705331/5000000000 : ℝ), (1347972647/2500000000 : ℝ)] ![(541234959007/1250000000000 : ℝ), (3136292833757/25000000000000 : ℝ), (44156031934671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531260359/1000000000 : ℝ)|^8381 ≤ (541234959007/1250000000000 : ℝ)^6333
        have hw : |(531260359/1000000000 : ℝ)|=(531260359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041705331/5000000000 : ℝ)|^8381 ≤ (3136292833757/25000000000000 : ℝ)^6333
        have hw : |(-1041705331/5000000000 : ℝ)|=(1041705331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347972647/2500000000 : ℝ)|^8381 ≤ (44156031934671/100000000000000 : ℝ)^6333
        have hw : |(1347972647/2500000000 : ℝ)|=(1347972647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s7_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328150897/2500000000 : ℝ)*x 0 + (5391890589/10000000000 : ℝ)*x 1 + (-2083410663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328150897/2500000000 : ℝ)^8381 ≤ (10824699174747/25000000000000 : ℝ)^6333 := by
    have hnat : (1328150897 : ℕ)^8381*25000000000000^6333 ≤ 10824699174747^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328150897 2500000000 10824699174747 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391890589/10000000000 : ℝ)^8381 ≤ (44156031945509/100000000000000 : ℝ)^6333 := by
    have hnat : (5391890589 : ℕ)^8381*100000000000000^6333 ≤ 44156031945509^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391890589 10000000000 44156031945509 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083410663/10000000000 : ℝ)^8381 ≤ (12545171342997/100000000000000 : ℝ)^6333 := by
    have hnat : (2083410663 : ℕ)^8381*100000000000000^6333 ≤ 12545171342997^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083410663 10000000000 12545171342997 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328150897/2500000000 : ℝ), (5391890589/10000000000 : ℝ), (-2083410663/10000000000 : ℝ)] ![(10824699174747/25000000000000 : ℝ), (44156031945509/100000000000000 : ℝ), (12545171342997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328150897/2500000000 : ℝ)|^8381 ≤ (10824699174747/25000000000000 : ℝ)^6333
        have hw : |(1328150897/2500000000 : ℝ)|=(1328150897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391890589/10000000000 : ℝ)|^8381 ≤ (44156031945509/100000000000000 : ℝ)^6333
        have hw : |(5391890589/10000000000 : ℝ)|=(5391890589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083410663/10000000000 : ℝ)|^8381 ≤ (12545171342997/100000000000000 : ℝ)^6333
        have hw : |(-2083410663/10000000000 : ℝ)|=(2083410663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s7_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089560443/2500000000 : ℝ)*x 0 + (4485632103/10000000000 : ℝ)*x 1 + (264652137/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089560443/2500000000 : ℝ)^8381 ≤ (33317303929609/100000000000000 : ℝ)^6333 := by
    have hnat : (1089560443 : ℕ)^8381*100000000000000^6333 ≤ 33317303929609^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089560443 2500000000 33317303929609 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485632103/10000000000 : ℝ)^8381 ≤ (34612142980479/100000000000000 : ℝ)^6333 := by
    have hnat : (4485632103 : ℕ)^8381*100000000000000^6333 ≤ 34612142980479^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485632103 10000000000 34612142980479 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264652137/625000000 : ℝ)^8381 ≤ (16035276535547/50000000000000 : ℝ)^6333 := by
    have hnat : (264652137 : ℕ)^8381*50000000000000^6333 ≤ 16035276535547^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264652137 625000000 16035276535547 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089560443/2500000000 : ℝ), (4485632103/10000000000 : ℝ), (264652137/625000000 : ℝ)] ![(33317303929609/100000000000000 : ℝ), (34612142980479/100000000000000 : ℝ), (16035276535547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089560443/2500000000 : ℝ)|^8381 ≤ (33317303929609/100000000000000 : ℝ)^6333
        have hw : |(1089560443/2500000000 : ℝ)|=(1089560443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485632103/10000000000 : ℝ)|^8381 ≤ (34612142980479/100000000000000 : ℝ)^6333
        have hw : |(4485632103/10000000000 : ℝ)|=(4485632103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264652137/625000000 : ℝ)|^8381 ≤ (16035276535547/50000000000000 : ℝ)^6333
        have hw : |(264652137/625000000 : ℝ)|=(264652137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2853/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5703/50000 : ℝ) ^ (2095/512 : ℝ) ≤ (6933479932300301/50000000000000000000 : ℝ) := by
    have hpowers : (5703/50000 : ℝ)^2095 ≤ (6933479932300301/50000000000000000000 : ℝ)^512 := by
      have hnat : (5703 : ℕ)^2095*50000000000000000000^512 ≤ 6933479932300301^512*50000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5703 50000 6933479932300301 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5703/50000 : ℝ)) (X := (6933479932300301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14081/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (8209585274336057/25000000000000000000 : ℝ) := by
    have hpowers : (14081/100000 : ℝ)^2095 ≤ (8209585274336057/25000000000000000000 : ℝ)^512 := by
      have hnat : (14081 : ℕ)^2095*25000000000000000000^512 ≤ 8209585274336057^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14081 100000 8209585274336057 25000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14081/100000 : ℝ)) (X := (8209585274336057/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006933479932300301/25000000000000000000 : ℝ) ≤ (1250084715270239/1250000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25006933479932300301/25000000000000000000 : ℝ)^512 ≤ (1250084715270239/1250000000000000 : ℝ)^2095 := by
      have hnat : (25006933479932300301 : ℕ)^512*1250000000000000^2095 ≤ 1250084715270239^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006933479932300301 25000000000000000000 1250084715270239 1250000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250084715270239/1250000000000000 : ℝ)) (X := (25006933479932300301/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004670530096194483/10000000000000000000 : ℝ) ≤ (250028530901749/250000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (10004670530096194483/10000000000000000000 : ℝ)^512 ≤ (250028530901749/250000000000000 : ℝ)^2095 := by
      have hnat : (10004670530096194483 : ℕ)^512*250000000000000^2095 ≤ 250028530901749^2095*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004670530096194483 10000000000000000000 250028530901749 250000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250028530901749/250000000000000 : ℝ)) (X := (10004670530096194483/10000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508209585274336057/12500000000000000000 : ℝ) ≤ (1250200593747251/1250000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (12508209585274336057/12500000000000000000 : ℝ)^512 ≤ (1250200593747251/1250000000000000 : ℝ)^2095 := by
      have hnat : (12508209585274336057 : ℕ)^512*1250000000000000^2095 ≤ 1250200593747251^2095*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508209585274336057 12500000000000000000 1250200593747251 1250000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250200593747251/1250000000000000 : ℝ)) (X := (12508209585274336057/12500000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6933479932300301/50000000000000000000 : ℝ) ≤ ((3342654903439090453/3343750000000000000 : ℝ)+2*(28969619253/16718750000000 : ℝ)*(5703/50000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (3342654903439090453/3343750000000000000 : ℝ)+2*(28969619253/16718750000000 : ℝ)*(5703/50000 : ℝ)=(1250084715270239/1250000000000000 : ℝ) by norm_num, show 1+2*(6933479932300301/50000000000000000000 : ℝ)=(25006933479932300301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8209585274336057/25000000000000000000 : ℝ)+(6933479932300301/50000000000000000000 : ℝ) ≤ ((3342654903439090453/3343750000000000000 : ℝ)+(28969619253/16718750000000 : ℝ)*((14081/100000 : ℝ)+(5703/50000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (3342654903439090453/3343750000000000000 : ℝ)+(28969619253/16718750000000 : ℝ)*((14081/100000 : ℝ)+(5703/50000 : ℝ))=(250028530901749/250000000000000 : ℝ) by norm_num, show 1+(8209585274336057/25000000000000000000 : ℝ)+(6933479932300301/50000000000000000000 : ℝ)=(10004670530096194483/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8209585274336057/25000000000000000000 : ℝ) ≤ ((3342654903439090453/3343750000000000000 : ℝ)+2*(28969619253/16718750000000 : ℝ)*(14081/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (3342654903439090453/3343750000000000000 : ℝ)+2*(28969619253/16718750000000 : ℝ)*(14081/100000 : ℝ)=(1250200593747251/1250000000000000 : ℝ) by norm_num, show 1+2*(8209585274336057/25000000000000000000 : ℝ)=(12508209585274336057/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3342654903439090453/3343750000000000000 : ℝ)*(X 1 0+X 2 0)+(28969619253/16718750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (3342654903439090453/3343750000000000000 : ℝ)) (alpha := (28969619253/16718750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3342654903439090453/3343750000000000000 : ℝ)*(X 0 1+X 2 1)+(28969619253/16718750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (3342654903439090453/3343750000000000000 : ℝ)) (alpha := (28969619253/16718750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3342654903439090453/3343750000000000000 : ℝ)*(X 0 2+X 1 2)+(28969619253/16718750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (3342654903439090453/3343750000000000000 : ℝ)) (alpha := (28969619253/16718750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-536270059/2500000000 : ℝ)*X 0 0+(5392208307/10000000000 : ℝ)*X 0 1+(1316610143/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344573979/10000000000 : ℝ)*X 1 0+(-1104430339/5000000000 : ℝ)*X 1 1+(5266440571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344573977/10000000000 : ℝ)*X 2 0+(1316610143/2500000000 : ℝ)*X 2 1+(-1104430339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179116087/5000000000 : ℝ)*X 0 0+(846759279/2000000000 : ℝ)*X 0 1+(4486267603/10000000000 : ℝ)*X 0 2+(2179116087/5000000000 : ℝ)*X 1 0+(846759279/2000000000 : ℝ)*X 1 1+(4486267603/10000000000 : ℝ)*X 1 2+(2179116087/5000000000 : ℝ)*X 2 0+(846759279/2000000000 : ℝ)*X 2 1+(4486267603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2145085017/10000000000 : ℝ)*X 0 0+(658344643/1250000000 : ℝ)*X 0 1+(5391890587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531260359/1000000000 : ℝ)*X 1 0+(-1041705331/5000000000 : ℝ)*X 1 1+(1347972647/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328150897/2500000000 : ℝ)*X 2 0+(5391890589/10000000000 : ℝ)*X 2 1+(-2083410663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089560443/2500000000 : ℝ)*X 0 0+(4485632103/10000000000 : ℝ)*X 0 1+(264652137/625000000 : ℝ)*X 0 2+(1089560443/2500000000 : ℝ)*X 1 0+(4485632103/10000000000 : ℝ)*X 1 1+(264652137/625000000 : ℝ)*X 1 2+(1089560443/2500000000 : ℝ)*X 2 0+(4485632103/10000000000 : ℝ)*X 2 1+(264652137/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108672744246162363489330249/41796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255461147/50000000000000 : ℝ)*(base19) + (472893893/100000000000000 : ℝ)*(base23) + (9367161/50000000000000 : ℝ)*(lower2) + (32570107/50000000000000 : ℝ)*(upper3) + (37825001/100000000000000 : ℝ)*(upper5) + (744503485268931/12500000000000 : ℝ)*(major0) + (744503485268931/12500000000000 : ℝ)*(major1) + (744503485268931/12500000000000 : ℝ)*(major2) + (1590235930991669/20000000000000 : ℝ)*(sp0) + (496949572910931/6250000000000 : ℝ)*(sp1) + (7951193204603297/100000000000000 : ℝ)*(sp2) + (990213612362321/25000000000000 : ℝ)*(sp3) + (2804507769/20000000000000 : ℝ)*(sp4) + (1510137809/20000000000000 : ℝ)*(sp7) + (495107750017291/12500000000000 : ℝ)*(f.failure) + (795119367749719/10000000000000 : ℝ)*(f.sum) + (50950768091379/13375000000000000000000000000 : ℝ)*base65 + (523105909922878007/41796875000000000000000000000000 : ℝ)*base68 + (416406716203431191/20898437500000000000000000000000 : ℝ)*base70 + (517342494106471757/41796875000000000000000000000000 : ℝ)*base72 + (61630612554879/13375000000000000000000000000 : ℝ)*base73 + (838212763628346757/41796875000000000000000000000000 : ℝ)*base76 + (21984923835633977/2612304687500000000000000000000 : ℝ)*base78 + (259808672915149941/20898437500000000000000000000000 : ℝ)*base80 + (44990944928373/6687500000000000000000000000 : ℝ)*base82 + (4385127/312500000000000000000 : ℝ)*base90 + (4385127/312500000000000000000 : ℝ)*base92 + (4385127/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72645806191559920072216767/8359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1575236011/100000000000000 : ℝ)*(base19) + (1709078333/100000000000000 : ℝ)*(base23) + (175086839/100000000000000 : ℝ)*(upper3) + (31226257/50000000000000 : ℝ)*(lower4) + (177402543/100000000000000 : ℝ)*(upper5) + (299309791556337/5000000000000 : ℝ)*(major0) + (299309791556337/5000000000000 : ℝ)*(major1) + (299309791556337/5000000000000 : ℝ)*(major2) + (43969567191/100000000000000 : ℝ)*(sp1) + (2948496239/6250000000000 : ℝ)*(sp2) + (7991467162339653/100000000000000 : ℝ)*(sp4) + (1997855404384113/25000000000000 : ℝ)*(sp5) + (998927284665187/12500000000000 : ℝ)*(sp6) + (1990462105117919/50000000000000 : ℝ)*(sp7) + (1990462105117919/50000000000000 : ℝ)*(f.failure) + (7991467162339653/100000000000000 : ℝ)*(f.sum) + (4924101307921/2675000000000000000000000000 : ℝ)*base66 + (56117567493363161/16718750000000000000000000000000 : ℝ)*base67 + (255766512473519411/16718750000000000000000000000000 : ℝ)*base69 + (187551062461793089/16718750000000000000000000000000 : ℝ)*base72 + (334762826069/167187500000000000000000000 : ℝ)*base73 + (68093623039293089/16718750000000000000000000000000 : ℝ)*base76 + (83531731774300661/16718750000000000000000000000000 : ℝ)*base77 + (13288987793363161/16718750000000000000000000000000 : ℝ)*base79 + (986185536863/334375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5679243/1250000000000000000000 : ℝ)*base90 + (5679243/1250000000000000000000 : ℝ)*base92 + (5679243/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1188_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2853/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1188_s8_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429016183/2000000000 : ℝ)*x 0 + (1078431327/2000000000 : ℝ)*x 1 + (5266492131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429016183/2000000000 : ℝ)^8381 ≤ (13038940333361/100000000000000 : ℝ)^6333 := by
    have hnat : (429016183 : ℕ)^8381*100000000000000^6333 ≤ 13038940333361^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429016183 2000000000 13038940333361 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078431327/2000000000 : ℝ)^8381 ≤ (22079457641633/50000000000000 : ℝ)^6333 := by
    have hnat : (1078431327 : ℕ)^8381*50000000000000^6333 ≤ 22079457641633^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078431327 2000000000 22079457641633 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266492131/10000000000 : ℝ)^8381 ≤ (10700536090677/25000000000000 : ℝ)^6333 := by
    have hnat : (5266492131 : ℕ)^8381*25000000000000^6333 ≤ 10700536090677^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266492131 10000000000 10700536090677 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429016183/2000000000 : ℝ), (1078431327/2000000000 : ℝ), (5266492131/10000000000 : ℝ)] ![(13038940333361/100000000000000 : ℝ), (22079457641633/50000000000000 : ℝ), (10700536090677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429016183/2000000000 : ℝ)|^8381 ≤ (13038940333361/100000000000000 : ℝ)^6333
        have hw : |(-429016183/2000000000 : ℝ)|=(429016183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078431327/2000000000 : ℝ)|^8381 ≤ (22079457641633/50000000000000 : ℝ)^6333
        have hw : |(1078431327/2000000000 : ℝ)|=(1078431327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266492131/10000000000 : ℝ)|^8381 ≤ (10700536090677/25000000000000 : ℝ)^6333
        have hw : |(5266492131/10000000000 : ℝ)|=(5266492131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s8_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344562037/10000000000 : ℝ)*x 0 + (-88352331/400000000 : ℝ)*x 1 + (1053298427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344562037/10000000000 : ℝ)^8381 ≤ (43643830875019/100000000000000 : ℝ)^6333 := by
    have hnat : (5344562037 : ℕ)^8381*100000000000000^6333 ≤ 43643830875019^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344562037 10000000000 43643830875019 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88352331/400000000 : ℝ)^8381 ≤ (1355402469957/10000000000000 : ℝ)^6333 := by
    have hnat : (88352331 : ℕ)^8381*10000000000000^6333 ≤ 1355402469957^6333*400000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88352331 400000000 1355402469957 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053298427/2000000000 : ℝ)^8381 ≤ (4280214440573/10000000000000 : ℝ)^6333 := by
    have hnat : (1053298427 : ℕ)^8381*10000000000000^6333 ≤ 4280214440573^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053298427 2000000000 4280214440573 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344562037/10000000000 : ℝ), (-88352331/400000000 : ℝ), (1053298427/2000000000 : ℝ)] ![(43643830875019/100000000000000 : ℝ), (1355402469957/10000000000000 : ℝ), (4280214440573/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344562037/10000000000 : ℝ)|^8381 ≤ (43643830875019/100000000000000 : ℝ)^6333
        have hw : |(5344562037/10000000000 : ℝ)|=(5344562037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88352331/400000000 : ℝ)|^8381 ≤ (1355402469957/10000000000000 : ℝ)^6333
        have hw : |(-88352331/400000000 : ℝ)|=(88352331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053298427/2000000000 : ℝ)|^8381 ≤ (4280214440573/10000000000000 : ℝ)^6333
        have hw : |(1053298427/2000000000 : ℝ)|=(1053298427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s8_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336140511/2500000000 : ℝ)*x 0 + (5266492133/10000000000 : ℝ)*x 1 + (-2208808269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336140511/2500000000 : ℝ)^8381 ≤ (43643830950667/100000000000000 : ℝ)^6333 := by
    have hnat : (1336140511 : ℕ)^8381*100000000000000^6333 ≤ 43643830950667^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336140511 2500000000 43643830950667 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266492133/10000000000 : ℝ)^8381 ≤ (42802144384219/100000000000000 : ℝ)^6333 := by
    have hnat : (5266492133 : ℕ)^8381*100000000000000^6333 ≤ 42802144384219^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266492133 10000000000 42802144384219 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208808269/10000000000 : ℝ)^8381 ≤ (6777012325423/50000000000000 : ℝ)^6333 := by
    have hnat : (2208808269 : ℕ)^8381*50000000000000^6333 ≤ 6777012325423^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208808269 10000000000 6777012325423 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336140511/2500000000 : ℝ), (5266492133/10000000000 : ℝ), (-2208808269/10000000000 : ℝ)] ![(43643830950667/100000000000000 : ℝ), (42802144384219/100000000000000 : ℝ), (6777012325423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336140511/2500000000 : ℝ)|^8381 ≤ (43643830950667/100000000000000 : ℝ)^6333
        have hw : |(1336140511/2500000000 : ℝ)|=(1336140511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266492133/10000000000 : ℝ)|^8381 ≤ (42802144384219/100000000000000 : ℝ)^6333
        have hw : |(5266492133/10000000000 : ℝ)|=(5266492133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2208808269/10000000000 : ℝ)|^8381 ≤ (6777012325423/50000000000000 : ℝ)^6333
        have hw : |(-2208808269/10000000000 : ℝ)|=(2208808269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s8_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179117397/5000000000 : ℝ)*x 0 + (4233899673/10000000000 : ℝ)*x 1 + (2243081823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179117397/5000000000 : ℝ)^8381 ≤ (33317233334317/100000000000000 : ℝ)^6333 := by
    have hnat : (2179117397 : ℕ)^8381*100000000000000^6333 ≤ 33317233334317^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179117397 5000000000 33317233334317 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233899673/10000000000 : ℝ)^8381 ≤ (32065195700407/100000000000000 : ℝ)^6333 := by
    have hnat : (4233899673 : ℕ)^8381*100000000000000^6333 ≤ 32065195700407^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233899673 10000000000 32065195700407 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243081823/5000000000 : ℝ)^8381 ≤ (8654392739107/25000000000000 : ℝ)^6333 := by
    have hnat : (2243081823 : ℕ)^8381*25000000000000^6333 ≤ 8654392739107^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243081823 5000000000 8654392739107 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179117397/5000000000 : ℝ), (4233899673/10000000000 : ℝ), (2243081823/5000000000 : ℝ)] ![(33317233334317/100000000000000 : ℝ), (32065195700407/100000000000000 : ℝ), (8654392739107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179117397/5000000000 : ℝ)|^8381 ≤ (33317233334317/100000000000000 : ℝ)^6333
        have hw : |(2179117397/5000000000 : ℝ)|=(2179117397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233899673/10000000000 : ℝ)|^8381 ≤ (32065195700407/100000000000000 : ℝ)^6333
        have hw : |(4233899673/10000000000 : ℝ)|=(4233899673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243081823/5000000000 : ℝ)|^8381 ≤ (8654392739107/25000000000000 : ℝ)^6333
        have hw : |(2243081823/5000000000 : ℝ)|=(2243081823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s8_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072542809/5000000000 : ℝ)*x 0 + (5266808203/10000000000 : ℝ)*x 1 + (5391839469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072542809/5000000000 : ℝ)^8381 ≤ (13038978165431/100000000000000 : ℝ)^6333 := by
    have hnat : (1072542809 : ℕ)^8381*100000000000000^6333 ≤ 13038978165431^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072542809 5000000000 13038978165431 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266808203/10000000000 : ℝ)^8381 ≤ (5350692988351/12500000000000 : ℝ)^6333 := by
    have hnat : (5266808203 : ℕ)^8381*12500000000000^6333 ≤ 5350692988351^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266808203 10000000000 5350692988351 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391839469/10000000000 : ℝ)^8381 ≤ (11038869481359/25000000000000 : ℝ)^6333 := by
    have hnat : (5391839469 : ℕ)^8381*25000000000000^6333 ≤ 11038869481359^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391839469 10000000000 11038869481359 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072542809/5000000000 : ℝ), (5266808203/10000000000 : ℝ), (5391839469/10000000000 : ℝ)] ![(13038978165431/100000000000000 : ℝ), (5350692988351/12500000000000 : ℝ), (11038869481359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072542809/5000000000 : ℝ)|^8381 ≤ (13038978165431/100000000000000 : ℝ)^6333
        have hw : |(-1072542809/5000000000 : ℝ)|=(1072542809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266808203/10000000000 : ℝ)|^8381 ≤ (5350692988351/12500000000000 : ℝ)^6333
        have hw : |(5266808203/10000000000 : ℝ)|=(5266808203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391839469/10000000000 : ℝ)|^8381 ≤ (11038869481359/25000000000000 : ℝ)^6333
        have hw : |(5391839469/10000000000 : ℝ)|=(5391839469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s8_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312617777/10000000000 : ℝ)*x 0 + (-2083461001/10000000000 : ℝ)*x 1 + (1078367891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312617777/10000000000 : ℝ)^8381 ≤ (21649474869809/50000000000000 : ℝ)^6333 := by
    have hnat : (5312617777 : ℕ)^8381*50000000000000^6333 ≤ 21649474869809^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312617777 10000000000 21649474869809 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083461001/10000000000 : ℝ)^8381 ≤ (1254557247353/10000000000000 : ℝ)^6333 := by
    have hnat : (2083461001 : ℕ)^8381*10000000000000^6333 ≤ 1254557247353^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083461001 10000000000 1254557247353 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078367891/2000000000 : ℝ)^8381 ≤ (4415547777371/10000000000000 : ℝ)^6333 := by
    have hnat : (1078367891 : ℕ)^8381*10000000000000^6333 ≤ 4415547777371^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078367891 2000000000 4415547777371 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312617777/10000000000 : ℝ), (-2083461001/10000000000 : ℝ), (1078367891/2000000000 : ℝ)] ![(21649474869809/50000000000000 : ℝ), (1254557247353/10000000000000 : ℝ), (4415547777371/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312617777/10000000000 : ℝ)|^8381 ≤ (21649474869809/50000000000000 : ℝ)^6333
        have hw : |(5312617777/10000000000 : ℝ)|=(5312617777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2083461001/10000000000 : ℝ)|^8381 ≤ (1254557247353/10000000000000 : ℝ)^6333
        have hw : |(-2083461001/10000000000 : ℝ)|=(2083461001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078367891/2000000000 : ℝ)|^8381 ≤ (4415547777371/10000000000000 : ℝ)^6333
        have hw : |(1078367891/2000000000 : ℝ)|=(1078367891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s8_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312617771/10000000000 : ℝ)*x 0 + (5391839477/10000000000 : ℝ)*x 1 + (-104173049/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312617771/10000000000 : ℝ)^8381 ≤ (43298949674903/100000000000000 : ℝ)^6333 := by
    have hnat : (5312617771 : ℕ)^8381*100000000000000^6333 ≤ 43298949674903^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312617771 10000000000 43298949674903 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391839477/10000000000 : ℝ)^8381 ≤ (44155478012137/100000000000000 : ℝ)^6333 := by
    have hnat : (5391839477 : ℕ)^8381*100000000000000^6333 ≤ 44155478012137^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391839477 10000000000 44155478012137 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104173049/500000000 : ℝ)^8381 ≤ (6272786153093/50000000000000 : ℝ)^6333 := by
    have hnat : (104173049 : ℕ)^8381*50000000000000^6333 ≤ 6272786153093^6333*500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104173049 500000000 6272786153093 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312617771/10000000000 : ℝ), (5391839477/10000000000 : ℝ), (-104173049/500000000 : ℝ)] ![(43298949674903/100000000000000 : ℝ), (44155478012137/100000000000000 : ℝ), (6272786153093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312617771/10000000000 : ℝ)|^8381 ≤ (43298949674903/100000000000000 : ℝ)^6333
        have hw : |(5312617771/10000000000 : ℝ)|=(5312617771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391839477/10000000000 : ℝ)|^8381 ≤ (44155478012137/100000000000000 : ℝ)^6333
        have hw : |(5391839477/10000000000 : ℝ)|=(5391839477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104173049/500000000 : ℝ)|^8381 ≤ (6272786153093/50000000000000 : ℝ)^6333
        have hw : |(-104173049/500000000 : ℝ)|=(104173049/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s8_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179122183/5000000000 : ℝ)*x 0 + (1121382291/2500000000 : ℝ)*x 1 + (8270579/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179122183/5000000000 : ℝ)^8381 ≤ (6663466034539/20000000000000 : ℝ)^6333 := by
    have hnat : (2179122183 : ℕ)^8381*20000000000000^6333 ≤ 6663466034539^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179122183 5000000000 6663466034539 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121382291/2500000000 : ℝ)^8381 ≤ (34611091818791/100000000000000 : ℝ)^6333 := by
    have hnat : (1121382291 : ℕ)^8381*100000000000000^6333 ≤ 34611091818791^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121382291 2500000000 34611091818791 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8270579/19531250 : ℝ)^8381 ≤ (16035788993119/50000000000000 : ℝ)^6333 := by
    have hnat : (8270579 : ℕ)^8381*50000000000000^6333 ≤ 16035788993119^6333*19531250^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8270579 19531250 16035788993119 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179122183/5000000000 : ℝ), (1121382291/2500000000 : ℝ), (8270579/19531250 : ℝ)] ![(6663466034539/20000000000000 : ℝ), (34611091818791/100000000000000 : ℝ), (16035788993119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179122183/5000000000 : ℝ)|^8381 ≤ (6663466034539/20000000000000 : ℝ)^6333
        have hw : |(2179122183/5000000000 : ℝ)|=(2179122183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121382291/2500000000 : ℝ)|^8381 ≤ (34611091818791/100000000000000 : ℝ)^6333
        have hw : |(1121382291/2500000000 : ℝ)|=(1121382291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8270579/19531250 : ℝ)|^8381 ≤ (16035788993119/50000000000000 : ℝ)^6333
        have hw : |(8270579/19531250 : ℝ)|=(8270579/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2853/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11413/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2853/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2853/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2853/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2853/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2853/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2853/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2853/25000 : ℝ) ^ (2095/512 : ℝ) ≤ (1737104000810973/12500000000000000000 : ℝ) := by
    have hpowers : (2853/25000 : ℝ)^2095 ≤ (1737104000810973/12500000000000000000 : ℝ)^512 := by
      have hnat : (2853 : ℕ)^2095*12500000000000000000^512 ≤ 1737104000810973^512*25000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2853 25000 1737104000810973 12500000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2853/25000 : ℝ)) (X := (1737104000810973/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/25000 : ℝ) ^ (2095/512 : ℝ) ≤ (16395327412330639/50000000000000000000 : ℝ) := by
    have hpowers : (3519/25000 : ℝ)^2095 ≤ (16395327412330639/50000000000000000000 : ℝ)^512 := by
      have hnat : (3519 : ℕ)^2095*50000000000000000000^512 ≤ 16395327412330639^512*25000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 25000 16395327412330639 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/25000 : ℝ)) (X := (16395327412330639/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251737104000810973/6250000000000000000 : ℝ) ≤ (10000679181954643/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (6251737104000810973/6250000000000000000 : ℝ)^512 ≤ (10000679181954643/10000000000000000 : ℝ)^2095 := by
      have hnat : (6251737104000810973 : ℕ)^512*10000000000000000^2095 ≤ 10000679181954643^2095*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251737104000810973 6250000000000000000 10000679181954643 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000679181954643/10000000000000000 : ℝ)) (X := (6251737104000810973/6250000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023343743415574531/50000000000000000000 : ℝ) ≤ (10001140800861461/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (50023343743415574531/50000000000000000000 : ℝ)^512 ≤ (10001140800861461/10000000000000000 : ℝ)^2095 := by
      have hnat : (50023343743415574531 : ℕ)^512*10000000000000000^2095 ≤ 10001140800861461^2095*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023343743415574531 50000000000000000000 10001140800861461 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001140800861461/10000000000000000 : ℝ)) (X := (50023343743415574531/50000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016395327412330639/25000000000000000000 : ℝ) ≤ (10001602419768279/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25016395327412330639/25000000000000000000 : ℝ)^512 ≤ (10001602419768279/10000000000000000 : ℝ)^2095 := by
      have hnat : (25016395327412330639 : ℕ)^512*10000000000000000^2095 ≤ 10001602419768279^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016395327412330639 25000000000000000000 10001602419768279 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001602419768279/10000000000000000 : ℝ)) (X := (25016395327412330639/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1737104000810973/12500000000000000000 : ℝ) ≤ ((73975759307772097/74000000000000000 : ℝ)+2*(230809453409/133200000000000 : ℝ)*(2853/25000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (73975759307772097/74000000000000000 : ℝ)+2*(230809453409/133200000000000 : ℝ)*(2853/25000 : ℝ)=(10000679181954643/10000000000000000 : ℝ) by norm_num, show 1+2*(1737104000810973/12500000000000000000 : ℝ)=(6251737104000810973/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16395327412330639/50000000000000000000 : ℝ)+(1737104000810973/12500000000000000000 : ℝ) ≤ ((73975759307772097/74000000000000000 : ℝ)+(230809453409/133200000000000 : ℝ)*((3519/25000 : ℝ)+(2853/25000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (73975759307772097/74000000000000000 : ℝ)+(230809453409/133200000000000 : ℝ)*((3519/25000 : ℝ)+(2853/25000 : ℝ))=(10001140800861461/10000000000000000 : ℝ) by norm_num, show 1+(16395327412330639/50000000000000000000 : ℝ)+(1737104000810973/12500000000000000000 : ℝ)=(50023343743415574531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16395327412330639/50000000000000000000 : ℝ) ≤ ((73975759307772097/74000000000000000 : ℝ)+2*(230809453409/133200000000000 : ℝ)*(3519/25000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (73975759307772097/74000000000000000 : ℝ)+2*(230809453409/133200000000000 : ℝ)*(3519/25000 : ℝ)=(10001602419768279/10000000000000000 : ℝ) by norm_num, show 1+2*(16395327412330639/50000000000000000000 : ℝ)=(25016395327412330639/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73975759307772097/74000000000000000 : ℝ)*(X 1 0+X 2 0)+(230809453409/133200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (2853/25000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (73975759307772097/74000000000000000 : ℝ)) (alpha := (230809453409/133200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73975759307772097/74000000000000000 : ℝ)*(X 0 1+X 2 1)+(230809453409/133200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (2853/25000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (73975759307772097/74000000000000000 : ℝ)) (alpha := (230809453409/133200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73975759307772097/74000000000000000 : ℝ)*(X 0 2+X 1 2)+(230809453409/133200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (2853/25000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (73975759307772097/74000000000000000 : ℝ)) (alpha := (230809453409/133200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429016183/2000000000 : ℝ)*X 0 0+(1078431327/2000000000 : ℝ)*X 0 1+(5266492131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344562037/10000000000 : ℝ)*X 1 0+(-88352331/400000000 : ℝ)*X 1 1+(1053298427/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336140511/2500000000 : ℝ)*X 2 0+(5266492133/10000000000 : ℝ)*X 2 1+(-2208808269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179117397/5000000000 : ℝ)*X 0 0+(4233899673/10000000000 : ℝ)*X 0 1+(2243081823/5000000000 : ℝ)*X 0 2+(2179117397/5000000000 : ℝ)*X 1 0+(4233899673/10000000000 : ℝ)*X 1 1+(2243081823/5000000000 : ℝ)*X 1 2+(2179117397/5000000000 : ℝ)*X 2 0+(4233899673/10000000000 : ℝ)*X 2 1+(2243081823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072542809/5000000000 : ℝ)*X 0 0+(5266808203/10000000000 : ℝ)*X 0 1+(5391839469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312617777/10000000000 : ℝ)*X 1 0+(-2083461001/10000000000 : ℝ)*X 1 1+(1078367891/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312617771/10000000000 : ℝ)*X 2 0+(5391839477/10000000000 : ℝ)*X 2 1+(-104173049/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179122183/5000000000 : ℝ)*X 0 0+(1121382291/2500000000 : ℝ)*X 0 1+(8270579/19531250 : ℝ)*X 0 2+(2179122183/5000000000 : ℝ)*X 1 0+(1121382291/2500000000 : ℝ)*X 1 1+(8270579/19531250 : ℝ)*X 1 2+(2179122183/5000000000 : ℝ)*X 2 0+(1121382291/2500000000 : ℝ)*X 2 1+(8270579/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (256815451609142154152877/74000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (674695923/100000000000000 : ℝ)*(base19) + (630312921/100000000000000 : ℝ)*(base23) + (7322797/25000000000000 : ℝ)*(lower2) + (5243497/6250000000000 : ℝ)*(upper3) + (55631113/100000000000000 : ℝ)*(upper5) + (119218557650753/2000000000000 : ℝ)*(major0) + (119218557650753/2000000000000 : ℝ)*(major1) + (119218557650753/2000000000000 : ℝ)*(major2) + (1989429006097183/25000000000000 : ℝ)*(sp0) + (7957734389186673/100000000000000 : ℝ)*(sp1) + (318309377342787/4000000000000 : ℝ)*(sp2) + (1982055284661531/50000000000000 : ℝ)*(sp3) + (2379936733/12500000000000 : ℝ)*(sp4) + (10016186993/100000000000000 : ℝ)*(sp7) + (1982060292755027/50000000000000 : ℝ)*(f.failure) + (1989433765970649/25000000000000 : ℝ)*(f.sum) + (722225719159/666000000000000000000000000 : ℝ)*base66 + (1417361017443631/1332000000000000000000000000000 : ℝ)*base68 + (20241378250868369/1332000000000000000000000000000 : ℝ)*base69 + (29153540776407631/1332000000000000000000000000000 : ℝ)*base72 + (802814001887/666000000000000000000000000 : ℝ)*base73 + (12862456895864369/1332000000000000000000000000000 : ℝ)*base75 + (12654898535324369/1332000000000000000000000000000 : ℝ)*base77 + (1861405516640369/1332000000000000000000000000000 : ℝ)*base79 + (2339493104221/666000000000000000000000000 : ℝ)*base82 + (16723919/1250000000000000000000 : ℝ)*base90 + (16723919/1250000000000000000000 : ℝ)*base92 + (16723919/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37680019855769622700261689/3700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1489937659/100000000000000 : ℝ)*(base19) + (441539881/25000000000000 : ℝ)*(base23) + (514291617/100000000000000 : ℝ)*(lower1) + (40274613/25000000000000 : ℝ)*(upper3) + (6475559/5000000000000 : ℝ)*(lower4) + (98897327/50000000000000 : ℝ)*(upper5) + (5991056937818221/100000000000000 : ℝ)*(major0) + (5991056937818221/100000000000000 : ℝ)*(major1) + (5991056937818221/100000000000000 : ℝ)*(major2) + (6897544829/100000000000000 : ℝ)*(sp2) + (7997956605551799/100000000000000 : ℝ)*(sp4) + (399897755780707/5000000000000 : ℝ)*(sp5) + (7997947941847447/100000000000000 : ℝ)*(sp6) + (249009808164061/6250000000000 : ℝ)*(sp7) + (249009808164061/6250000000000 : ℝ)*(f.failure) + (7997956605551799/100000000000000 : ℝ)*(f.sum) + (8646232405051/6660000000000000000000000000 : ℝ)*base66 + (174041086417840067/66600000000000000000000000000000 : ℝ)*base68 + (995809710563359933/66600000000000000000000000000000 : ℝ)*base69 + (3796657825768840067/66600000000000000000000000000000 : ℝ)*base72 + (16537308911549/6660000000000000000000000000 : ℝ)*base73 + (10836909495227959933/66600000000000000000000000000000 : ℝ)*base75 + (137505117653359933/66600000000000000000000000000000 : ℝ)*base77 + (247204694200759933/66600000000000000000000000000000 : ℝ)*base79 + (60185693040031/6660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (647317/156250000000000000000 : ℝ)*base90 + (647317/156250000000000000000 : ℝ)*base92 + (647317/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1188_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2853/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1188_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1188_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1188_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1188_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
