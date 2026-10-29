-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:04.461283+00:00
-- url     : https://prove2.me/submissions/9d882e73-2e99-4aff-b246-25c22bf4c17c

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
theorem support_rectangle_w1352_box_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-467226817/2500000000 : ℝ)*x 0 + (1077903859/2000000000 : ℝ)*x 1 + (5389519981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467226817/2500000000 : ℝ)^539 ≤ (2216992885457/20000000000000 : ℝ)^411 := by
    have hnat : (467226817 : ℕ)^539*20000000000000^411 ≤ 2216992885457^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467226817 2500000000 2216992885457 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077903859/2000000000 : ℝ)^539 ≤ (8891502813451/20000000000000 : ℝ)^411 := by
    have hnat : (1077903859 : ℕ)^539*20000000000000^411 ≤ 8891502813451^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077903859 2000000000 8891502813451 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389519981/10000000000 : ℝ)^539 ≤ (138929754651/312500000000 : ℝ)^411 := by
    have hnat : (5389519981 : ℕ)^539*312500000000^411 ≤ 138929754651^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389519981 10000000000 138929754651 312500000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467226817/2500000000 : ℝ), (1077903859/2000000000 : ℝ), (5389519981/10000000000 : ℝ)] ![(2216992885457/20000000000000 : ℝ), (8891502813451/20000000000000 : ℝ), (138929754651/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467226817/2500000000 : ℝ)|^539 ≤ (2216992885457/20000000000000 : ℝ)^411
        have hw : |(-467226817/2500000000 : ℝ)|=(467226817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077903859/2000000000 : ℝ)|^539 ≤ (8891502813451/20000000000000 : ℝ)^411
        have hw : |(1077903859/2000000000 : ℝ)|=(1077903859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389519981/10000000000 : ℝ)|^539 ≤ (138929754651/312500000000 : ℝ)^411
        have hw : |(5389519981/10000000000 : ℝ)|=(5389519981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1321324677/2500000000 : ℝ)*x 0 + (-125733963/625000000 : ℝ)*x 1 + (53895193/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321324677/2500000000 : ℝ)^539 ≤ (43333478625293/100000000000000 : ℝ)^411 := by
    have hnat : (1321324677 : ℕ)^539*100000000000000^411 ≤ 43333478625293^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321324677 2500000000 43333478625293 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125733963/625000000 : ℝ)^539 ≤ (1220900723849/10000000000000 : ℝ)^411 := by
    have hnat : (125733963 : ℕ)^539*10000000000000^411 ≤ 1220900723849^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125733963 625000000 1220900723849 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53895193/100000000 : ℝ)^539 ≤ (8891502824269/20000000000000 : ℝ)^411 := by
    have hnat : (53895193 : ℕ)^539*20000000000000^411 ≤ 8891502824269^411*100000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53895193 100000000 8891502824269 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321324677/2500000000 : ℝ), (-125733963/625000000 : ℝ), (53895193/100000000 : ℝ)] ![(43333478625293/100000000000000 : ℝ), (1220900723849/10000000000000 : ℝ), (8891502824269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321324677/2500000000 : ℝ)|^539 ≤ (43333478625293/100000000000000 : ℝ)^411
        have hw : |(1321324677/2500000000 : ℝ)|=(1321324677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125733963/625000000 : ℝ)|^539 ≤ (1220900723849/10000000000000 : ℝ)^411
        have hw : |(-125733963/625000000 : ℝ)|=(125733963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53895193/100000000 : ℝ)|^539 ≤ (8891502824269/20000000000000 : ℝ)^411
        have hw : |(53895193/100000000 : ℝ)|=(53895193/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5285298557/10000000000 : ℝ)*x 0 + (5389519483/10000000000 : ℝ)*x 1 + (-502935841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285298557/10000000000 : ℝ)^539 ≤ (21666738500849/50000000000000 : ℝ)^411 := by
    have hnat : (5285298557 : ℕ)^539*50000000000000^411 ≤ 21666738500849^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285298557 10000000000 21666738500849 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389519483/10000000000 : ℝ)^539 ≤ (44457516101017/100000000000000 : ℝ)^411 := by
    have hnat : (5389519483 : ℕ)^539*100000000000000^411 ≤ 44457516101017^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389519483 10000000000 44457516101017 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502935841/2500000000 : ℝ)^539 ≤ (12209006888297/100000000000000 : ℝ)^411 := by
    have hnat : (502935841 : ℕ)^539*100000000000000^411 ≤ 12209006888297^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502935841 2500000000 12209006888297 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285298557/10000000000 : ℝ), (5389519483/10000000000 : ℝ), (-502935841/2500000000 : ℝ)] ![(21666738500849/50000000000000 : ℝ), (44457516101017/100000000000000 : ℝ), (12209006888297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285298557/10000000000 : ℝ)|^539 ≤ (21666738500849/50000000000000 : ℝ)^411
        have hw : |(5285298557/10000000000 : ℝ)|=(5285298557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389519483/10000000000 : ℝ)|^539 ≤ (44457516101017/100000000000000 : ℝ)^411
        have hw : |(5389519483/10000000000 : ℝ)|=(5389519483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-502935841/2500000000 : ℝ)|^539 ≤ (12209006888297/100000000000000 : ℝ)^411
        have hw : |(-502935841/2500000000 : ℝ)|=(502935841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4471967111/10000000000 : ℝ)*x 0 + (4253904427/10000000000 : ℝ)*x 1 + (4253904657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4471967111/10000000000 : ℝ)^539 ≤ (34805786334441/100000000000000 : ℝ)^411 := by
    have hnat : (4471967111 : ℕ)^539*100000000000000^411 ≤ 34805786334441^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471967111 10000000000 34805786334441 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253904427/10000000000 : ℝ)^539 ≤ (8149276417131/25000000000000 : ℝ)^411 := by
    have hnat : (4253904427 : ℕ)^539*25000000000000^411 ≤ 8149276417131^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253904427 10000000000 8149276417131 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253904657/10000000000 : ℝ)^539 ≤ (8149276994969/25000000000000 : ℝ)^411 := by
    have hnat : (4253904657 : ℕ)^539*25000000000000^411 ≤ 8149276994969^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253904657 10000000000 8149276994969 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4471967111/10000000000 : ℝ), (4253904427/10000000000 : ℝ), (4253904657/10000000000 : ℝ)] ![(34805786334441/100000000000000 : ℝ), (8149276417131/25000000000000 : ℝ), (8149276994969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4471967111/10000000000 : ℝ)|^539 ≤ (34805786334441/100000000000000 : ℝ)^411
        have hw : |(4471967111/10000000000 : ℝ)|=(4471967111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253904427/10000000000 : ℝ)|^539 ≤ (8149276417131/25000000000000 : ℝ)^411
        have hw : |(4253904427/10000000000 : ℝ)|=(4253904427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253904657/10000000000 : ℝ)|^539 ≤ (8149276994969/25000000000000 : ℝ)^411
        have hw : |(4253904657/10000000000 : ℝ)|=(4253904657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-137786107/625000000 : ℝ)*x 0 + (5265144711/10000000000 : ℝ)*x 1 + (329071561/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137786107/625000000 : ℝ)^539 ≤ (13766185542753/100000000000000 : ℝ)^411 := by
    have hnat : (137786107 : ℕ)^539*100000000000000^411 ≤ 13766185542753^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137786107 625000000 13766185542753 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265144711/10000000000 : ℝ)^539 ≤ (43116905796743/100000000000000 : ℝ)^411 := by
    have hnat : (5265144711 : ℕ)^539*100000000000000^411 ≤ 43116905796743^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265144711 10000000000 43116905796743 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329071561/625000000 : ℝ)^539 ≤ (5389613580339/12500000000000 : ℝ)^411 := by
    have hnat : (329071561 : ℕ)^539*12500000000000^411 ≤ 5389613580339^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329071561 625000000 5389613580339 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137786107/625000000 : ℝ), (5265144711/10000000000 : ℝ), (329071561/625000000 : ℝ)] ![(13766185542753/100000000000000 : ℝ), (43116905796743/100000000000000 : ℝ), (5389613580339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137786107/625000000 : ℝ)|^539 ≤ (13766185542753/100000000000000 : ℝ)^411
        have hw : |(-137786107/625000000 : ℝ)|=(137786107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265144711/10000000000 : ℝ)|^539 ≤ (43116905796743/100000000000000 : ℝ)^411
        have hw : |(5265144711/10000000000 : ℝ)|=(5265144711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329071561/625000000 : ℝ)|^539 ≤ (5389613580339/12500000000000 : ℝ)^411
        have hw : |(329071561/625000000 : ℝ)|=(329071561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5372619539/10000000000 : ℝ)*x 0 + (-2061720847/10000000000 : ℝ)*x 1 + (658143159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372619539/10000000000 : ℝ)^539 ≤ (1770991355873/4000000000000 : ℝ)^411 := by
    have hnat : (5372619539 : ℕ)^539*4000000000000^411 ≤ 1770991355873^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372619539 10000000000 1770991355873 4000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061720847/10000000000 : ℝ)^539 ≤ (12608304265359/100000000000000 : ℝ)^411 := by
    have hnat : (2061720847 : ℕ)^539*100000000000000^411 ≤ 12608304265359^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061720847 10000000000 12608304265359 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658143159/1250000000 : ℝ)^539 ≤ (8623382364321/20000000000000 : ℝ)^411 := by
    have hnat : (658143159 : ℕ)^539*20000000000000^411 ≤ 8623382364321^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658143159 1250000000 8623382364321 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372619539/10000000000 : ℝ), (-2061720847/10000000000 : ℝ), (658143159/1250000000 : ℝ)] ![(1770991355873/4000000000000 : ℝ), (12608304265359/100000000000000 : ℝ), (8623382364321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372619539/10000000000 : ℝ)|^539 ≤ (1770991355873/4000000000000 : ℝ)^411
        have hw : |(5372619539/10000000000 : ℝ)|=(5372619539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061720847/10000000000 : ℝ)|^539 ≤ (12608304265359/100000000000000 : ℝ)^411
        have hw : |(-2061720847/10000000000 : ℝ)|=(2061720847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658143159/1250000000 : ℝ)|^539 ≤ (8623382364321/20000000000000 : ℝ)^411
        have hw : |(658143159/1250000000 : ℝ)|=(658143159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5372619959/10000000000 : ℝ)*x 0 + (658143127/1250000000 : ℝ)*x 1 + (-3298753/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372619959/10000000000 : ℝ)^539 ≤ (11068697108973/25000000000000 : ℝ)^411 := by
    have hnat : (5372619959 : ℕ)^539*25000000000000^411 ≤ 11068697108973^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372619959 10000000000 11068697108973 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658143127/1250000000 : ℝ)^539 ≤ (10779227268073/25000000000000 : ℝ)^411 := by
    have hnat : (658143127 : ℕ)^539*25000000000000^411 ≤ 10779227268073^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658143127 1250000000 10779227268073 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3298753/16000000 : ℝ)^539 ≤ (12608302484921/100000000000000 : ℝ)^411 := by
    have hnat : (3298753 : ℕ)^539*100000000000000^411 ≤ 12608302484921^411*16000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3298753 16000000 12608302484921 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372619959/10000000000 : ℝ), (658143127/1250000000 : ℝ), (-3298753/16000000 : ℝ)] ![(11068697108973/25000000000000 : ℝ), (10779227268073/25000000000000 : ℝ), (12608302484921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372619959/10000000000 : ℝ)|^539 ≤ (11068697108973/25000000000000 : ℝ)^411
        have hw : |(5372619959/10000000000 : ℝ)|=(5372619959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658143127/1250000000 : ℝ)|^539 ≤ (10779227268073/25000000000000 : ℝ)^411
        have hw : |(658143127/1250000000 : ℝ)|=(658143127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3298753/16000000 : ℝ)|^539 ≤ (12608302484921/100000000000000 : ℝ)^411
        have hw : |(-3298753/16000000 : ℝ)|=(3298753/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2087560351/5000000000 : ℝ)*x 0 + (440227481/1000000000 : ℝ)*x 1 + (550284271/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087560351/5000000000 : ℝ)^539 ≤ (993989781291/3125000000000 : ℝ)^411 := by
    have hnat : (2087560351 : ℕ)^539*3125000000000^411 ≤ 993989781291^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087560351 5000000000 993989781291 3125000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440227481/1000000000 : ℝ)^539 ≤ (34096166757129/100000000000000 : ℝ)^411 := by
    have hnat : (440227481 : ℕ)^539*100000000000000^411 ≤ 34096166757129^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440227481 1000000000 34096166757129 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550284271/1250000000 : ℝ)^539 ≤ (17048080118093/50000000000000 : ℝ)^411 := by
    have hnat : (550284271 : ℕ)^539*50000000000000^411 ≤ 17048080118093^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550284271 1250000000 17048080118093 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087560351/5000000000 : ℝ), (440227481/1000000000 : ℝ), (550284271/1250000000 : ℝ)] ![(993989781291/3125000000000 : ℝ), (34096166757129/100000000000000 : ℝ), (17048080118093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087560351/5000000000 : ℝ)|^539 ≤ (993989781291/3125000000000 : ℝ)^411
        have hw : |(2087560351/5000000000 : ℝ)|=(2087560351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440227481/1000000000 : ℝ)|^539 ≤ (34096166757129/100000000000000 : ℝ)^411
        have hw : |(440227481/1000000000 : ℝ)|=(440227481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550284271/1250000000 : ℝ)|^539 ≤ (17048080118093/50000000000000 : ℝ)^411
        have hw : |(550284271/1250000000 : ℝ)|=(550284271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_8 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-426812267/2000000000 : ℝ)*x 0 + (207178977/400000000 : ℝ)*x 1 + (5403534641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426812267/2000000000 : ℝ)^539 ≤ (13191618907111/100000000000000 : ℝ)^411 := by
    have hnat : (426812267 : ℕ)^539*100000000000000^411 ≤ 13191618907111^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426812267 2000000000 13191618907111 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207178977/400000000 : ℝ)^539 ≤ (10549797339663/25000000000000 : ℝ)^411 := by
    have hnat : (207178977 : ℕ)^539*25000000000000^411 ≤ 10549797339663^411*400000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207178977 400000000 10549797339663 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403534641/10000000000 : ℝ)^539 ≤ (22304595866053/50000000000000 : ℝ)^411 := by
    have hnat : (5403534641 : ℕ)^539*50000000000000^411 ≤ 22304595866053^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403534641 10000000000 22304595866053 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426812267/2000000000 : ℝ), (207178977/400000000 : ℝ), (5403534641/10000000000 : ℝ)] ![(13191618907111/100000000000000 : ℝ), (10549797339663/25000000000000 : ℝ), (22304595866053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426812267/2000000000 : ℝ)|^539 ≤ (13191618907111/100000000000000 : ℝ)^411
        have hw : |(-426812267/2000000000 : ℝ)|=(426812267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207178977/400000000 : ℝ)|^539 ≤ (10549797339663/25000000000000 : ℝ)^411
        have hw : |(207178977/400000000 : ℝ)|=(207178977/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403534641/10000000000 : ℝ)|^539 ≤ (22304595866053/50000000000000 : ℝ)^411
        have hw : |(5403534641/10000000000 : ℝ)|=(5403534641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_9 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5275453389/10000000000 : ℝ)*x 0 + (-2005980037/10000000000 : ℝ)*x 1 + (5403534751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275453389/10000000000 : ℝ)^539 ≤ (21613824811061/50000000000000 : ℝ)^411 := by
    have hnat : (5275453389 : ℕ)^539*50000000000000^411 ≤ 21613824811061^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275453389 10000000000 21613824811061 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005980037/10000000000 : ℝ)^539 ≤ (6081578723209/50000000000000 : ℝ)^411 := by
    have hnat : (2005980037 : ℕ)^539*50000000000000^411 ≤ 6081578723209^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005980037 10000000000 6081578723209 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403534751/10000000000 : ℝ)^539 ≤ (11152298230759/25000000000000 : ℝ)^411 := by
    have hnat : (5403534751 : ℕ)^539*25000000000000^411 ≤ 11152298230759^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403534751 10000000000 11152298230759 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275453389/10000000000 : ℝ), (-2005980037/10000000000 : ℝ), (5403534751/10000000000 : ℝ)] ![(21613824811061/50000000000000 : ℝ), (6081578723209/50000000000000 : ℝ), (11152298230759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275453389/10000000000 : ℝ)|^539 ≤ (21613824811061/50000000000000 : ℝ)^411
        have hw : |(5275453389/10000000000 : ℝ)|=(5275453389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005980037/10000000000 : ℝ)|^539 ≤ (6081578723209/50000000000000 : ℝ)^411
        have hw : |(-2005980037/10000000000 : ℝ)|=(2005980037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403534751/10000000000 : ℝ)|^539 ≤ (11152298230759/25000000000000 : ℝ)^411
        have hw : |(5403534751/10000000000 : ℝ)|=(5403534751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_10 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5275453393/10000000000 : ℝ)*x 0 + (5403534719/10000000000 : ℝ)*x 1 + (-501495019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275453393/10000000000 : ℝ)^539 ≤ (21613824832553/50000000000000 : ℝ)^411 := by
    have hnat : (5275453393 : ℕ)^539*50000000000000^411 ≤ 21613824832553^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275453393 10000000000 21613824832553 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403534719/10000000000 : ℝ)^539 ≤ (44609192576583/100000000000000 : ℝ)^411 := by
    have hnat : (5403534719 : ℕ)^539*100000000000000^411 ≤ 44609192576583^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403534719 10000000000 44609192576583 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501495019/2500000000 : ℝ)^539 ≤ (12163157756539/100000000000000 : ℝ)^411 := by
    have hnat : (501495019 : ℕ)^539*100000000000000^411 ≤ 12163157756539^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501495019 2500000000 12163157756539 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275453393/10000000000 : ℝ), (5403534719/10000000000 : ℝ), (-501495019/2500000000 : ℝ)] ![(21613824832553/50000000000000 : ℝ), (44609192576583/100000000000000 : ℝ), (12163157756539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275453393/10000000000 : ℝ)|^539 ≤ (21613824832553/50000000000000 : ℝ)^411
        have hw : |(5275453393/10000000000 : ℝ)|=(5275453393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403534719/10000000000 : ℝ)|^539 ≤ (44609192576583/100000000000000 : ℝ)^411
        have hw : |(5403534719/10000000000 : ℝ)|=(5403534719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-501495019/2500000000 : ℝ)|^539 ≤ (12163157756539/100000000000000 : ℝ)^411
        have hw : |(-501495019/2500000000 : ℝ)|=(501495019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_11 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4504857363/10000000000 : ℝ)*x 0 + (4237172023/10000000000 : ℝ)*x 1 + (2118586011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4504857363/10000000000 : ℝ)^539 ≤ (35141882266269/100000000000000 : ℝ)^411 := by
    have hnat : (4504857363 : ℕ)^539*100000000000000^411 ≤ 35141882266269^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504857363 10000000000 35141882266269 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237172023/10000000000 : ℝ)^539 ≤ (32429058860339/100000000000000 : ℝ)^411 := by
    have hnat : (4237172023 : ℕ)^539*100000000000000^411 ≤ 32429058860339^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237172023 10000000000 32429058860339 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118586011/5000000000 : ℝ)^539 ≤ (16214529425151/50000000000000 : ℝ)^411 := by
    have hnat : (2118586011 : ℕ)^539*50000000000000^411 ≤ 16214529425151^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118586011 5000000000 16214529425151 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4504857363/10000000000 : ℝ), (4237172023/10000000000 : ℝ), (2118586011/5000000000 : ℝ)] ![(35141882266269/100000000000000 : ℝ), (32429058860339/100000000000000 : ℝ), (16214529425151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4504857363/10000000000 : ℝ)|^539 ≤ (35141882266269/100000000000000 : ℝ)^411
        have hw : |(4504857363/10000000000 : ℝ)|=(4504857363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237172023/10000000000 : ℝ)|^539 ≤ (32429058860339/100000000000000 : ℝ)^411
        have hw : |(4237172023/10000000000 : ℝ)|=(4237172023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118586011/5000000000 : ℝ)|^539 ≤ (16214529425151/50000000000000 : ℝ)^411
        have hw : |(2118586011/5000000000 : ℝ)|=(2118586011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_12 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1939741749/10000000000 : ℝ)*x 0 + (2736503523/5000000000 : ℝ)*x 1 + (1050813541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939741749/10000000000 : ℝ)^539 ≤ (5819585733581/50000000000000 : ℝ)^411 := by
    have hnat : (1939741749 : ℕ)^539*50000000000000^411 ≤ 5819585733581^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939741749 10000000000 5819585733581 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736503523/5000000000 : ℝ)^539 ≤ (4536284528311/10000000000000 : ℝ)^411 := by
    have hnat : (2736503523 : ℕ)^539*10000000000000^411 ≤ 4536284528311^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736503523 5000000000 4536284528311 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050813541/2000000000 : ℝ)^539 ≤ (21498991619669/50000000000000 : ℝ)^411 := by
    have hnat : (1050813541 : ℕ)^539*50000000000000^411 ≤ 21498991619669^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050813541 2000000000 21498991619669 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1939741749/10000000000 : ℝ), (2736503523/5000000000 : ℝ), (1050813541/2000000000 : ℝ)] ![(5819585733581/50000000000000 : ℝ), (4536284528311/10000000000000 : ℝ), (21498991619669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1939741749/10000000000 : ℝ)|^539 ≤ (5819585733581/50000000000000 : ℝ)^411
        have hw : |(-1939741749/10000000000 : ℝ)|=(1939741749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736503523/5000000000 : ℝ)|^539 ≤ (4536284528311/10000000000000 : ℝ)^411
        have hw : |(2736503523/5000000000 : ℝ)|=(2736503523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050813541/2000000000 : ℝ)|^539 ≤ (21498991619669/50000000000000 : ℝ)^411
        have hw : |(1050813541/2000000000 : ℝ)|=(1050813541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_13 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (672549371/1250000000 : ℝ)*x 0 + (-1033034273/5000000000 : ℝ)*x 1 + (2627033773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672549371/1250000000 : ℝ)^539 ≤ (11089708560207/25000000000000 : ℝ)^411 := by
    have hnat : (672549371 : ℕ)^539*25000000000000^411 ≤ 11089708560207^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672549371 1250000000 11089708560207 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033034273/5000000000 : ℝ)^539 ≤ (2528636841397/20000000000000 : ℝ)^411 := by
    have hnat : (1033034273 : ℕ)^539*20000000000000^411 ≤ 2528636841397^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033034273 5000000000 2528636841397 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627033773/5000000000 : ℝ)^539 ≤ (10749495383219/25000000000000 : ℝ)^411 := by
    have hnat : (2627033773 : ℕ)^539*25000000000000^411 ≤ 10749495383219^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627033773 5000000000 10749495383219 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672549371/1250000000 : ℝ), (-1033034273/5000000000 : ℝ), (2627033773/5000000000 : ℝ)] ![(11089708560207/25000000000000 : ℝ), (2528636841397/20000000000000 : ℝ), (10749495383219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672549371/1250000000 : ℝ)|^539 ≤ (11089708560207/25000000000000 : ℝ)^411
        have hw : |(672549371/1250000000 : ℝ)|=(672549371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033034273/5000000000 : ℝ)|^539 ≤ (2528636841397/20000000000000 : ℝ)^411
        have hw : |(-1033034273/5000000000 : ℝ)|=(1033034273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627033773/5000000000 : ℝ)|^539 ≤ (10749495383219/25000000000000 : ℝ)^411
        have hw : |(2627033773/5000000000 : ℝ)|=(2627033773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_14 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2690197287/5000000000 : ℝ)*x 0 + (1050813631/2000000000 : ℝ)*x 1 + (-1033034131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690197287/5000000000 : ℝ)^539 ≤ (1386213436901/3125000000000 : ℝ)^411 := by
    have hnat : (2690197287 : ℕ)^539*3125000000000^411 ≤ 1386213436901^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690197287 5000000000 1386213436901 3125000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050813631/2000000000 : ℝ)^539 ≤ (21498994034473/50000000000000 : ℝ)^411 := by
    have hnat : (1050813631 : ℕ)^539*50000000000000^411 ≤ 21498994034473^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050813631 2000000000 21498994034473 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033034131/5000000000 : ℝ)^539 ≤ (6321590963907/50000000000000 : ℝ)^411 := by
    have hnat : (1033034131 : ℕ)^539*50000000000000^411 ≤ 6321590963907^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033034131 5000000000 6321590963907 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690197287/5000000000 : ℝ), (1050813631/2000000000 : ℝ), (-1033034131/5000000000 : ℝ)] ![(1386213436901/3125000000000 : ℝ), (21498994034473/50000000000000 : ℝ), (6321590963907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690197287/5000000000 : ℝ)|^539 ≤ (1386213436901/3125000000000 : ℝ)^411
        have hw : |(2690197287/5000000000 : ℝ)|=(2690197287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050813631/2000000000 : ℝ)|^539 ≤ (21498994034473/50000000000000 : ℝ)^411
        have hw : |(1050813631/2000000000 : ℝ)|=(1050813631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033034131/5000000000 : ℝ)|^539 ≤ (6321590963907/50000000000000 : ℝ)^411
        have hw : |(-1033034131/5000000000 : ℝ)|=(1033034131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_box_15 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1037058689/2500000000 : ℝ)*x 0 + (883095651/2000000000 : ℝ)*x 1 + (1103869457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037058689/2500000000 : ℝ)^539 ≤ (3153932474799/10000000000000 : ℝ)^411 := by
    have hnat : (1037058689 : ℕ)^539*10000000000000^411 ≤ 3153932474799^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037058689 2500000000 3153932474799 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883095651/2000000000 : ℝ)^539 ≤ (1711516989769/5000000000000 : ℝ)^411 := by
    have hnat : (883095651 : ℕ)^539*5000000000000^411 ≤ 1711516989769^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883095651 2000000000 1711516989769 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103869457/2500000000 : ℝ)^539 ≤ (8557583863549/25000000000000 : ℝ)^411 := by
    have hnat : (1103869457 : ℕ)^539*25000000000000^411 ≤ 8557583863549^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103869457 2500000000 8557583863549 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037058689/2500000000 : ℝ), (883095651/2000000000 : ℝ), (1103869457/2500000000 : ℝ)] ![(3153932474799/10000000000000 : ℝ), (1711516989769/5000000000000 : ℝ), (8557583863549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037058689/2500000000 : ℝ)|^539 ≤ (3153932474799/10000000000000 : ℝ)^411
        have hw : |(1037058689/2500000000 : ℝ)|=(1037058689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(883095651/2000000000 : ℝ)|^539 ≤ (1711516989769/5000000000000 : ℝ)^411
        have hw : |(883095651/2000000000 : ℝ)|=(883095651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103869457/2500000000 : ℝ)|^539 ≤ (8557583863549/25000000000000 : ℝ)^411
        have hw : |(1103869457/2500000000 : ℝ)|=(1103869457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62859/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58961/100000 : ℝ) ∧ (80013/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84391/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11173/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (9836306063966147/100000000000000000000 : ℝ) := by
    have hpowers : (11173/100000 : ℝ)^4311 ≤ (9836306063966147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11173 : ℕ)^4311*100000000000000000000^1024 ≤ 9836306063966147^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11173 100000 9836306063966147 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11173/100000 : ℝ)) (X := (9836306063966147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1839/12500 : ℝ) ^ (4311/1024 : ℝ) ≤ (31327838996319483/100000000000000000000 : ℝ) := by
    have hpowers : (1839/12500 : ℝ)^4311 ≤ (31327838996319483/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1839 : ℕ)^4311*100000000000000000000^1024 ≤ 31327838996319483^1024*12500^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 12500 31327838996319483 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/12500 : ℝ)) (X := (31327838996319483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009836306063966147/50000000000000000000 : ℝ) ≤ (10000467252242247/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50009836306063966147/50000000000000000000 : ℝ)^1024 ≤ (10000467252242247/10000000000000000 : ℝ)^4311 := by
      have hnat : (50009836306063966147 : ℕ)^1024*10000000000000000^4311 ≤ 10000467252242247^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009836306063966147 50000000000000000000 10000467252242247 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000467252242247/10000000000000000 : ℝ)) (X := (50009836306063966147/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004116414506028563/10000000000000000000 : ℝ) ≤ (1250122203291409/1250000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (10004116414506028563/10000000000000000000 : ℝ)^1024 ≤ (1250122203291409/1250000000000000 : ℝ)^4311 := by
      have hnat : (10004116414506028563 : ℕ)^1024*1250000000000000^4311 ≤ 1250122203291409^4311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004116414506028563 10000000000000000000 1250122203291409 1250000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250122203291409/1250000000000000 : ℝ)) (X := (10004116414506028563/10000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031327838996319483/50000000000000000000 : ℝ) ≤ (10001488000420297/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50031327838996319483/50000000000000000000 : ℝ)^1024 ≤ (10001488000420297/10000000000000000 : ℝ)^4311 := by
      have hnat : (50031327838996319483 : ℕ)^1024*10000000000000000^4311 ≤ 10001488000420297^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031327838996319483 50000000000000000000 10001488000420297 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001488000420297/10000000000000000 : ℝ)) (X := (50031327838996319483/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9836306063966147/100000000000000000000 : ℝ) ≤ ((35380248786291959483/35390000000000000000 : ℝ)+2*(20414963561/14156000000000 : ℝ)*(11173/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (35380248786291959483/35390000000000000000 : ℝ)+2*(20414963561/14156000000000 : ℝ)*(11173/100000 : ℝ)=(10000467252242247/10000000000000000 : ℝ) by norm_num, show 1+2*(9836306063966147/100000000000000000000 : ℝ)=(50009836306063966147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31327838996319483/100000000000000000000 : ℝ)+(9836306063966147/100000000000000000000 : ℝ) ≤ ((35380248786291959483/35390000000000000000 : ℝ)+(20414963561/14156000000000 : ℝ)*((1839/12500 : ℝ)+(11173/100000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (35380248786291959483/35390000000000000000 : ℝ)+(20414963561/14156000000000 : ℝ)*((1839/12500 : ℝ)+(11173/100000 : ℝ))=(1250122203291409/1250000000000000 : ℝ) by norm_num, show 1+(31327838996319483/100000000000000000000 : ℝ)+(9836306063966147/100000000000000000000 : ℝ)=(10004116414506028563/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31327838996319483/100000000000000000000 : ℝ) ≤ ((35380248786291959483/35390000000000000000 : ℝ)+2*(20414963561/14156000000000 : ℝ)*(1839/12500 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (35380248786291959483/35390000000000000000 : ℝ)+2*(20414963561/14156000000000 : ℝ)*(1839/12500 : ℝ)=(10001488000420297/10000000000000000 : ℝ) by norm_num, show 1+2*(31327838996319483/100000000000000000000 : ℝ)=(50031327838996319483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35380248786291959483/35390000000000000000 : ℝ)*(X 1 0+X 2 0)+(20414963561/14156000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (35380248786291959483/35390000000000000000 : ℝ)) (alpha := (20414963561/14156000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35380248786291959483/35390000000000000000 : ℝ)*(X 0 1+X 2 1)+(20414963561/14156000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (35380248786291959483/35390000000000000000 : ℝ)) (alpha := (20414963561/14156000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35380248786291959483/35390000000000000000 : ℝ)*(X 0 2+X 1 2)+(20414963561/14156000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (35380248786291959483/35390000000000000000 : ℝ)) (alpha := (20414963561/14156000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-467226817/2500000000 : ℝ)*X 0 0+(1077903859/2000000000 : ℝ)*X 0 1+(5389519981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321324677/2500000000 : ℝ)*X 1 0+(-125733963/625000000 : ℝ)*X 1 1+(53895193/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285298557/10000000000 : ℝ)*X 2 0+(5389519483/10000000000 : ℝ)*X 2 1+(-502935841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4471967111/10000000000 : ℝ)*X 0 0+(4253904427/10000000000 : ℝ)*X 0 1+(4253904657/10000000000 : ℝ)*X 0 2+(4471967111/10000000000 : ℝ)*X 1 0+(4253904427/10000000000 : ℝ)*X 1 1+(4253904657/10000000000 : ℝ)*X 1 2+(4471967111/10000000000 : ℝ)*X 2 0+(4253904427/10000000000 : ℝ)*X 2 1+(4253904657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-137786107/625000000 : ℝ)*X 0 0+(5265144711/10000000000 : ℝ)*X 0 1+(329071561/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5372619539/10000000000 : ℝ)*X 1 0+(-2061720847/10000000000 : ℝ)*X 1 1+(658143159/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5372619959/10000000000 : ℝ)*X 2 0+(658143127/1250000000 : ℝ)*X 2 1+(-3298753/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087560351/5000000000 : ℝ)*X 0 0+(440227481/1000000000 : ℝ)*X 0 1+(550284271/1250000000 : ℝ)*X 0 2+(2087560351/5000000000 : ℝ)*X 1 0+(440227481/1000000000 : ℝ)*X 1 1+(550284271/1250000000 : ℝ)*X 1 2+(2087560351/5000000000 : ℝ)*X 2 0+(440227481/1000000000 : ℝ)*X 2 1+(550284271/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-426812267/2000000000 : ℝ)*X 0 0+(207178977/400000000 : ℝ)*X 0 1+(5403534641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275453389/10000000000 : ℝ)*X 1 0+(-2005980037/10000000000 : ℝ)*X 1 1+(5403534751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275453393/10000000000 : ℝ)*X 2 0+(5403534719/10000000000 : ℝ)*X 2 1+(-501495019/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4504857363/10000000000 : ℝ)*X 0 0+(4237172023/10000000000 : ℝ)*X 0 1+(2118586011/5000000000 : ℝ)*X 0 2+(4504857363/10000000000 : ℝ)*X 1 0+(4237172023/10000000000 : ℝ)*X 1 1+(2118586011/5000000000 : ℝ)*X 1 2+(4504857363/10000000000 : ℝ)*X 2 0+(4237172023/10000000000 : ℝ)*X 2 1+(2118586011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1939741749/10000000000 : ℝ)*X 0 0+(2736503523/5000000000 : ℝ)*X 0 1+(1050813541/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672549371/1250000000 : ℝ)*X 1 0+(-1033034273/5000000000 : ℝ)*X 1 1+(2627033773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690197287/5000000000 : ℝ)*X 2 0+(1050813631/2000000000 : ℝ)*X 2 1+(-1033034131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1037058689/2500000000 : ℝ)*X 0 0+(883095651/2000000000 : ℝ)*X 0 1+(1103869457/2500000000 : ℝ)*X 0 2+(1037058689/2500000000 : ℝ)*X 1 0+(883095651/2000000000 : ℝ)*X 1 1+(1103869457/2500000000 : ℝ)*X 1 2+(1037058689/2500000000 : ℝ)*X 2 0+(883095651/2000000000 : ℝ)*X 2 1+(1103869457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62859/100000 : ℝ) ≤ (-444900651708480399319090917/707800000000000000000000000 : ℝ) := by norm_num
    linear_combination (6893029/20000000000000 : ℝ)*(upper1) + (146203161/100000000000000 : ℝ)*(lower2) + (24796431/100000000000000 : ℝ)*(upper4) + (586378827991151/20000000000000 : ℝ)*(major0) + (586378827991151/20000000000000 : ℝ)*(major1) + (586378827991151/20000000000000 : ℝ)*(major2) + (877706757/20000000000000 : ℝ)*(sp3) + (399469166323913/10000000000000 : ℝ)*(sp4) + (998643792031003/25000000000000 : ℝ)*(sp5) + (1997285505446887/50000000000000 : ℝ)*(sp6) + (945021461204777/50000000000000 : ℝ)*(sp7) + (791409031/50000000000000 : ℝ)*(sp8) + (5903896659/5000000000000 : ℝ)*(sp13) + (122235163419/100000000000000 : ℝ)*(sp14) + (945023655471669/50000000000000 : ℝ)*(f.failure) + (499336655757149/12500000000000 : ℝ)*(f.sum) + (6806555299383/884750000000000000000000000 : ℝ)*base66 + (898487037275034933/707800000000000000000000000000000 : ℝ)*base67 + (1095165034227834933/707800000000000000000000000000000 : ℝ)*base69 + (11683814533405765067/707800000000000000000000000000000 : ℝ)*base72 + (7130437246937/1769500000000000000000000000 : ℝ)*base74 + (1758762271636234933/707800000000000000000000000000000 : ℝ)*base75 + (10164603275704965067/707800000000000000000000000000000 : ℝ)*base78 + (3960946810107165067/707800000000000000000000000000000 : ℝ)*base80 + (1242446699001/884750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (33291821/5000000000000000000000 : ℝ)*base90 + (33291821/5000000000000000000000 : ℝ)*base92 + (33291821/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58961/100000 : ℝ) ≤ (521676860323166828133627942950769/884750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5707547/100000000000000 : ℝ)*(lower0) + (6702449/10000000000000 : ℝ)*(lower1) + (64837/200000000000 : ℝ)*(lower3) + (67210657/100000000000000 : ℝ)*(lower5) + (1500463965123681/50000000000000 : ℝ)*(major0) + (1500463965123681/50000000000000 : ℝ)*(major1) + (1500463965123681/50000000000000 : ℝ)*(major2) + (2023817497980729/50000000000000 : ℝ)*(sp0) + (2023794698751273/50000000000000 : ℝ)*(sp1) + (2023825738648213/50000000000000 : ℝ)*(sp2) + (77381704796831/4000000000000 : ℝ)*(sp3) + (1841306113/25000000000000 : ℝ)*(sp7) + (62079793881/100000000000000 : ℝ)*(sp9) + (16481334969/100000000000000 : ℝ)*(sp12) + (483637496286307/25000000000000 : ℝ)*(f.failure) + (2023825738648213/50000000000000 : ℝ)*(f.sum) + (6203949476527/1769500000000000000000000000 : ℝ)*base65 + (23559348399927183077/1769500000000000000000000000000000 : ℝ)*base68 + (133147173772235316923/1769500000000000000000000000000000 : ℝ)*base69 + (15230331146778683077/1769500000000000000000000000000000 : ℝ)*base72 + (1497516973211/353900000000000000000000000 : ℝ)*base74 + (19489591852530683077/1769500000000000000000000000000000 : ℝ)*base76 + (7896875518626183077/1769500000000000000000000000000000 : ℝ)*base78 + (7755945961129816923/1769500000000000000000000000000000 : ℝ)*base79 + (5705585117923/3539000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (26922837/2500000000000000000000 : ℝ)*base89 + (26922837/2500000000000000000000 : ℝ)*base91 + (26922837/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80013/100000 : ℝ) ≤ (566348074576725360891565167/707800000000000000000000000 : ℝ) := by norm_num
    linear_combination (488781/20000000000000 : ℝ)*(upper1) + (58781/500000000000 : ℝ)*(upper2) + (6369181/100000000000000 : ℝ)*(upper3) + (439733/50000000000000 : ℝ)*(lower5) + (3312620227834141/100000000000000 : ℝ)*(major0) + (3312620227834141/100000000000000 : ℝ)*(major1) + (3312620227834141/100000000000000 : ℝ)*(major2) + (584328919/100000000000000 : ℝ)*(sp0) + (4101508083/12500000000000 : ℝ)*(sp1) + (9529089499/50000000000000 : ℝ)*(sp2) + (278942843985279/6250000000000 : ℝ)*(sp8) + (55788165950359/1250000000000 : ℝ)*(sp9) + (892613405982877/20000000000000 : ℝ)*(sp10) + (133467663200847/6250000000000 : ℝ)*(sp11) + (133467663200847/6250000000000 : ℝ)*(f.failure) + (4463086088093383/100000000000000 : ℝ)*(f.sum) + (7593922901389/3539000000000000000000000000 : ℝ)*base65 + (26396375201729609103/3539000000000000000000000000000000 : ℝ)*base67 + (11628017844404390897/3539000000000000000000000000000000 : ℝ)*base70 + (921479236883390897/3539000000000000000000000000000000 : ℝ)*base72 + (229414308889/3539000000000000000000000000 : ℝ)*base73 + (17696114496227390897/3539000000000000000000000000000000 : ℝ)*base76 + (23186620524655609103/3539000000000000000000000000000000 : ℝ)*base77 + (8423119401513609103/3539000000000000000000000000000000 : ℝ)*base79 + (33648446966363/3539000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1046023/625000000000000000000 : ℝ)*base90 + (1046023/625000000000000000000 : ℝ)*base92 + (1046023/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84391/100000 : ℝ) ≤ (-93328315962447199888130018028453/110593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53809843/20000000000000 : ℝ)*(lower0) + (162545539/100000000000000 : ℝ)*(lower1) + (4961497/50000000000000 : ℝ)*(lower2) + (37853303/100000000000000 : ℝ)*(upper5) + (418650537586303/12500000000000 : ℝ)*(major0) + (418650537586303/12500000000000 : ℝ)*(major1) + (418650537586303/12500000000000 : ℝ)*(major2) + (326290377/12500000000000 : ℝ)*(sp0) + (30525867311/12500000000000 : ℝ)*(sp5) + (1742533061/6250000000000 : ℝ)*(sp7) + (456746890804159/10000000000000 : ℝ)*(sp12) + (4567227311426117/100000000000000 : ℝ)*(sp13) + (913494303672921/20000000000000 : ℝ)*(sp14) + (2159038675132999/100000000000000 : ℝ)*(sp15) + (86362662226479/4000000000000 : ℝ)*(f.failure) + (913494303672921/20000000000000 : ℝ)*(f.sum) + (8442059615799/1769500000000000000000000000 : ℝ)*base65 + (7764563227442613651/442375000000000000000000000000000 : ℝ)*base68 + (3878388929282488651/442375000000000000000000000000000 : ℝ)*base70 + (3410842304285238651/442375000000000000000000000000000 : ℝ)*base72 + (117396521892573/3539000000000000000000000000 : ℝ)*base74 + (154694700145988651/442375000000000000000000000000000 : ℝ)*base76 + (440363624197488651/442375000000000000000000000000000 : ℝ)*base78 + (1187329789784261349/442375000000000000000000000000000 : ℝ)*base79 + (20539711603/14156000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (582889/400000000000000000000 : ℝ)*base89 + (582889/400000000000000000000 : ℝ)*base91 + (582889/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1352_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62859/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58961/100000 : ℝ) else (80013/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84391/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1352_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1352_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62859/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58961/100000 : ℝ) else (80013/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84391/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1352_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62859/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58961/100000 : ℝ) else (80013/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84391/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
