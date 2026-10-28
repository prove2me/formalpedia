-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:27:46.987753+00:00
-- url     : https://prove2.me/submissions/a3c90259-837b-4ab7-a3b1-8d57fdb4288b

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
theorem support_rectangle_w1133_s6_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171165711/10000000000 : ℝ)*x 0 + (5393560897/10000000000 : ℝ)*x 1 + (658156121/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171165711/10000000000 : ℝ)^4163 ≤ (13191978067769/100000000000000 : ℝ)^3139 := by
    have hnat : (2171165711 : ℕ)^4163*100000000000000^3139 ≤ 13191978067769^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171165711 10000000000 13191978067769 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393560897/10000000000 : ℝ)^4163 ≤ (22048468880043/50000000000000 : ℝ)^3139 := by
    have hnat : (5393560897 : ℕ)^4163*50000000000000^3139 ≤ 22048468880043^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393560897 10000000000 22048468880043 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658156121/1250000000 : ℝ)^4163 ≤ (4271108416019/10000000000000 : ℝ)^3139 := by
    have hnat : (658156121 : ℕ)^4163*10000000000000^3139 ≤ 4271108416019^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658156121 1250000000 4271108416019 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171165711/10000000000 : ℝ), (5393560897/10000000000 : ℝ), (658156121/1250000000 : ℝ)] ![(13191978067769/100000000000000 : ℝ), (22048468880043/50000000000000 : ℝ), (4271108416019/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171165711/10000000000 : ℝ)|^4163 ≤ (13191978067769/100000000000000 : ℝ)^3139
        have hw : |(-2171165711/10000000000 : ℝ)|=(2171165711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393560897/10000000000 : ℝ)|^4163 ≤ (22048468880043/50000000000000 : ℝ)^3139
        have hw : |(5393560897/10000000000 : ℝ)|=(5393560897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658156121/1250000000 : ℝ)|^4163 ≤ (4271108416019/10000000000000 : ℝ)^3139
        have hw : |(658156121/1250000000 : ℝ)|=(658156121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s6_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344882101/10000000000 : ℝ)*x 0 + (-223625513/1000000000 : ℝ)*x 1 + (5265248947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344882101/10000000000 : ℝ)^4163 ≤ (43569894017653/100000000000000 : ℝ)^3139 := by
    have hnat : (5344882101 : ℕ)^4163*100000000000000^3139 ≤ 43569894017653^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344882101 10000000000 43569894017653 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223625513/1000000000 : ℝ)^4163 ≤ (1371902203639/10000000000000 : ℝ)^3139 := by
    have hnat : (223625513 : ℕ)^4163*10000000000000^3139 ≤ 1371902203639^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223625513 1000000000 1371902203639 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265248947/10000000000 : ℝ)^4163 ≤ (42711083934269/100000000000000 : ℝ)^3139 := by
    have hnat : (5265248947 : ℕ)^4163*100000000000000^3139 ≤ 42711083934269^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265248947 10000000000 42711083934269 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344882101/10000000000 : ℝ), (-223625513/1000000000 : ℝ), (5265248947/10000000000 : ℝ)] ![(43569894017653/100000000000000 : ℝ), (1371902203639/10000000000000 : ℝ), (42711083934269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344882101/10000000000 : ℝ)|^4163 ≤ (43569894017653/100000000000000 : ℝ)^3139
        have hw : |(5344882101/10000000000 : ℝ)|=(5344882101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223625513/1000000000 : ℝ)|^4163 ≤ (1371902203639/10000000000000 : ℝ)^3139
        have hw : |(-223625513/1000000000 : ℝ)|=(223625513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265248947/10000000000 : ℝ)|^4163 ≤ (42711083934269/100000000000000 : ℝ)^3139
        have hw : |(5265248947/10000000000 : ℝ)|=(5265248947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s6_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344882063/10000000000 : ℝ)*x 0 + (5265248969/10000000000 : ℝ)*x 1 + (-139765947/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344882063/10000000000 : ℝ)^4163 ≤ (43569893606837/100000000000000 : ℝ)^3139 := by
    have hnat : (5344882063 : ℕ)^4163*100000000000000^3139 ≤ 43569893606837^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344882063 10000000000 43569893606837 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265248969/10000000000 : ℝ)^4163 ≤ (10677771042737/25000000000000 : ℝ)^3139 := by
    have hnat : (5265248969 : ℕ)^4163*25000000000000^3139 ≤ 10677771042737^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265248969 10000000000 10677771042737 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139765947/625000000 : ℝ)^4163 ≤ (1714877776923/12500000000000 : ℝ)^3139 := by
    have hnat : (139765947 : ℕ)^4163*12500000000000^3139 ≤ 1714877776923^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139765947 625000000 1714877776923 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344882063/10000000000 : ℝ), (5265248969/10000000000 : ℝ), (-139765947/625000000 : ℝ)] ![(43569893606837/100000000000000 : ℝ), (10677771042737/25000000000000 : ℝ), (1714877776923/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344882063/10000000000 : ℝ)|^4163 ≤ (43569893606837/100000000000000 : ℝ)^3139
        have hw : |(5344882063/10000000000 : ℝ)|=(5344882063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265248969/10000000000 : ℝ)|^4163 ≤ (10677771042737/25000000000000 : ℝ)^3139
        have hw : |(5265248969/10000000000 : ℝ)|=(5265248969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139765947/625000000 : ℝ)|^4163 ≤ (1714877776923/12500000000000 : ℝ)^3139
        have hw : |(-139765947/625000000 : ℝ)|=(139765947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s6_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6821757/15625000 : ℝ)*x 0 + (4240366999/10000000000 : ℝ)*x 1 + (899037959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6821757/15625000 : ℝ)^4163 ≤ (33316733011533/100000000000000 : ℝ)^3139 := by
    have hnat : (6821757 : ℕ)^4163*100000000000000^3139 ≤ 33316733011533^3139*15625000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6821757 15625000 33316733011533 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240366999/10000000000 : ℝ)^4163 ≤ (16026015041671/50000000000000 : ℝ)^3139 := by
    have hnat : (4240366999 : ℕ)^4163*50000000000000^3139 ≤ 16026015041671^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240366999 10000000000 16026015041671 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899037959/2000000000 : ℝ)^4163 ≤ (8657809224299/25000000000000 : ℝ)^3139 := by
    have hnat : (899037959 : ℕ)^4163*25000000000000^3139 ≤ 8657809224299^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899037959 2000000000 8657809224299 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6821757/15625000 : ℝ), (4240366999/10000000000 : ℝ), (899037959/2000000000 : ℝ)] ![(33316733011533/100000000000000 : ℝ), (16026015041671/50000000000000 : ℝ), (8657809224299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6821757/15625000 : ℝ)|^4163 ≤ (33316733011533/100000000000000 : ℝ)^3139
        have hw : |(6821757/15625000 : ℝ)|=(6821757/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240366999/10000000000 : ℝ)|^4163 ≤ (16026015041671/50000000000000 : ℝ)^3139
        have hw : |(4240366999/10000000000 : ℝ)|=(4240366999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899037959/2000000000 : ℝ)|^4163 ≤ (8657809224299/25000000000000 : ℝ)^3139
        have hw : |(899037959/2000000000 : ℝ)|=(899037959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s6_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085585357/5000000000 : ℝ)*x 0 + (210622921/400000000 : ℝ)*x 1 + (107864713/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085585357/5000000000 : ℝ)^4163 ≤ (6596009191201/50000000000000 : ℝ)^3139 := by
    have hnat : (1085585357 : ℕ)^4163*50000000000000^3139 ≤ 6596009191201^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085585357 5000000000 6596009191201 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210622921/400000000 : ℝ)^4163 ≤ (42714570442449/100000000000000 : ℝ)^3139 := by
    have hnat : (210622921 : ℕ)^4163*100000000000000^3139 ≤ 42714570442449^3139*400000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210622921 400000000 42714570442449 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107864713/200000000 : ℝ)^4163 ≤ (11023352788469/25000000000000 : ℝ)^3139 := by
    have hnat : (107864713 : ℕ)^4163*25000000000000^3139 ≤ 11023352788469^3139*200000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107864713 200000000 11023352788469 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085585357/5000000000 : ℝ), (210622921/400000000 : ℝ), (107864713/200000000 : ℝ)] ![(6596009191201/50000000000000 : ℝ), (42714570442449/100000000000000 : ℝ), (11023352788469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085585357/5000000000 : ℝ)|^4163 ≤ (6596009191201/50000000000000 : ℝ)^3139
        have hw : |(-1085585357/5000000000 : ℝ)|=(1085585357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210622921/400000000 : ℝ)|^4163 ≤ (42714570442449/100000000000000 : ℝ)^3139
        have hw : |(210622921/400000000 : ℝ)|=(210622921/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107864713/200000000 : ℝ)|^4163 ≤ (11023352788469/25000000000000 : ℝ)^3139
        have hw : |(107864713/200000000 : ℝ)|=(107864713/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s6_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656197721/5000000000 : ℝ)*x 0 + (-2108268507/10000000000 : ℝ)*x 1 + (1348308913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656197721/5000000000 : ℝ)^4163 ≤ (21609515675801/50000000000000 : ℝ)^3139 := by
    have hnat : (2656197721 : ℕ)^4163*50000000000000^3139 ≤ 21609515675801^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656197721 5000000000 21609515675801 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108268507/10000000000 : ℝ)^4163 ≤ (101500459627/800000000000 : ℝ)^3139 := by
    have hnat : (2108268507 : ℕ)^4163*800000000000^3139 ≤ 101500459627^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108268507 10000000000 101500459627 800000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348308913/2500000000 : ℝ)^4163 ≤ (22046705587781/50000000000000 : ℝ)^3139 := by
    have hnat : (1348308913 : ℕ)^4163*50000000000000^3139 ≤ 22046705587781^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348308913 2500000000 22046705587781 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656197721/5000000000 : ℝ), (-2108268507/10000000000 : ℝ), (1348308913/2500000000 : ℝ)] ![(21609515675801/50000000000000 : ℝ), (101500459627/800000000000 : ℝ), (22046705587781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656197721/5000000000 : ℝ)|^4163 ≤ (21609515675801/50000000000000 : ℝ)^3139
        have hw : |(2656197721/5000000000 : ℝ)|=(2656197721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108268507/10000000000 : ℝ)|^4163 ≤ (101500459627/800000000000 : ℝ)^3139
        have hw : |(-2108268507/10000000000 : ℝ)|=(2108268507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348308913/2500000000 : ℝ)|^4163 ≤ (22046705587781/50000000000000 : ℝ)^3139
        have hw : |(1348308913/2500000000 : ℝ)|=(1348308913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s6_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312395441/10000000000 : ℝ)*x 0 + (337077229/625000000 : ℝ)*x 1 + (-2108268493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312395441/10000000000 : ℝ)^4163 ≤ (43219031340813/100000000000000 : ℝ)^3139 := by
    have hnat : (5312395441 : ℕ)^4163*100000000000000^3139 ≤ 43219031340813^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312395441 10000000000 43219031340813 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337077229/625000000 : ℝ)^4163 ≤ (1763736452227/4000000000000 : ℝ)^3139 := by
    have hnat : (337077229 : ℕ)^4163*4000000000000^3139 ≤ 1763736452227^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337077229 625000000 1763736452227 4000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108268493/10000000000 : ℝ)^4163 ≤ (12687557341639/100000000000000 : ℝ)^3139 := by
    have hnat : (2108268493 : ℕ)^4163*100000000000000^3139 ≤ 12687557341639^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108268493 10000000000 12687557341639 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312395441/10000000000 : ℝ), (337077229/625000000 : ℝ), (-2108268493/10000000000 : ℝ)] ![(43219031340813/100000000000000 : ℝ), (1763736452227/4000000000000 : ℝ), (12687557341639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312395441/10000000000 : ℝ)|^4163 ≤ (43219031340813/100000000000000 : ℝ)^3139
        have hw : |(5312395441/10000000000 : ℝ)|=(5312395441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337077229/625000000 : ℝ)|^4163 ≤ (1763736452227/4000000000000 : ℝ)^3139
        have hw : |(337077229/625000000 : ℝ)|=(337077229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108268493/10000000000 : ℝ)|^4163 ≤ (12687557341639/100000000000000 : ℝ)^3139
        have hw : |(-2108268493/10000000000 : ℝ)|=(2108268493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s6_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365934397/10000000000 : ℝ)*x 0 + (4494546177/10000000000 : ℝ)*x 1 + (265063309/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365934397/10000000000 : ℝ)^4163 ≤ (33316833376411/100000000000000 : ℝ)^3139 := by
    have hnat : (4365934397 : ℕ)^4163*100000000000000^3139 ≤ 33316833376411^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365934397 10000000000 33316833376411 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494546177/10000000000 : ℝ)^4163 ≤ (34624661028939/100000000000000 : ℝ)^3139 := by
    have hnat : (4494546177 : ℕ)^4163*100000000000000^3139 ≤ 34624661028939^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494546177 10000000000 34624661028939 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265063309/625000000 : ℝ)^4163 ≤ (1602925279327/5000000000000 : ℝ)^3139 := by
    have hnat : (265063309 : ℕ)^4163*5000000000000^3139 ≤ 1602925279327^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265063309 625000000 1602925279327 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365934397/10000000000 : ℝ), (4494546177/10000000000 : ℝ), (265063309/625000000 : ℝ)] ![(33316833376411/100000000000000 : ℝ), (34624661028939/100000000000000 : ℝ), (1602925279327/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365934397/10000000000 : ℝ)|^4163 ≤ (33316833376411/100000000000000 : ℝ)^3139
        have hw : |(4365934397/10000000000 : ℝ)|=(4365934397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494546177/10000000000 : ℝ)|^4163 ≤ (34624661028939/100000000000000 : ℝ)^3139
        have hw : |(4494546177/10000000000 : ℝ)|=(4494546177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265063309/625000000 : ℝ)|^4163 ≤ (1602925279327/5000000000000 : ℝ)^3139
        have hw : |(265063309/625000000 : ℝ)|=(265063309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5667/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5651/50000 : ℝ) ^ (8325/2048 : ℝ) ≤ (14162234647085541/100000000000000000000 : ℝ) := by
    have hpowers : (5651/50000 : ℝ)^8325 ≤ (14162234647085541/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5651 : ℕ)^8325*100000000000000000000^2048 ≤ 14162234647085541^2048*50000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5651 50000 14162234647085541 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5651/50000 : ℝ)) (X := (14162234647085541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2817/20000 : ℝ) ^ (8325/2048 : ℝ) ≤ (34653449993149889/100000000000000000000 : ℝ) := by
    have hpowers : (2817/20000 : ℝ)^8325 ≤ (34653449993149889/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2817 : ℕ)^8325*100000000000000000000^2048 ≤ 34653449993149889^2048*20000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 20000 34653449993149889 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/20000 : ℝ)) (X := (34653449993149889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014162234647085541/50000000000000000000 : ℝ) ≤ (5000348362281393/5000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50014162234647085541/50000000000000000000 : ℝ)^2048 ≤ (5000348362281393/5000000000000000 : ℝ)^8325 := by
      have hnat : (50014162234647085541 : ℕ)^2048*5000000000000000^8325 ≤ 5000348362281393^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014162234647085541 50000000000000000000 5000348362281393 5000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000348362281393/5000000000000000 : ℝ)) (X := (50014162234647085541/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004881568464023543/10000000000000000000 : ℝ) ≤ (10001200674218797/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (10004881568464023543/10000000000000000000 : ℝ)^2048 ≤ (10001200674218797/10000000000000000 : ℝ)^8325 := by
      have hnat : (10004881568464023543 : ℕ)^2048*10000000000000000^8325 ≤ 10001200674218797^8325*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004881568464023543 10000000000000000000 10001200674218797 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001200674218797/10000000000000000 : ℝ)) (X := (10004881568464023543/10000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034653449993149889/50000000000000000000 : ℝ) ≤ (1250213077984351/1250000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50034653449993149889/50000000000000000000 : ℝ)^2048 ≤ (1250213077984351/1250000000000000 : ℝ)^8325 := by
      have hnat : (50034653449993149889 : ℕ)^2048*1250000000000000^8325 ≤ 1250213077984351^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034653449993149889 50000000000000000000 1250213077984351 1250000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250213077984351/1250000000000000 : ℝ)) (X := (50034653449993149889/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14162234647085541/100000000000000000000 : ℝ) ≤ ((13910273853216880397/13915000000000000000 : ℝ)+2*(503949656011/278300000000000 : ℝ)*(5651/50000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (13910273853216880397/13915000000000000000 : ℝ)+2*(503949656011/278300000000000 : ℝ)*(5651/50000 : ℝ)=(5000348362281393/5000000000000000 : ℝ) by norm_num, show 1+2*(14162234647085541/100000000000000000000 : ℝ)=(50014162234647085541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34653449993149889/100000000000000000000 : ℝ)+(14162234647085541/100000000000000000000 : ℝ) ≤ ((13910273853216880397/13915000000000000000 : ℝ)+(503949656011/278300000000000 : ℝ)*((2817/20000 : ℝ)+(5651/50000 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (13910273853216880397/13915000000000000000 : ℝ)+(503949656011/278300000000000 : ℝ)*((2817/20000 : ℝ)+(5651/50000 : ℝ))=(10001200674218797/10000000000000000 : ℝ) by norm_num, show 1+(34653449993149889/100000000000000000000 : ℝ)+(14162234647085541/100000000000000000000 : ℝ)=(10004881568464023543/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34653449993149889/100000000000000000000 : ℝ) ≤ ((13910273853216880397/13915000000000000000 : ℝ)+2*(503949656011/278300000000000 : ℝ)*(2817/20000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (13910273853216880397/13915000000000000000 : ℝ)+2*(503949656011/278300000000000 : ℝ)*(2817/20000 : ℝ)=(1250213077984351/1250000000000000 : ℝ) by norm_num, show 1+2*(34653449993149889/100000000000000000000 : ℝ)=(50034653449993149889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13910273853216880397/13915000000000000000 : ℝ)*(X 1 0+X 2 0)+(503949656011/278300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13910273853216880397/13915000000000000000 : ℝ)) (alpha := (503949656011/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13910273853216880397/13915000000000000000 : ℝ)*(X 0 1+X 2 1)+(503949656011/278300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13910273853216880397/13915000000000000000 : ℝ)) (alpha := (503949656011/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13910273853216880397/13915000000000000000 : ℝ)*(X 0 2+X 1 2)+(503949656011/278300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13910273853216880397/13915000000000000000 : ℝ)) (alpha := (503949656011/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2171165711/10000000000 : ℝ)*X 0 0+(5393560897/10000000000 : ℝ)*X 0 1+(658156121/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344882101/10000000000 : ℝ)*X 1 0+(-223625513/1000000000 : ℝ)*X 1 1+(5265248947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344882063/10000000000 : ℝ)*X 2 0+(5265248969/10000000000 : ℝ)*X 2 1+(-139765947/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6821757/15625000 : ℝ)*X 0 0+(4240366999/10000000000 : ℝ)*X 0 1+(899037959/2000000000 : ℝ)*X 0 2+(6821757/15625000 : ℝ)*X 1 0+(4240366999/10000000000 : ℝ)*X 1 1+(899037959/2000000000 : ℝ)*X 1 2+(6821757/15625000 : ℝ)*X 2 0+(4240366999/10000000000 : ℝ)*X 2 1+(899037959/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1085585357/5000000000 : ℝ)*X 0 0+(210622921/400000000 : ℝ)*X 0 1+(107864713/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656197721/5000000000 : ℝ)*X 1 0+(-2108268507/10000000000 : ℝ)*X 1 1+(1348308913/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312395441/10000000000 : ℝ)*X 2 0+(337077229/625000000 : ℝ)*X 2 1+(-2108268493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365934397/10000000000 : ℝ)*X 0 0+(4494546177/10000000000 : ℝ)*X 0 1+(265063309/625000000 : ℝ)*X 0 2+(4365934397/10000000000 : ℝ)*X 1 0+(4494546177/10000000000 : ℝ)*X 1 1+(265063309/625000000 : ℝ)*X 1 2+(4365934397/10000000000 : ℝ)*X 2 0+(4494546177/10000000000 : ℝ)*X 2 1+(265063309/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69554424370067702254647/13915000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1169456213/100000000000000 : ℝ)*(base19) + (1023302327/100000000000000 : ℝ)*(base23) + (12125489/25000000000000 : ℝ)*(lower2) + (9212021/6250000000000 : ℝ)*(upper3) + (17592883/50000000000000 : ℝ)*(upper5) + (5858951673680001/100000000000000 : ℝ)*(major0) + (5858951673680001/100000000000000 : ℝ)*(major1) + (5858951673680001/100000000000000 : ℝ)*(major2) + (974192831229557/12500000000000 : ℝ)*(sp0) + (1558714389672007/20000000000000 : ℝ)*(sp1) + (7793572094513921/100000000000000 : ℝ)*(sp2) + (1962155802860639/50000000000000 : ℝ)*(sp3) + (1904248737/6250000000000 : ℝ)*(sp4) + (9228602547/50000000000000 : ℝ)*(sp7) + (981082515731593/25000000000000 : ℝ)*(f.failure) + (974196639727031/12500000000000 : ℝ)*(f.sum) + (21731762604601/13915000000000000000000000000 : ℝ)*base65 + (941791199336399127/126500000000000000000000000000000 : ℝ)*base67 + (853955321943399127/126500000000000000000000000000000 : ℝ)*base69 + (1375996840940100873/126500000000000000000000000000000 : ℝ)*base72 + (9012495864861/13915000000000000000000000000 : ℝ)*base73 + (899005648412899127/126500000000000000000000000000000 : ℝ)*base75 + (70702225172100873/126500000000000000000000000000000 : ℝ)*base78 + (522373641214100873/126500000000000000000000000000000 : ℝ)*base80 + (27368590900899/13915000000000000000000000000 : ℝ)*base82 + (1942241/2500000000000000000000 : ℝ)*base89 + (1942241/2500000000000000000000 : ℝ)*base91 + (1942241/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (744400712270369204294801979/86968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1556834917/100000000000000 : ℝ)*(base19) + (1709330253/100000000000000 : ℝ)*(base23) + (173118777/100000000000000 : ℝ)*(upper3) + (16732127/25000000000000 : ℝ)*(lower4) + (170865951/100000000000000 : ℝ)*(upper5) + (1472175023427869/25000000000000 : ℝ)*(major0) + (1472175023427869/25000000000000 : ℝ)*(major1) + (1472175023427869/25000000000000 : ℝ)*(major2) + (10658236151/25000000000000 : ℝ)*(sp1) + (47209141087/100000000000000 : ℝ)*(sp2) + (156662886519177/2000000000000 : ℝ)*(sp4) + (61196094813901/781250000000 : ℝ)*(sp5) + (7833095407487509/100000000000000 : ℝ)*(sp6) + (3944255576150609/100000000000000 : ℝ)*(sp7) + (3944255576150609/100000000000000 : ℝ)*(f.failure) + (156662886519177/2000000000000 : ℝ)*(f.sum) + (46729479564441/13915000000000000000000000000 : ℝ)*base65 + (457796661479644637/31625000000000000000000000000000 : ℝ)*base68 + (15074882143269637/31625000000000000000000000000000 : ℝ)*base70 + (218043131433394637/31625000000000000000000000000000 : ℝ)*base72 + (12173426547719/13915000000000000000000000000 : ℝ)*base74 + (24636110897269637/31625000000000000000000000000000 : ℝ)*base76 + (136220179109644637/31625000000000000000000000000000 : ℝ)*base78 + (362695335478230363/31625000000000000000000000000000 : ℝ)*base79 + (46011189184711/13915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (44884567/10000000000000000000000 : ℝ)*base90 + (44884567/10000000000000000000000 : ℝ)*base92 + (44884567/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1133_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1133_s7_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171193081/10000000000 : ℝ)*x 0 + (2696613827/5000000000 : ℝ)*x 1 + (5265564331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171193081/10000000000 : ℝ)^4163 ≤ (13192198618111/100000000000000 : ℝ)^3139 := by
    have hnat : (2171193081 : ℕ)^4163*100000000000000^3139 ≤ 13192198618111^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171193081 10000000000 13192198618111 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696613827/5000000000 : ℝ)^4163 ≤ (22046662227639/50000000000000 : ℝ)^3139 := by
    have hnat : (2696613827 : ℕ)^4163*50000000000000^3139 ≤ 22046662227639^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696613827 5000000000 22046662227639 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265564331/10000000000 : ℝ)^4163 ≤ (5339309613677/12500000000000 : ℝ)^3139 := by
    have hnat : (5265564331 : ℕ)^4163*12500000000000^3139 ≤ 5339309613677^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265564331 10000000000 5339309613677 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171193081/10000000000 : ℝ), (2696613827/5000000000 : ℝ), (5265564331/10000000000 : ℝ)] ![(13192198618111/100000000000000 : ℝ), (22046662227639/50000000000000 : ℝ), (5339309613677/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171193081/10000000000 : ℝ)|^4163 ≤ (13192198618111/100000000000000 : ℝ)^3139
        have hw : |(-2171193081/10000000000 : ℝ)|=(2171193081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696613827/5000000000 : ℝ)|^4163 ≤ (22046662227639/50000000000000 : ℝ)^3139
        have hw : |(2696613827/5000000000 : ℝ)|=(2696613827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265564331/10000000000 : ℝ)|^4163 ≤ (5339309613677/12500000000000 : ℝ)^3139
        have hw : |(5265564331/10000000000 : ℝ)|=(5265564331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167024961/312500000 : ℝ)*x 0 + (-89437953/400000000 : ℝ)*x 1 + (5265564347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167024961/312500000 : ℝ)^4163 ≤ (21784496469441/50000000000000 : ℝ)^3139 := by
    have hnat : (167024961 : ℕ)^4163*50000000000000^3139 ≤ 21784496469441^3139*312500000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167024961 312500000 21784496469441 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89437953/400000000 : ℝ)^4163 ≤ (6858264980197/50000000000000 : ℝ)^3139 := by
    have hnat : (89437953 : ℕ)^4163*50000000000000^3139 ≤ 6858264980197^3139*400000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89437953 400000000 6858264980197 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265564347/10000000000 : ℝ)^4163 ≤ (42714477081549/100000000000000 : ℝ)^3139 := by
    have hnat : (5265564347 : ℕ)^4163*100000000000000^3139 ≤ 42714477081549^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265564347 10000000000 42714477081549 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167024961/312500000 : ℝ), (-89437953/400000000 : ℝ), (5265564347/10000000000 : ℝ)] ![(21784496469441/50000000000000 : ℝ), (6858264980197/50000000000000 : ℝ), (42714477081549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167024961/312500000 : ℝ)|^4163 ≤ (21784496469441/50000000000000 : ℝ)^3139
        have hw : |(167024961/312500000 : ℝ)|=(167024961/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89437953/400000000 : ℝ)|^4163 ≤ (6858264980197/50000000000000 : ℝ)^3139
        have hw : |(-89437953/400000000 : ℝ)|=(89437953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265564347/10000000000 : ℝ)|^4163 ≤ (42714477081549/100000000000000 : ℝ)^3139
        have hw : |(5265564347/10000000000 : ℝ)|=(5265564347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344798771/10000000000 : ℝ)*x 0 + (5265564337/10000000000 : ℝ)*x 1 + (-447189763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344798771/10000000000 : ℝ)^4163 ≤ (43568993144289/100000000000000 : ℝ)^3139 := by
    have hnat : (5344798771 : ℕ)^4163*100000000000000^3139 ≤ 43568993144289^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344798771 10000000000 43568993144289 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265564337/10000000000 : ℝ)^4163 ≤ (21357238486983/50000000000000 : ℝ)^3139 := by
    have hnat : (5265564337 : ℕ)^4163*50000000000000^3139 ≤ 21357238486983^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265564337 10000000000 21357238486983 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447189763/2000000000 : ℝ)^4163 ≤ (13716529879037/100000000000000 : ℝ)^3139 := by
    have hnat : (447189763 : ℕ)^4163*100000000000000^3139 ≤ 13716529879037^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447189763 2000000000 13716529879037 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344798771/10000000000 : ℝ), (5265564337/10000000000 : ℝ), (-447189763/2000000000 : ℝ)] ![(43568993144289/100000000000000 : ℝ), (21357238486983/50000000000000 : ℝ), (13716529879037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344798771/10000000000 : ℝ)|^4163 ≤ (43568993144289/100000000000000 : ℝ)^3139
        have hw : |(5344798771/10000000000 : ℝ)|=(5344798771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265564337/10000000000 : ℝ)|^4163 ≤ (21357238486983/50000000000000 : ℝ)^3139
        have hw : |(5265564337/10000000000 : ℝ)|=(5265564337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447189763/2000000000 : ℝ)|^4163 ≤ (13716529879037/100000000000000 : ℝ)^3139
        have hw : |(-447189763/2000000000 : ℝ)|=(447189763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (436594103/1000000000 : ℝ)*x 0 + (4241008949/10000000000 : ℝ)*x 1 + (2247271763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436594103/1000000000 : ℝ)^4163 ≤ (2082306281603/6250000000000 : ℝ)^3139 := by
    have hnat : (436594103 : ℕ)^4163*6250000000000^3139 ≤ 2082306281603^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436594103 1000000000 2082306281603 6250000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241008949/10000000000 : ℝ)^4163 ≤ (16029232768133/50000000000000 : ℝ)^3139 := by
    have hnat : (4241008949 : ℕ)^4163*50000000000000^3139 ≤ 16029232768133^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241008949 10000000000 16029232768133 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247271763/5000000000 : ℝ)^4163 ≤ (8656158486053/25000000000000 : ℝ)^3139 := by
    have hnat : (2247271763 : ℕ)^4163*25000000000000^3139 ≤ 8656158486053^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247271763 5000000000 8656158486053 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436594103/1000000000 : ℝ), (4241008949/10000000000 : ℝ), (2247271763/5000000000 : ℝ)] ![(2082306281603/6250000000000 : ℝ), (16029232768133/50000000000000 : ℝ), (8656158486053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436594103/1000000000 : ℝ)|^4163 ≤ (2082306281603/6250000000000 : ℝ)^3139
        have hw : |(436594103/1000000000 : ℝ)|=(436594103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241008949/10000000000 : ℝ)|^4163 ≤ (16029232768133/50000000000000 : ℝ)^3139
        have hw : |(4241008949/10000000000 : ℝ)|=(4241008949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247271763/5000000000 : ℝ)|^4163 ≤ (8656158486053/25000000000000 : ℝ)^3139
        have hw : |(2247271763/5000000000 : ℝ)|=(2247271763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-108559781/500000000 : ℝ)*x 0 + (1316473263/2500000000 : ℝ)*x 1 + (5392899599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108559781/500000000 : ℝ)^4163 ≤ (6596109538843/50000000000000 : ℝ)^3139 := by
    have hnat : (108559781 : ℕ)^4163*50000000000000^3139 ≤ 6596109538843^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108559781 500000000 6596109538843 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316473263/2500000000 : ℝ)^4163 ≤ (21359006718851/50000000000000 : ℝ)^3139 := by
    have hnat : (1316473263 : ℕ)^4163*50000000000000^3139 ≤ 21359006718851^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316473263 2500000000 21359006718851 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392899599/10000000000 : ℝ)^4163 ≤ (4408976747433/10000000000000 : ℝ)^3139 := by
    have hnat : (5392899599 : ℕ)^4163*10000000000000^3139 ≤ 4408976747433^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392899599 10000000000 4408976747433 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108559781/500000000 : ℝ), (1316473263/2500000000 : ℝ), (5392899599/10000000000 : ℝ)] ![(6596109538843/50000000000000 : ℝ), (21359006718851/50000000000000 : ℝ), (4408976747433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108559781/500000000 : ℝ)|^4163 ≤ (6596109538843/50000000000000 : ℝ)^3139
        have hw : |(-108559781/500000000 : ℝ)|=(108559781/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316473263/2500000000 : ℝ)|^4163 ≤ (21359006718851/50000000000000 : ℝ)^3139
        have hw : |(1316473263/2500000000 : ℝ)|=(1316473263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392899599/10000000000 : ℝ)|^4163 ≤ (4408976747433/10000000000000 : ℝ)^3139
        have hw : |(5392899599/10000000000 : ℝ)|=(5392899599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312472217/10000000000 : ℝ)*x 0 + (-6589391/31250000 : ℝ)*x 1 + (5392911469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312472217/10000000000 : ℝ)^4163 ≤ (2701241232149/6250000000000 : ℝ)^3139 := by
    have hnat : (5312472217 : ℕ)^4163*6250000000000^3139 ≤ 2701241232149^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312472217 10000000000 2701241232149 6250000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6589391/31250000 : ℝ)^4163 ≤ (12690244092839/100000000000000 : ℝ)^3139 := by
    have hnat : (6589391 : ℕ)^4163*100000000000000^3139 ≤ 12690244092839^3139*31250000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6589391 31250000 12690244092839 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392911469/10000000000 : ℝ)^4163 ≤ (11022474043797/25000000000000 : ℝ)^3139 := by
    have hnat : (5392911469 : ℕ)^4163*25000000000000^3139 ≤ 11022474043797^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392911469 10000000000 11022474043797 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312472217/10000000000 : ℝ), (-6589391/31250000 : ℝ), (5392911469/10000000000 : ℝ)] ![(2701241232149/6250000000000 : ℝ), (12690244092839/100000000000000 : ℝ), (11022474043797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312472217/10000000000 : ℝ)|^4163 ≤ (2701241232149/6250000000000 : ℝ)^3139
        have hw : |(5312472217/10000000000 : ℝ)|=(5312472217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6589391/31250000 : ℝ)|^4163 ≤ (12690244092839/100000000000000 : ℝ)^3139
        have hw : |(-6589391/31250000 : ℝ)|=(6589391/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392911469/10000000000 : ℝ)|^4163 ≤ (11022474043797/25000000000000 : ℝ)^3139
        have hw : |(5392911469/10000000000 : ℝ)|=(5392911469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312475677/10000000000 : ℝ)*x 0 + (1348226541/2500000000 : ℝ)*x 1 + (-2108607649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312475677/10000000000 : ℝ)^4163 ≤ (43219897046097/100000000000000 : ℝ)^3139 := by
    have hnat : (5312475677 : ℕ)^4163*100000000000000^3139 ≤ 43219897046097^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312475677 10000000000 43219897046097 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348226541/2500000000 : ℝ)^4163 ≤ (44089838655543/100000000000000 : ℝ)^3139 := by
    have hnat : (1348226541 : ℕ)^4163*100000000000000^3139 ≤ 44089838655543^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348226541 2500000000 44089838655543 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108607649/10000000000 : ℝ)^4163 ≤ (6345132139151/50000000000000 : ℝ)^3139 := by
    have hnat : (2108607649 : ℕ)^4163*50000000000000^3139 ≤ 6345132139151^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108607649 10000000000 6345132139151 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312475677/10000000000 : ℝ), (1348226541/2500000000 : ℝ), (-2108607649/10000000000 : ℝ)] ![(43219897046097/100000000000000 : ℝ), (44089838655543/100000000000000 : ℝ), (6345132139151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312475677/10000000000 : ℝ)|^4163 ≤ (43219897046097/100000000000000 : ℝ)^3139
        have hw : |(5312475677/10000000000 : ℝ)|=(5312475677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348226541/2500000000 : ℝ)|^4163 ≤ (44089838655543/100000000000000 : ℝ)^3139
        have hw : |(1348226541/2500000000 : ℝ)|=(1348226541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108607649/10000000000 : ℝ)|^4163 ≤ (6345132139151/50000000000000 : ℝ)^3139
        have hw : |(-2108607649/10000000000 : ℝ)|=(2108607649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873189979/2000000000 : ℝ)*x 0 + (898781477/2000000000 : ℝ)*x 1 + (4241648273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873189979/2000000000 : ℝ)^4163 ≤ (33316990223879/100000000000000 : ℝ)^3139 := by
    have hnat : (873189979 : ℕ)^4163*100000000000000^3139 ≤ 33316990223879^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873189979 2000000000 33316990223879 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898781477/2000000000 : ℝ)^4163 ≤ (34618134771833/100000000000000 : ℝ)^3139 := by
    have hnat : (898781477 : ℕ)^4163*100000000000000^3139 ≤ 34618134771833^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898781477 2000000000 34618134771833 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241648273/10000000000 : ℝ)^4163 ≤ (4008109372471/12500000000000 : ℝ)^3139 := by
    have hnat : (4241648273 : ℕ)^4163*12500000000000^3139 ≤ 4008109372471^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241648273 10000000000 4008109372471 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873189979/2000000000 : ℝ), (898781477/2000000000 : ℝ), (4241648273/10000000000 : ℝ)] ![(33316990223879/100000000000000 : ℝ), (34618134771833/100000000000000 : ℝ), (4008109372471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873189979/2000000000 : ℝ)|^4163 ≤ (33316990223879/100000000000000 : ℝ)^3139
        have hw : |(873189979/2000000000 : ℝ)|=(873189979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898781477/2000000000 : ℝ)|^4163 ≤ (34618134771833/100000000000000 : ℝ)^3139
        have hw : |(898781477/2000000000 : ℝ)|=(898781477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241648273/10000000000 : ℝ)|^4163 ≤ (4008109372471/12500000000000 : ℝ)^3139
        have hw : |(4241648273/10000000000 : ℝ)|=(4241648273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_8 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8371822971/10000000000 : ℝ)*x 0 + (-343591379/5000000000 : ℝ)*x 1 + (1379606171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8371822971/10000000000 : ℝ)^4163 ≤ (39501401578781/50000000000000 : ℝ)^3139 := by
    have hnat : (8371822971 : ℕ)^4163*50000000000000^3139 ≤ 39501401578781^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8371822971 10000000000 39501401578781 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343591379/5000000000 : ℝ)^4163 ≤ (89650699677/3125000000000 : ℝ)^3139 := by
    have hnat : (343591379 : ℕ)^4163*3125000000000^3139 ≤ 89650699677^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343591379 5000000000 89650699677 3125000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379606171/5000000000 : ℝ)^4163 ≤ (1812837444477/10000000000000 : ℝ)^3139 := by
    have hnat : (1379606171 : ℕ)^4163*10000000000000^3139 ≤ 1812837444477^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379606171 5000000000 1812837444477 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8371822971/10000000000 : ℝ), (-343591379/5000000000 : ℝ), (1379606171/5000000000 : ℝ)] ![(39501401578781/50000000000000 : ℝ), (89650699677/3125000000000 : ℝ), (1812837444477/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8371822971/10000000000 : ℝ)|^4163 ≤ (39501401578781/50000000000000 : ℝ)^3139
        have hw : |(8371822971/10000000000 : ℝ)|=(8371822971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343591379/5000000000 : ℝ)|^4163 ≤ (89650699677/3125000000000 : ℝ)^3139
        have hw : |(-343591379/5000000000 : ℝ)|=(343591379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379606171/5000000000 : ℝ)|^4163 ≤ (1812837444477/10000000000000 : ℝ)^3139
        have hw : |(1379606171/5000000000 : ℝ)|=(1379606171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s7_9 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1624397017/2000000000 : ℝ)*x 0 + (151608717/500000000 : ℝ)*x 1 + (-809379637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624397017/2000000000 : ℝ)^4163 ≤ (18972839243239/25000000000000 : ℝ)^3139 := by
    have hnat : (1624397017 : ℕ)^4163*25000000000000^3139 ≤ 18972839243239^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624397017 2000000000 18972839243239 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151608717/500000000 : ℝ)^4163 ≤ (20544367211563/100000000000000 : ℝ)^3139 := by
    have hnat : (151608717 : ℕ)^4163*100000000000000^3139 ≤ 20544367211563^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151608717 500000000 20544367211563 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809379637/10000000000 : ℝ)^4163 ≤ (111383618701/3125000000000 : ℝ)^3139 := by
    have hnat : (809379637 : ℕ)^4163*3125000000000^3139 ≤ 111383618701^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809379637 10000000000 111383618701 3125000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1624397017/2000000000 : ℝ), (151608717/500000000 : ℝ), (-809379637/10000000000 : ℝ)] ![(18972839243239/25000000000000 : ℝ), (20544367211563/100000000000000 : ℝ), (111383618701/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1624397017/2000000000 : ℝ)|^4163 ≤ (18972839243239/25000000000000 : ℝ)^3139
        have hw : |(1624397017/2000000000 : ℝ)|=(1624397017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151608717/500000000 : ℝ)|^4163 ≤ (20544367211563/100000000000000 : ℝ)^3139
        have hw : |(151608717/500000000 : ℝ)|=(151608717/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-809379637/10000000000 : ℝ)|^4163 ≤ (111383618701/3125000000000 : ℝ)^3139
        have hw : |(-809379637/10000000000 : ℝ)|=(809379637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2809/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (8325/2048 : ℝ) ≤ (7162970347751761/50000000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^8325 ≤ (7162970347751761/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5667 : ℕ)^8325*50000000000000000000^2048 ≤ 7162970347751761^2048*50000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 7162970347751761 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (7162970347751761/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3513/25000 : ℝ) ^ (8325/2048 : ℝ) ≤ (17162299840414599/50000000000000000000 : ℝ) := by
    have hpowers : (3513/25000 : ℝ)^8325 ≤ (17162299840414599/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3513 : ℕ)^8325*50000000000000000000^2048 ≤ 17162299840414599^2048*25000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3513 25000 17162299840414599 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3513/25000 : ℝ)) (X := (17162299840414599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007162970347751761/25000000000000000000 : ℝ) ≤ (10000704777367337/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (25007162970347751761/25000000000000000000 : ℝ)^2048 ≤ (10000704777367337/10000000000000000 : ℝ)^8325 := by
      have hnat : (25007162970347751761 : ℕ)^2048*10000000000000000^8325 ≤ 10000704777367337^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007162970347751761 25000000000000000000 10000704777367337 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000704777367337/10000000000000000 : ℝ)) (X := (25007162970347751761/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250608131754704159/1250000000000000000 : ℝ) ≤ (10001196613062881/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (1250608131754704159/1250000000000000000 : ℝ)^2048 ≤ (10001196613062881/10000000000000000 : ℝ)^8325 := by
      have hnat : (1250608131754704159 : ℕ)^2048*10000000000000000^8325 ≤ 10001196613062881^8325*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250608131754704159 1250000000000000000 10001196613062881 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001196613062881/10000000000000000 : ℝ)) (X := (1250608131754704159/1250000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017162299840414599/25000000000000000000 : ℝ) ≤ (400067537950337/400000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (25017162299840414599/25000000000000000000 : ℝ)^2048 ≤ (400067537950337/400000000000000 : ℝ)^8325 := by
      have hnat : (25017162299840414599 : ℕ)^2048*400000000000000^8325 ≤ 400067537950337^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017162299840414599 25000000000000000000 400067537950337 400000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400067537950337/400000000000000 : ℝ)) (X := (25017162299840414599/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7162970347751761/50000000000000000000 : ℝ) ≤ ((1509487036296546143/1510000000000000000 : ℝ)+2*(6831051327/3775000000000 : ℝ)*(5667/50000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (1509487036296546143/1510000000000000000 : ℝ)+2*(6831051327/3775000000000 : ℝ)*(5667/50000 : ℝ)=(10000704777367337/10000000000000000 : ℝ) by norm_num, show 1+2*(7162970347751761/50000000000000000000 : ℝ)=(25007162970347751761/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17162299840414599/50000000000000000000 : ℝ)+(7162970347751761/50000000000000000000 : ℝ) ≤ ((1509487036296546143/1510000000000000000 : ℝ)+(6831051327/3775000000000 : ℝ)*((3513/25000 : ℝ)+(5667/50000 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (1509487036296546143/1510000000000000000 : ℝ)+(6831051327/3775000000000 : ℝ)*((3513/25000 : ℝ)+(5667/50000 : ℝ))=(10001196613062881/10000000000000000 : ℝ) by norm_num, show 1+(17162299840414599/50000000000000000000 : ℝ)+(7162970347751761/50000000000000000000 : ℝ)=(1250608131754704159/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17162299840414599/50000000000000000000 : ℝ) ≤ ((1509487036296546143/1510000000000000000 : ℝ)+2*(6831051327/3775000000000 : ℝ)*(3513/25000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (1509487036296546143/1510000000000000000 : ℝ)+2*(6831051327/3775000000000 : ℝ)*(3513/25000 : ℝ)=(400067537950337/400000000000000 : ℝ) by norm_num, show 1+2*(17162299840414599/50000000000000000000 : ℝ)=(25017162299840414599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1509487036296546143/1510000000000000000 : ℝ)*(X 1 0+X 2 0)+(6831051327/3775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (1509487036296546143/1510000000000000000 : ℝ)) (alpha := (6831051327/3775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1509487036296546143/1510000000000000000 : ℝ)*(X 0 1+X 2 1)+(6831051327/3775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (1509487036296546143/1510000000000000000 : ℝ)) (alpha := (6831051327/3775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1509487036296546143/1510000000000000000 : ℝ)*(X 0 2+X 1 2)+(6831051327/3775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (1509487036296546143/1510000000000000000 : ℝ)) (alpha := (6831051327/3775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2171193081/10000000000 : ℝ)*X 0 0+(2696613827/5000000000 : ℝ)*X 0 1+(5265564331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167024961/312500000 : ℝ)*X 1 0+(-89437953/400000000 : ℝ)*X 1 1+(5265564347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344798771/10000000000 : ℝ)*X 2 0+(5265564337/10000000000 : ℝ)*X 2 1+(-447189763/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436594103/1000000000 : ℝ)*X 0 0+(4241008949/10000000000 : ℝ)*X 0 1+(2247271763/5000000000 : ℝ)*X 0 2+(436594103/1000000000 : ℝ)*X 1 0+(4241008949/10000000000 : ℝ)*X 1 1+(2247271763/5000000000 : ℝ)*X 1 2+(436594103/1000000000 : ℝ)*X 2 0+(4241008949/10000000000 : ℝ)*X 2 1+(2247271763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-108559781/500000000 : ℝ)*X 0 0+(1316473263/2500000000 : ℝ)*X 0 1+(5392899599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312472217/10000000000 : ℝ)*X 1 0+(-6589391/31250000 : ℝ)*X 1 1+(5392911469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312475677/10000000000 : ℝ)*X 2 0+(1348226541/2500000000 : ℝ)*X 2 1+(-2108607649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873189979/2000000000 : ℝ)*X 0 0+(898781477/2000000000 : ℝ)*X 0 1+(4241648273/10000000000 : ℝ)*X 0 2+(873189979/2000000000 : ℝ)*X 1 0+(898781477/2000000000 : ℝ)*X 1 1+(4241648273/10000000000 : ℝ)*X 1 2+(873189979/2000000000 : ℝ)*X 2 0+(898781477/2000000000 : ℝ)*X 2 1+(4241648273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((8371822971/10000000000 : ℝ)*X 1 0+(-343591379/5000000000 : ℝ)*X 1 1+(1379606171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1624397017/2000000000 : ℝ)*X 2 0+(151608717/500000000 : ℝ)*X 2 1+(-809379637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (197414595653256453107769987/75500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21287491/4000000000000 : ℝ)*(base19) + (134768181/25000000000000 : ℝ)*(base23) + (11202821/100000000000000 : ℝ)*(lower2) + (57349531/100000000000000 : ℝ)*(upper3) + (64410953/100000000000000 : ℝ)*(upper5) + (5888692833201899/100000000000000 : ℝ)*(major0) + (5888692833201899/100000000000000 : ℝ)*(major1) + (5888692833201899/100000000000000 : ℝ)*(major2) + (3916559299286419/50000000000000 : ℝ)*(sp0) + (7833134334001703/100000000000000 : ℝ)*(sp1) + (3916567163558127/50000000000000 : ℝ)*(sp2) + (3944242885300713/100000000000000 : ℝ)*(sp3) + (16267616139/100000000000000 : ℝ)*(sp4) + (7827755337/100000000000000 : ℝ)*(sp7) + (78885014261121/2000000000000 : ℝ)*(f.failure) + (3916567433094489/50000000000000 : ℝ)*(f.sum) + (5557842024907/755000000000000000000000000 : ℝ)*base65 + (305627605515925557/151000000000000000000000000000000 : ℝ)*base67 + (277418689099925557/151000000000000000000000000000000 : ℝ)*base69 + (1765601909666925557/151000000000000000000000000000000 : ℝ)*base71 + (994158552393/755000000000000000000000000 : ℝ)*base74 + (99719880497925557/151000000000000000000000000000000 : ℝ)*base75 + (1313651483788925557/151000000000000000000000000000000 : ℝ)*base77 + (1012699402497925557/151000000000000000000000000000000 : ℝ)*base79 + (1292898932003/755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1168423/200000000000000000000 : ℝ)*base90 + (1168423/200000000000000000000 : ℝ)*base92 + (1168423/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3904172180688385013541/755000000000000000000000000 : ℝ) := by norm_num
    linear_combination (772499107/50000000000000 : ℝ)*(lower4) + (995034433/50000000000000 : ℝ)*(lower5) + (1479740548472423/25000000000000 : ℝ)*(major0) + (1479740548472423/25000000000000 : ℝ)*(major1) + (1479740548472423/25000000000000 : ℝ)*(major2) + (93262981999/20000000000000 : ℝ)*(sp1) + (347027616821/100000000000000 : ℝ)*(sp2) + (715383251/400000000000 : ℝ)*(sp3) + (7873399062701577/100000000000000 : ℝ)*(sp4) + (787291981032853/10000000000000 : ℝ)*(sp5) + (61508216950691/781250000000 : ℝ)*(sp6) + (991086576723853/25000000000000 : ℝ)*(sp7) + (12937463053/100000000000000 : ℝ)*(sp8) + (265396309/100000000000000 : ℝ)*(sp9) + (1982262576354081/50000000000000 : ℝ)*(f.failure) + (7873399062701577/100000000000000 : ℝ)*(f.sum) + (653236663159/188750000000000000000000000 : ℝ)*base65 + (557798622592414489/37750000000000000000000000000000 : ℝ)*base67 + (195037820151335511/37750000000000000000000000000000 : ℝ)*base70 + (149607057985164489/37750000000000000000000000000000 : ℝ)*base71 + (4014999605781/755000000000000000000000000 : ℝ)*base73 + (113025618160835511/37750000000000000000000000000000 : ℝ)*base76 + (224552516562914489/37750000000000000000000000000000 : ℝ)*base77 + (112055278646335511/37750000000000000000000000000000 : ℝ)*base80 + (761986339189/188750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (54352903/5000000000000000000000 : ℝ)*base90 + (54352903/5000000000000000000000 : ℝ)*base92 + (54352903/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1133_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1133_s8_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-434239641/2000000000 : ℝ)*x 0 + (1348289227/2500000000 : ℝ)*x 1 + (1053126359/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434239641/2000000000 : ℝ)^4163 ≤ (13192239907943/100000000000000 : ℝ)^3139 := by
    have hnat : (434239641 : ℕ)^4163*100000000000000^3139 ≤ 13192239907943^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434239641 2000000000 13192239907943 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348289227/2500000000 : ℝ)^4163 ≤ (44092557376183/100000000000000 : ℝ)^3139 := by
    have hnat : (1348289227 : ℕ)^4163*100000000000000^3139 ≤ 44092557376183^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348289227 2500000000 44092557376183 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053126359/2000000000 : ℝ)^4163 ≤ (42715202711581/100000000000000 : ℝ)^3139 := by
    have hnat : (1053126359 : ℕ)^4163*100000000000000^3139 ≤ 42715202711581^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053126359 2000000000 42715202711581 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434239641/2000000000 : ℝ), (1348289227/2500000000 : ℝ), (1053126359/2000000000 : ℝ)] ![(13192239907943/100000000000000 : ℝ), (44092557376183/100000000000000 : ℝ), (42715202711581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434239641/2000000000 : ℝ)|^4163 ≤ (13192239907943/100000000000000 : ℝ)^3139
        have hw : |(-434239641/2000000000 : ℝ)|=(434239641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348289227/2500000000 : ℝ)|^4163 ≤ (44092557376183/100000000000000 : ℝ)^3139
        have hw : |(1348289227/2500000000 : ℝ)|=(1348289227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053126359/2000000000 : ℝ)|^4163 ≤ (42715202711581/100000000000000 : ℝ)^3139
        have hw : |(1053126359/2000000000 : ℝ)|=(1053126359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s8_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53447813/100000000 : ℝ)*x 0 + (-2235882871/10000000000 : ℝ)*x 1 + (5265631761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53447813/100000000 : ℝ)^4163 ≤ (10892201066853/25000000000000 : ℝ)^3139 := by
    have hnat : (53447813 : ℕ)^4163*25000000000000^3139 ≤ 10892201066853^3139*100000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53447813 100000000 10892201066853 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235882871/10000000000 : ℝ)^4163 ≤ (13715993377847/100000000000000 : ℝ)^3139 := by
    have hnat : (2235882871 : ℕ)^4163*100000000000000^3139 ≤ 13715993377847^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235882871 10000000000 13715993377847 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265631761/10000000000 : ℝ)^4163 ≤ (10678800586449/25000000000000 : ℝ)^3139 := by
    have hnat : (5265631761 : ℕ)^4163*25000000000000^3139 ≤ 10678800586449^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265631761 10000000000 10678800586449 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53447813/100000000 : ℝ), (-2235882871/10000000000 : ℝ), (5265631761/10000000000 : ℝ)] ![(10892201066853/25000000000000 : ℝ), (13715993377847/100000000000000 : ℝ), (10678800586449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53447813/100000000 : ℝ)|^4163 ≤ (10892201066853/25000000000000 : ℝ)^3139
        have hw : |(53447813/100000000 : ℝ)|=(53447813/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235882871/10000000000 : ℝ)|^4163 ≤ (13715993377847/100000000000000 : ℝ)^3139
        have hw : |(-2235882871/10000000000 : ℝ)|=(2235882871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265631761/10000000000 : ℝ)|^4163 ≤ (10678800586449/25000000000000 : ℝ)^3139
        have hw : |(5265631761/10000000000 : ℝ)|=(5265631761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s8_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344781333/10000000000 : ℝ)*x 0 + (526563173/1000000000 : ℝ)*x 1 + (-558970717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344781333/10000000000 : ℝ)^4163 ≤ (43568804624171/100000000000000 : ℝ)^3139 := by
    have hnat : (5344781333 : ℕ)^4163*100000000000000^3139 ≤ 43568804624171^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344781333 10000000000 43568804624171 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526563173/1000000000 : ℝ)^4163 ≤ (21357601006143/50000000000000 : ℝ)^3139 := by
    have hnat : (526563173 : ℕ)^4163*50000000000000^3139 ≤ 21357601006143^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526563173 1000000000 21357601006143 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558970717/2500000000 : ℝ)^4163 ≤ (85724958459/625000000000 : ℝ)^3139 := by
    have hnat : (558970717 : ℕ)^4163*625000000000^3139 ≤ 85724958459^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558970717 2500000000 85724958459 625000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344781333/10000000000 : ℝ), (526563173/1000000000 : ℝ), (-558970717/2500000000 : ℝ)] ![(43568804624171/100000000000000 : ℝ), (21357601006143/50000000000000 : ℝ), (85724958459/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344781333/10000000000 : ℝ)|^4163 ≤ (43568804624171/100000000000000 : ℝ)^3139
        have hw : |(5344781333/10000000000 : ℝ)|=(5344781333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526563173/1000000000 : ℝ)|^4163 ≤ (21357601006143/50000000000000 : ℝ)^3139
        have hw : |(526563173/1000000000 : ℝ)|=(526563173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558970717/2500000000 : ℝ)|^4163 ≤ (85724958459/625000000000 : ℝ)^3139
        have hw : |(-558970717/2500000000 : ℝ)|=(558970717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s8_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182972267/5000000000 : ℝ)*x 0 + (4241145589/10000000000 : ℝ)*x 1 + (2247202989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182972267/5000000000 : ℝ)^4163 ≤ (260288562249/781250000000 : ℝ)^3139 := by
    have hnat : (2182972267 : ℕ)^4163*781250000000^3139 ≤ 260288562249^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182972267 5000000000 260288562249 781250000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241145589/10000000000 : ℝ)^4163 ≤ (32059835372889/100000000000000 : ℝ)^3139 := by
    have hnat : (4241145589 : ℕ)^4163*100000000000000^3139 ≤ 32059835372889^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241145589 10000000000 32059835372889 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247202989/5000000000 : ℝ)^4163 ≤ (34623228651457/100000000000000 : ℝ)^3139 := by
    have hnat : (2247202989 : ℕ)^4163*100000000000000^3139 ≤ 34623228651457^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247202989 5000000000 34623228651457 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182972267/5000000000 : ℝ), (4241145589/10000000000 : ℝ), (2247202989/5000000000 : ℝ)] ![(260288562249/781250000000 : ℝ), (32059835372889/100000000000000 : ℝ), (34623228651457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182972267/5000000000 : ℝ)|^4163 ≤ (260288562249/781250000000 : ℝ)^3139
        have hw : |(2182972267/5000000000 : ℝ)|=(2182972267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241145589/10000000000 : ℝ)|^4163 ≤ (32059835372889/100000000000000 : ℝ)^3139
        have hw : |(4241145589/10000000000 : ℝ)|=(4241145589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247202989/5000000000 : ℝ)|^4163 ≤ (34623228651457/100000000000000 : ℝ)^3139
        have hw : |(2247202989/5000000000 : ℝ)|=(2247202989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s8_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-434240623/2000000000 : ℝ)*x 0 + (5265951863/10000000000 : ℝ)*x 1 + (5392835673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434240623/2000000000 : ℝ)^4163 ≤ (6596139736683/50000000000000 : ℝ)^3139 := by
    have hnat : (434240623 : ℕ)^4163*50000000000000^3139 ≤ 6596139736683^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434240623 2000000000 6596139736683 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265951863/10000000000 : ℝ)^4163 ≤ (5339830770059/12500000000000 : ℝ)^3139 := by
    have hnat : (5265951863 : ℕ)^4163*12500000000000^3139 ≤ 5339830770059^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265951863 10000000000 5339830770059 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392835673/10000000000 : ℝ)^4163 ≤ (44089074356199/100000000000000 : ℝ)^3139 := by
    have hnat : (5392835673 : ℕ)^4163*100000000000000^3139 ≤ 44089074356199^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392835673 10000000000 44089074356199 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434240623/2000000000 : ℝ), (5265951863/10000000000 : ℝ), (5392835673/10000000000 : ℝ)] ![(6596139736683/50000000000000 : ℝ), (5339830770059/12500000000000 : ℝ), (44089074356199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434240623/2000000000 : ℝ)|^4163 ≤ (6596139736683/50000000000000 : ℝ)^3139
        have hw : |(-434240623/2000000000 : ℝ)|=(434240623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265951863/10000000000 : ℝ)|^4163 ≤ (5339830770059/12500000000000 : ℝ)^3139
        have hw : |(5265951863/10000000000 : ℝ)|=(5265951863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392835673/10000000000 : ℝ)|^4163 ≤ (44089074356199/100000000000000 : ℝ)^3139
        have hw : |(5392835673/10000000000 : ℝ)|=(5392835673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s8_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312493771/10000000000 : ℝ)*x 0 + (-105433947/500000000 : ℝ)*x 1 + (2696417839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312493771/10000000000 : ℝ)^4163 ≤ (8644018454333/20000000000000 : ℝ)^3139 := by
    have hnat : (5312493771 : ℕ)^4163*20000000000000^3139 ≤ 8644018454333^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312493771 10000000000 8644018454333 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105433947/500000000 : ℝ)^4163 ≤ (6345416648859/50000000000000 : ℝ)^3139 := by
    have hnat : (105433947 : ℕ)^4163*50000000000000^3139 ≤ 6345416648859^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105433947 500000000 6345416648859 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696417839/5000000000 : ℝ)^4163 ≤ (11022268602603/25000000000000 : ℝ)^3139 := by
    have hnat : (2696417839 : ℕ)^4163*25000000000000^3139 ≤ 11022268602603^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696417839 5000000000 11022268602603 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312493771/10000000000 : ℝ), (-105433947/500000000 : ℝ), (2696417839/5000000000 : ℝ)] ![(8644018454333/20000000000000 : ℝ), (6345416648859/50000000000000 : ℝ), (11022268602603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312493771/10000000000 : ℝ)|^4163 ≤ (8644018454333/20000000000000 : ℝ)^3139
        have hw : |(5312493771/10000000000 : ℝ)|=(5312493771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105433947/500000000 : ℝ)|^4163 ≤ (6345416648859/50000000000000 : ℝ)^3139
        have hw : |(-105433947/500000000 : ℝ)|=(105433947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696417839/5000000000 : ℝ)|^4163 ≤ (11022268602603/25000000000000 : ℝ)^3139
        have hw : |(2696417839/5000000000 : ℝ)|=(2696417839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s8_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265624687/500000000 : ℝ)*x 0 + (337052233/625000000 : ℝ)*x 1 + (-1054339457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265624687/500000000 : ℝ)^4163 ≤ (4322009193719/10000000000000 : ℝ)^3139 := by
    have hnat : (265624687 : ℕ)^4163*10000000000000^3139 ≤ 4322009193719^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265624687 500000000 4322009193719 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337052233/625000000 : ℝ)^4163 ≤ (5511134369067/12500000000000 : ℝ)^3139 := by
    have hnat : (337052233 : ℕ)^4163*12500000000000^3139 ≤ 5511134369067^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337052233 625000000 5511134369067 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054339457/5000000000 : ℝ)^4163 ≤ (6345416545097/50000000000000 : ℝ)^3139 := by
    have hnat : (1054339457 : ℕ)^4163*50000000000000^3139 ≤ 6345416545097^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054339457 5000000000 6345416545097 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265624687/500000000 : ℝ), (337052233/625000000 : ℝ), (-1054339457/5000000000 : ℝ)] ![(4322009193719/10000000000000 : ℝ), (5511134369067/12500000000000 : ℝ), (6345416545097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265624687/500000000 : ℝ)|^4163 ≤ (4322009193719/10000000000000 : ℝ)^3139
        have hw : |(265624687/500000000 : ℝ)|=(265624687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337052233/625000000 : ℝ)|^4163 ≤ (5511134369067/12500000000000 : ℝ)^3139
        have hw : |(337052233/625000000 : ℝ)|=(337052233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054339457/5000000000 : ℝ)|^4163 ≤ (6345416545097/50000000000000 : ℝ)^3139
        have hw : |(-1054339457/5000000000 : ℝ)|=(1054339457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s8_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365954293/10000000000 : ℝ)*x 0 + (4493770197/10000000000 : ℝ)*x 1 + (4241783631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365954293/10000000000 : ℝ)^4163 ≤ (1665851736693/5000000000000 : ℝ)^3139 := by
    have hnat : (4365954293 : ℕ)^4163*5000000000000^3139 ≤ 1665851736693^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365954293 10000000000 1665851736693 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493770197/10000000000 : ℝ)^4163 ≤ (17308366610903/50000000000000 : ℝ)^3139 := by
    have hnat : (4493770197 : ℕ)^4163*50000000000000^3139 ≤ 17308366610903^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493770197 10000000000 17308366610903 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241783631/10000000000 : ℝ)^4163 ≤ (4008279003851/12500000000000 : ℝ)^3139 := by
    have hnat : (4241783631 : ℕ)^4163*12500000000000^3139 ≤ 4008279003851^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241783631 10000000000 4008279003851 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365954293/10000000000 : ℝ), (4493770197/10000000000 : ℝ), (4241783631/10000000000 : ℝ)] ![(1665851736693/5000000000000 : ℝ), (17308366610903/50000000000000 : ℝ), (4008279003851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365954293/10000000000 : ℝ)|^4163 ≤ (1665851736693/5000000000000 : ℝ)^3139
        have hw : |(4365954293/10000000000 : ℝ)|=(4365954293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493770197/10000000000 : ℝ)|^4163 ≤ (17308366610903/50000000000000 : ℝ)^3139
        have hw : |(4493770197/10000000000 : ℝ)|=(4493770197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241783631/10000000000 : ℝ)|^4163 ≤ (4008279003851/12500000000000 : ℝ)^3139
        have hw : |(4241783631/10000000000 : ℝ)|=(4241783631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5671/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11341/100000 : ℝ) ^ (8325/2048 : ℝ) ≤ (14361940761558199/100000000000000000000 : ℝ) := by
    have hpowers : (11341/100000 : ℝ)^8325 ≤ (14361940761558199/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11341 : ℕ)^8325*100000000000000000000^2048 ≤ 14361940761558199^2048*100000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11341 100000 14361940761558199 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11341/100000 : ℝ)) (X := (14361940761558199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2809/20000 : ℝ) ^ (8325/2048 : ℝ) ≤ (17127573571761049/50000000000000000000 : ℝ) := by
    have hpowers : (2809/20000 : ℝ)^8325 ≤ (17127573571761049/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2809 : ℕ)^8325*50000000000000000000^2048 ≤ 17127573571761049^2048*20000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 20000 17127573571761049 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/20000 : ℝ)) (X := (17127573571761049/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014361940761558199/50000000000000000000 : ℝ) ≤ (10000706548230797/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50014361940761558199/50000000000000000000 : ℝ)^2048 ≤ (10000706548230797/10000000000000000 : ℝ)^8325 := by
      have hnat : (50014361940761558199 : ℕ)^2048*10000000000000000^8325 ≤ 10000706548230797^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014361940761558199 50000000000000000000 10000706548230797 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706548230797/10000000000000000 : ℝ)) (X := (50014361940761558199/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048617087905080297/100000000000000000000 : ℝ) ≤ (250029894760341/250000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (100048617087905080297/100000000000000000000 : ℝ)^2048 ≤ (250029894760341/250000000000000 : ℝ)^8325 := by
      have hnat : (100048617087905080297 : ℕ)^2048*250000000000000^8325 ≤ 250029894760341^8325*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048617087905080297 100000000000000000000 250029894760341 250000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250029894760341/250000000000000 : ℝ)) (X := (100048617087905080297/100000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017127573571761049/25000000000000000000 : ℝ) ≤ (10001685032596483/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (25017127573571761049/25000000000000000000 : ℝ)^2048 ≤ (10001685032596483/10000000000000000 : ℝ)^8325 := by
      have hnat : (25017127573571761049 : ℕ)^2048*10000000000000000^8325 ≤ 10001685032596483^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017127573571761049 25000000000000000000 10001685032596483 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001685032596483/10000000000000000 : ℝ)) (X := (25017127573571761049/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14361940761558199/100000000000000000000 : ℝ) ≤ ((13515406757612415081/13520000000000000000 : ℝ)+2*(489242182843/270400000000000 : ℝ)*(11341/100000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (13515406757612415081/13520000000000000000 : ℝ)+2*(489242182843/270400000000000 : ℝ)*(11341/100000 : ℝ)=(10000706548230797/10000000000000000 : ℝ) by norm_num, show 1+2*(14361940761558199/100000000000000000000 : ℝ)=(50014361940761558199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17127573571761049/50000000000000000000 : ℝ)+(14361940761558199/100000000000000000000 : ℝ) ≤ ((13515406757612415081/13520000000000000000 : ℝ)+(489242182843/270400000000000 : ℝ)*((2809/20000 : ℝ)+(11341/100000 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (13515406757612415081/13520000000000000000 : ℝ)+(489242182843/270400000000000 : ℝ)*((2809/20000 : ℝ)+(11341/100000 : ℝ))=(250029894760341/250000000000000 : ℝ) by norm_num, show 1+(17127573571761049/50000000000000000000 : ℝ)+(14361940761558199/100000000000000000000 : ℝ)=(100048617087905080297/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17127573571761049/50000000000000000000 : ℝ) ≤ ((13515406757612415081/13520000000000000000 : ℝ)+2*(489242182843/270400000000000 : ℝ)*(2809/20000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (13515406757612415081/13520000000000000000 : ℝ)+2*(489242182843/270400000000000 : ℝ)*(2809/20000 : ℝ)=(10001685032596483/10000000000000000 : ℝ) by norm_num, show 1+2*(17127573571761049/50000000000000000000 : ℝ)=(25017127573571761049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13515406757612415081/13520000000000000000 : ℝ)*(X 1 0+X 2 0)+(489242182843/270400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (13515406757612415081/13520000000000000000 : ℝ)) (alpha := (489242182843/270400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13515406757612415081/13520000000000000000 : ℝ)*(X 0 1+X 2 1)+(489242182843/270400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (13515406757612415081/13520000000000000000 : ℝ)) (alpha := (489242182843/270400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13515406757612415081/13520000000000000000 : ℝ)*(X 0 2+X 1 2)+(489242182843/270400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (13515406757612415081/13520000000000000000 : ℝ)) (alpha := (489242182843/270400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-434239641/2000000000 : ℝ)*X 0 0+(1348289227/2500000000 : ℝ)*X 0 1+(1053126359/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53447813/100000000 : ℝ)*X 1 0+(-2235882871/10000000000 : ℝ)*X 1 1+(5265631761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344781333/10000000000 : ℝ)*X 2 0+(526563173/1000000000 : ℝ)*X 2 1+(-558970717/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182972267/5000000000 : ℝ)*X 0 0+(4241145589/10000000000 : ℝ)*X 0 1+(2247202989/5000000000 : ℝ)*X 0 2+(2182972267/5000000000 : ℝ)*X 1 0+(4241145589/10000000000 : ℝ)*X 1 1+(2247202989/5000000000 : ℝ)*X 1 2+(2182972267/5000000000 : ℝ)*X 2 0+(4241145589/10000000000 : ℝ)*X 2 1+(2247202989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-434240623/2000000000 : ℝ)*X 0 0+(5265951863/10000000000 : ℝ)*X 0 1+(5392835673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312493771/10000000000 : ℝ)*X 1 0+(-105433947/500000000 : ℝ)*X 1 1+(2696417839/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265624687/500000000 : ℝ)*X 2 0+(337052233/625000000 : ℝ)*X 2 1+(-1054339457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365954293/10000000000 : ℝ)*X 0 0+(4493770197/10000000000 : ℝ)*X 0 1+(4241783631/10000000000 : ℝ)*X 0 2+(4365954293/10000000000 : ℝ)*X 1 0+(4493770197/10000000000 : ℝ)*X 1 1+(4241783631/10000000000 : ℝ)*X 1 2+(4365954293/10000000000 : ℝ)*X 2 0+(4493770197/10000000000 : ℝ)*X 2 1+(4241783631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87030489844036143292497/13520000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1365028609/100000000000000 : ℝ)*(base19) + (340848343/25000000000000 : ℝ)*(base23) + (26751493/100000000000000 : ℝ)*(lower2) + (76884341/50000000000000 : ℝ)*(upper3) + (32606973/25000000000000 : ℝ)*(upper5) + (5895106097040353/100000000000000 : ℝ)*(major0) + (5895106097040353/100000000000000 : ℝ)*(major1) + (5895106097040353/100000000000000 : ℝ)*(major2) + (7841629037397273/100000000000000 : ℝ)*(sp0) + (980208036584069/12500000000000 : ℝ)*(sp1) + (7841664294307789/100000000000000 : ℝ)*(sp2) + (1974262640580849/50000000000000 : ℝ)*(sp3) + (36620303889/100000000000000 : ℝ)*(sp4) + (10520322811/50000000000000 : ℝ)*(sp7) + (98713658045183/2500000000000 : ℝ)*(f.failure) + (7841665657701161/100000000000000 : ℝ)*(f.sum) + (51257102665019/13520000000000000000000000000 : ℝ)*base65 + (34705565632122286407/1352000000000000000000000000000000 : ℝ)*base68 + (25200041265394286407/1352000000000000000000000000000000 : ℝ)*base70 + (27742504467634286407/1352000000000000000000000000000000 : ℝ)*base72 + (27956794817701/13520000000000000000000000000 : ℝ)*base74 + (20863684742125713593/1352000000000000000000000000000000 : ℝ)*base75 + (4907179947141713593/1352000000000000000000000000000000 : ℝ)*base77 + (4477371155469713593/1352000000000000000000000000000000 : ℝ)*base79 + (79079489640901/13520000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1224071/250000000000000000000 : ℝ)*base89 + (1224071/250000000000000000000 : ℝ)*base91 + (1224071/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8794774409954393180517/2704000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194487917/25000000000000 : ℝ)*(base19) + (759255717/100000000000000 : ℝ)*(base23) + (263180759/100000000000000 : ℝ)*(lower1) + (19834991/20000000000000 : ℝ)*(upper3) + (1686179/25000000000000 : ℝ)*(lower4) + (82274031/100000000000000 : ℝ)*(upper5) + (1184965935069557/20000000000000 : ℝ)*(major0) + (1184965935069557/20000000000000 : ℝ)*(major1) + (1184965935069557/20000000000000 : ℝ)*(major2) + (1200896319/50000000000000 : ℝ)*(sp2) + (1576240809250371/20000000000000 : ℝ)*(sp4) + (7881203268300187/100000000000000 : ℝ)*(sp5) + (7881200885203501/100000000000000 : ℝ)*(sp6) + (79369103920537/2000000000000 : ℝ)*(sp7) + (79369103920537/2000000000000 : ℝ)*(f.failure) + (1576240809250371/20000000000000 : ℝ)*(f.sum) + (15246528501849/2704000000000000000000000000 : ℝ)*base66 + (11070090370157660883/270400000000000000000000000000000 : ℝ)*base68 + (21644500162339117/270400000000000000000000000000000 : ℝ)*base69 + (22667837440837539117/270400000000000000000000000000000 : ℝ)*base71 + (6503385009129/2704000000000000000000000000 : ℝ)*base74 + (13304005059356060883/270400000000000000000000000000000 : ℝ)*base76 + (1617374683759260883/270400000000000000000000000000000 : ℝ)*base78 + (753898204391139117/270400000000000000000000000000000 : ℝ)*base79 + (14589813295543/2704000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (139569/200000000000000000000 : ℝ)*base89 + (139569/200000000000000000000 : ℝ)*base91 + (139569/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1133_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1133_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1133_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1133_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1133_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
