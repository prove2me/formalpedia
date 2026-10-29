-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:53.327859+00:00
-- url     : https://prove2.me/submissions/ad28e544-4e85-43cd-9b83-0f6b12e4c35a

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
theorem support_rectangle_w1311_s6_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207104963/1000000000 : ℝ)*x 0 + (676791799/1250000000 : ℝ)*x 1 + (2621791083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207104963/1000000000 : ℝ)^4271 ≤ (3151220990563/25000000000000 : ℝ)^3247 := by
    have hnat : (207104963 : ℕ)^4271*25000000000000^3247 ≤ 3151220990563^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207104963 1000000000 3151220990563 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676791799/1250000000 : ℝ)^4271 ≤ (8923674173729/20000000000000 : ℝ)^3247 := by
    have hnat : (676791799 : ℕ)^4271*20000000000000^3247 ≤ 8923674173729^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676791799 1250000000 8923674173729 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621791083/5000000000 : ℝ)^4271 ≤ (42776745148669/100000000000000 : ℝ)^3247 := by
    have hnat : (2621791083 : ℕ)^4271*100000000000000^3247 ≤ 42776745148669^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621791083 5000000000 42776745148669 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207104963/1000000000 : ℝ), (676791799/1250000000 : ℝ), (2621791083/5000000000 : ℝ)] ![(3151220990563/25000000000000 : ℝ), (8923674173729/20000000000000 : ℝ), (42776745148669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207104963/1000000000 : ℝ)|^4271 ≤ (3151220990563/25000000000000 : ℝ)^3247
        have hw : |(-207104963/1000000000 : ℝ)|=(207104963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676791799/1250000000 : ℝ)|^4271 ≤ (8923674173729/20000000000000 : ℝ)^3247
        have hw : |(676791799/1250000000 : ℝ)|=(676791799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621791083/5000000000 : ℝ)|^4271 ≤ (42776745148669/100000000000000 : ℝ)^3247
        have hw : |(2621791083/5000000000 : ℝ)|=(2621791083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s6_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349517573/10000000000 : ℝ)*x 0 + (-539518829/2500000000 : ℝ)*x 1 + (2621790823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349517573/10000000000 : ℝ)^4271 ≤ (8783421618059/20000000000000 : ℝ)^3247 := by
    have hnat : (5349517573 : ℕ)^4271*20000000000000^3247 ≤ 8783421618059^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349517573 10000000000 8783421618059 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539518829/2500000000 : ℝ)^4271 ≤ (6653076160051/50000000000000 : ℝ)^3247 := by
    have hnat : (539518829 : ℕ)^4271*50000000000000^3247 ≤ 6653076160051^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539518829 2500000000 6653076160051 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621790823/5000000000 : ℝ)^4271 ≤ (42776739568719/100000000000000 : ℝ)^3247 := by
    have hnat : (2621790823 : ℕ)^4271*100000000000000^3247 ≤ 42776739568719^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621790823 5000000000 42776739568719 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349517573/10000000000 : ℝ), (-539518829/2500000000 : ℝ), (2621790823/5000000000 : ℝ)] ![(8783421618059/20000000000000 : ℝ), (6653076160051/50000000000000 : ℝ), (42776739568719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349517573/10000000000 : ℝ)|^4271 ≤ (8783421618059/20000000000000 : ℝ)^3247
        have hw : |(5349517573/10000000000 : ℝ)|=(5349517573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539518829/2500000000 : ℝ)|^4271 ≤ (6653076160051/50000000000000 : ℝ)^3247
        have hw : |(-539518829/2500000000 : ℝ)|=(539518829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621790823/5000000000 : ℝ)|^4271 ≤ (42776739568719/100000000000000 : ℝ)^3247
        have hw : |(2621790823/5000000000 : ℝ)|=(2621790823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s6_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8559227/16000000 : ℝ)*x 0 + (1310895503/2500000000 : ℝ)*x 1 + (-2158075761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8559227/16000000 : ℝ)^4271 ≤ (4391710055289/10000000000000 : ℝ)^3247 := by
    have hnat : (8559227 : ℕ)^4271*10000000000000^3247 ≤ 4391710055289^3247*16000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8559227 16000000 4391710055289 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310895503/2500000000 : ℝ)^4271 ≤ (8555348699229/20000000000000 : ℝ)^3247 := by
    have hnat : (1310895503 : ℕ)^4271*20000000000000^3247 ≤ 8555348699229^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310895503 2500000000 8555348699229 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158075761/10000000000 : ℝ)^4271 ≤ (6653077964577/50000000000000 : ℝ)^3247 := by
    have hnat : (2158075761 : ℕ)^4271*50000000000000^3247 ≤ 6653077964577^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158075761 10000000000 6653077964577 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8559227/16000000 : ℝ), (1310895503/2500000000 : ℝ), (-2158075761/10000000000 : ℝ)] ![(4391710055289/10000000000000 : ℝ), (8555348699229/20000000000000 : ℝ), (6653077964577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8559227/16000000 : ℝ)|^4271 ≤ (4391710055289/10000000000000 : ℝ)^3247
        have hw : |(8559227/16000000 : ℝ)|=(8559227/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310895503/2500000000 : ℝ)|^4271 ≤ (8555348699229/20000000000000 : ℝ)^3247
        have hw : |(1310895503/2500000000 : ℝ)|=(1310895503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2158075761/10000000000 : ℝ)|^4271 ≤ (6653077964577/50000000000000 : ℝ)^3247
        have hw : |(-2158075761/10000000000 : ℝ)|=(2158075761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s6_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083696853/2500000000 : ℝ)*x 0 + (260091193/625000000 : ℝ)*x 1 + (4514946021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083696853/2500000000 : ℝ)^4271 ≤ (33302670018707/100000000000000 : ℝ)^3247 := by
    have hnat : (1083696853 : ℕ)^4271*100000000000000^3247 ≤ 33302670018707^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083696853 2500000000 33302670018707 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260091193/625000000 : ℝ)^4271 ≤ (3945280498931/12500000000000 : ℝ)^3247 := by
    have hnat : (260091193 : ℕ)^4271*12500000000000^3247 ≤ 3945280498931^3247*625000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260091193 625000000 3945280498931 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514946021/10000000000 : ℝ)^4271 ≤ (35135085981151/100000000000000 : ℝ)^3247 := by
    have hnat : (4514946021 : ℕ)^4271*100000000000000^3247 ≤ 35135085981151^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514946021 10000000000 35135085981151 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083696853/2500000000 : ℝ), (260091193/625000000 : ℝ), (4514946021/10000000000 : ℝ)] ![(33302670018707/100000000000000 : ℝ), (3945280498931/12500000000000 : ℝ), (35135085981151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083696853/2500000000 : ℝ)|^4271 ≤ (33302670018707/100000000000000 : ℝ)^3247
        have hw : |(1083696853/2500000000 : ℝ)|=(1083696853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260091193/625000000 : ℝ)|^4271 ≤ (3945280498931/12500000000000 : ℝ)^3247
        have hw : |(260091193/625000000 : ℝ)|=(260091193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514946021/10000000000 : ℝ)|^4271 ≤ (35135085981151/100000000000000 : ℝ)^3247
        have hw : |(4514946021/10000000000 : ℝ)|=(4514946021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s6_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071062511/10000000000 : ℝ)*x 0 + (2622095953/5000000000 : ℝ)*x 1 + (169178789/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071062511/10000000000 : ℝ)^4271 ≤ (126049870829/1000000000000 : ℝ)^3247 := by
    have hnat : (2071062511 : ℕ)^4271*1000000000000^3247 ≤ 126049870829^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071062511 10000000000 126049870829 1000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622095953/5000000000 : ℝ)^4271 ≤ (21391644094451/50000000000000 : ℝ)^3247 := by
    have hnat : (2622095953 : ℕ)^4271*50000000000000^3247 ≤ 21391644094451^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622095953 5000000000 21391644094451 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169178789/312500000 : ℝ)^4271 ≤ (5576465588863/12500000000000 : ℝ)^3247 := by
    have hnat : (169178789 : ℕ)^4271*12500000000000^3247 ≤ 5576465588863^3247*312500000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169178789 312500000 5576465588863 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071062511/10000000000 : ℝ), (2622095953/5000000000 : ℝ), (169178789/312500000 : ℝ)] ![(126049870829/1000000000000 : ℝ), (21391644094451/50000000000000 : ℝ), (5576465588863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071062511/10000000000 : ℝ)|^4271 ≤ (126049870829/1000000000000 : ℝ)^3247
        have hw : |(-2071062511/10000000000 : ℝ)|=(2071062511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622095953/5000000000 : ℝ)|^4271 ≤ (21391644094451/50000000000000 : ℝ)^3247
        have hw : |(2622095953/5000000000 : ℝ)|=(2622095953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169178789/312500000 : ℝ)|^4271 ≤ (5576465588863/12500000000000 : ℝ)^3247
        have hw : |(169178789/312500000 : ℝ)|=(169178789/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s6_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10611393/20000000 : ℝ)*x 0 + (-496984103/2500000000 : ℝ)*x 1 + (5413721253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10611393/20000000 : ℝ)^4271 ≤ (5430564422427/12500000000000 : ℝ)^3247 := by
    have hnat : (10611393 : ℕ)^4271*12500000000000^3247 ≤ 5430564422427^3247*20000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10611393 20000000 5430564422427 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496984103/2500000000 : ℝ)^4271 ≤ (2985939959083/25000000000000 : ℝ)^3247 := by
    have hnat : (496984103 : ℕ)^4271*25000000000000^3247 ≤ 2985939959083^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496984103 2500000000 2985939959083 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413721253/10000000000 : ℝ)^4271 ≤ (446117247651/1000000000000 : ℝ)^3247 := by
    have hnat : (5413721253 : ℕ)^4271*1000000000000^3247 ≤ 446117247651^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413721253 10000000000 446117247651 1000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10611393/20000000 : ℝ), (-496984103/2500000000 : ℝ), (5413721253/10000000000 : ℝ)] ![(5430564422427/12500000000000 : ℝ), (2985939959083/25000000000000 : ℝ), (446117247651/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10611393/20000000 : ℝ)|^4271 ≤ (5430564422427/12500000000000 : ℝ)^3247
        have hw : |(10611393/20000000 : ℝ)|=(10611393/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496984103/2500000000 : ℝ)|^4271 ≤ (2985939959083/25000000000000 : ℝ)^3247
        have hw : |(-496984103/2500000000 : ℝ)|=(496984103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413721253/10000000000 : ℝ)|^4271 ≤ (446117247651/1000000000000 : ℝ)^3247
        have hw : |(5413721253/10000000000 : ℝ)|=(5413721253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s6_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326424139/2500000000 : ℝ)*x 0 + (5413721213/10000000000 : ℝ)*x 1 + (-248492049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326424139/2500000000 : ℝ)^4271 ≤ (4344451598257/10000000000000 : ℝ)^3247 := by
    have hnat : (1326424139 : ℕ)^4271*10000000000000^3247 ≤ 4344451598257^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326424139 2500000000 4344451598257 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413721213/10000000000 : ℝ)^4271 ≤ (44611724331529/100000000000000 : ℝ)^3247 := by
    have hnat : (5413721213 : ℕ)^4271*100000000000000^3247 ≤ 44611724331529^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413721213 10000000000 44611724331529 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248492049/1250000000 : ℝ)^4271 ≤ (5971879839137/50000000000000 : ℝ)^3247 := by
    have hnat : (248492049 : ℕ)^4271*50000000000000^3247 ≤ 5971879839137^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248492049 1250000000 5971879839137 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326424139/2500000000 : ℝ), (5413721213/10000000000 : ℝ), (-248492049/1250000000 : ℝ)] ![(4344451598257/10000000000000 : ℝ), (44611724331529/100000000000000 : ℝ), (5971879839137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326424139/2500000000 : ℝ)|^4271 ≤ (4344451598257/10000000000000 : ℝ)^3247
        have hw : |(1326424139/2500000000 : ℝ)|=(1326424139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413721213/10000000000 : ℝ)|^4271 ≤ (44611724331529/100000000000000 : ℝ)^3247
        have hw : |(5413721213/10000000000 : ℝ)|=(5413721213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248492049/1250000000 : ℝ)|^4271 ≤ (5971879839137/50000000000000 : ℝ)^3247
        have hw : |(-248492049/1250000000 : ℝ)|=(248492049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s6_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541851703/1250000000 : ℝ)*x 0 + (225684139/500000000 : ℝ)*x 1 + (52034107/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541851703/1250000000 : ℝ)^4271 ≤ (33302934904769/100000000000000 : ℝ)^3247 := by
    have hnat : (541851703 : ℕ)^4271*100000000000000^3247 ≤ 33302934904769^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541851703 1250000000 33302934904769 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225684139/500000000 : ℝ)^4271 ≤ (8780538963529/25000000000000 : ℝ)^3247 := by
    have hnat : (225684139 : ℕ)^4271*25000000000000^3247 ≤ 8780538963529^3247*500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225684139 500000000 8780538963529 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52034107/125000000 : ℝ)^4271 ≤ (7893727308717/25000000000000 : ℝ)^3247 := by
    have hnat : (52034107 : ℕ)^4271*25000000000000^3247 ≤ 7893727308717^3247*125000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52034107 125000000 7893727308717 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541851703/1250000000 : ℝ), (225684139/500000000 : ℝ), (52034107/125000000 : ℝ)] ![(33302934904769/100000000000000 : ℝ), (8780538963529/25000000000000 : ℝ), (7893727308717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541851703/1250000000 : ℝ)|^4271 ≤ (33302934904769/100000000000000 : ℝ)^3247
        have hw : |(541851703/1250000000 : ℝ)|=(541851703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225684139/500000000 : ℝ)|^4271 ≤ (8780538963529/25000000000000 : ℝ)^3247
        have hw : |(225684139/500000000 : ℝ)|=(225684139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52034107/125000000 : ℝ)|^4271 ≤ (7893727308717/25000000000000 : ℝ)^3247
        have hw : |(52034107/125000000 : ℝ)|=(52034107/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11073/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (459/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1383/12500 : ℝ) ^ (2135/512 : ℝ) ≤ (1288541600184667/12500000000000000000 : ℝ) := by
    have hpowers : (1383/12500 : ℝ)^2135 ≤ (1288541600184667/12500000000000000000 : ℝ)^512 := by
      have hnat : (1383 : ℕ)^2135*12500000000000000000^512 ≤ 1288541600184667^512*12500^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1383 12500 1288541600184667 12500000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1383/12500 : ℝ)) (X := (1288541600184667/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7349/50000 : ℝ) ^ (2135/512 : ℝ) ≤ (16846199356017973/50000000000000000000 : ℝ) := by
    have hpowers : (7349/50000 : ℝ)^2135 ≤ (16846199356017973/50000000000000000000 : ℝ)^512 := by
      have hnat : (7349 : ℕ)^2135*50000000000000000000^512 ≤ 16846199356017973^512*50000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7349 50000 16846199356017973 50000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7349/50000 : ℝ)) (X := (16846199356017973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251288541600184667/6250000000000000000 : ℝ) ≤ (5000247187487439/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (6251288541600184667/6250000000000000000 : ℝ)^512 ≤ (5000247187487439/5000000000000000 : ℝ)^2135 := by
      have hnat : (6251288541600184667 : ℕ)^512*5000000000000000^2135 ≤ 5000247187487439^2135*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251288541600184667 6250000000000000000 5000247187487439 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000247187487439/5000000000000000 : ℝ)) (X := (6251288541600184667/6250000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022000365756756641/50000000000000000000 : ℝ) ≤ (5000527508378733/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50022000365756756641/50000000000000000000 : ℝ)^512 ≤ (5000527508378733/5000000000000000 : ℝ)^2135 := by
      have hnat : (50022000365756756641 : ℕ)^512*5000000000000000^2135 ≤ 5000527508378733^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022000365756756641 50000000000000000000 5000527508378733 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000527508378733/5000000000000000 : ℝ)) (X := (50022000365756756641/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016846199356017973/25000000000000000000 : ℝ) ≤ (5000807829270027/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (25016846199356017973/25000000000000000000 : ℝ)^512 ≤ (5000807829270027/5000000000000000 : ℝ)^2135 := by
      have hnat : (25016846199356017973 : ℕ)^512*5000000000000000^2135 ≤ 5000807829270027^2135*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016846199356017973 25000000000000000000 5000807829270027 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000807829270027/5000000000000000 : ℝ)) (X := (25016846199356017973/25000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1288541600184667/12500000000000000000 : ℝ) ≤ ((9082347669323399847/9085000000000000000 : ℝ)+2*(140160445647/90850000000000 : ℝ)*(1383/12500 : ℝ))^(2135/512 : ℝ) := by
    rw [show (9082347669323399847/9085000000000000000 : ℝ)+2*(140160445647/90850000000000 : ℝ)*(1383/12500 : ℝ)=(5000247187487439/5000000000000000 : ℝ) by norm_num, show 1+2*(1288541600184667/12500000000000000000 : ℝ)=(6251288541600184667/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16846199356017973/50000000000000000000 : ℝ)+(1288541600184667/12500000000000000000 : ℝ) ≤ ((9082347669323399847/9085000000000000000 : ℝ)+(140160445647/90850000000000 : ℝ)*((7349/50000 : ℝ)+(1383/12500 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (9082347669323399847/9085000000000000000 : ℝ)+(140160445647/90850000000000 : ℝ)*((7349/50000 : ℝ)+(1383/12500 : ℝ))=(5000527508378733/5000000000000000 : ℝ) by norm_num, show 1+(16846199356017973/50000000000000000000 : ℝ)+(1288541600184667/12500000000000000000 : ℝ)=(50022000365756756641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16846199356017973/50000000000000000000 : ℝ) ≤ ((9082347669323399847/9085000000000000000 : ℝ)+2*(140160445647/90850000000000 : ℝ)*(7349/50000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (9082347669323399847/9085000000000000000 : ℝ)+2*(140160445647/90850000000000 : ℝ)*(7349/50000 : ℝ)=(5000807829270027/5000000000000000 : ℝ) by norm_num, show 1+2*(16846199356017973/50000000000000000000 : ℝ)=(25016846199356017973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9082347669323399847/9085000000000000000 : ℝ)*(X 1 0+X 2 0)+(140160445647/90850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (9082347669323399847/9085000000000000000 : ℝ)) (alpha := (140160445647/90850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9082347669323399847/9085000000000000000 : ℝ)*(X 0 1+X 2 1)+(140160445647/90850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (9082347669323399847/9085000000000000000 : ℝ)) (alpha := (140160445647/90850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9082347669323399847/9085000000000000000 : ℝ)*(X 0 2+X 1 2)+(140160445647/90850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (9082347669323399847/9085000000000000000 : ℝ)) (alpha := (140160445647/90850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207104963/1000000000 : ℝ)*X 0 0+(676791799/1250000000 : ℝ)*X 0 1+(2621791083/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349517573/10000000000 : ℝ)*X 1 0+(-539518829/2500000000 : ℝ)*X 1 1+(2621790823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8559227/16000000 : ℝ)*X 2 0+(1310895503/2500000000 : ℝ)*X 2 1+(-2158075761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083696853/2500000000 : ℝ)*X 0 0+(260091193/625000000 : ℝ)*X 0 1+(4514946021/10000000000 : ℝ)*X 0 2+(1083696853/2500000000 : ℝ)*X 1 0+(260091193/625000000 : ℝ)*X 1 1+(4514946021/10000000000 : ℝ)*X 1 2+(1083696853/2500000000 : ℝ)*X 2 0+(260091193/625000000 : ℝ)*X 2 1+(4514946021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2071062511/10000000000 : ℝ)*X 0 0+(2622095953/5000000000 : ℝ)*X 0 1+(169178789/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10611393/20000000 : ℝ)*X 1 0+(-496984103/2500000000 : ℝ)*X 1 1+(5413721253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326424139/2500000000 : ℝ)*X 2 0+(5413721213/10000000000 : ℝ)*X 2 1+(-248492049/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((541851703/1250000000 : ℝ)*X 0 0+(225684139/500000000 : ℝ)*X 0 1+(52034107/125000000 : ℝ)*X 0 2+(541851703/1250000000 : ℝ)*X 1 0+(225684139/500000000 : ℝ)*X 1 1+(52034107/125000000 : ℝ)*X 1 2+(541851703/1250000000 : ℝ)*X 2 0+(225684139/500000000 : ℝ)*X 2 1+(52034107/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4983375076973799502402316409/454250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (271020479/12500000000000 : ℝ)*(base19) + (1740317171/100000000000000 : ℝ)*(base23) + (161069731/100000000000000 : ℝ)*(upper3) + (209250661/100000000000000 : ℝ)*(lower4) + (4342765094972949/100000000000000 : ℝ)*(major0) + (4342765094972949/100000000000000 : ℝ)*(major1) + (4342765094972949/100000000000000 : ℝ)*(major2) + (2928244387226813/50000000000000 : ℝ)*(sp0) + (5856519853239411/100000000000000 : ℝ)*(sp1) + (5856513584907577/100000000000000 : ℝ)*(sp2) + (282898436276011/10000000000000 : ℝ)*(sp3) + (33246949617/100000000000000 : ℝ)*(sp4) + (104627789/1562500000000 : ℝ)*(sp6) + (11720048669/50000000000000 : ℝ)*(sp7) + (353625975357181/12500000000000 : ℝ)*(f.failure) + (1464130505350811/25000000000000 : ℝ)*(f.sum) + (32733070112019/9085000000000000000000000000 : ℝ)*base66 + (4378642750807038803/908500000000000000000000000000000 : ℝ)*base67 + (3048223744260961197/908500000000000000000000000000000 : ℝ)*base70 + (2291988121228538803/908500000000000000000000000000000 : ℝ)*base71 + (295346663867/4542500000000000000000000000 : ℝ)*base74 + (84201224739961197/908500000000000000000000000000000 : ℝ)*base76 + (9468228355229461197/908500000000000000000000000000000 : ℝ)*base78 + (1387820408405961197/908500000000000000000000000000000 : ℝ)*base80 + (12938004328179/9085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2392477/1250000000000000000000 : ℝ)*base89 + (2392477/1250000000000000000000 : ℝ)*base91 + (2392477/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4918612708038741590091043143/454250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466211629/25000000000000 : ℝ)*(base19) + (8432351/400000000000 : ℝ)*(base23) + (26630729/12500000000000 : ℝ)*(upper3) + (39946901/50000000000000 : ℝ)*(lower4) + (229456083/100000000000000 : ℝ)*(upper5) + (4374028840275241/100000000000000 : ℝ)*(major0) + (4374028840275241/100000000000000 : ℝ)*(major1) + (4374028840275241/100000000000000 : ℝ)*(major2) + (37920277071/100000000000000 : ℝ)*(sp1) + (41601869789/100000000000000 : ℝ)*(sp2) + (5898683372731521/100000000000000 : ℝ)*(sp4) + (2949321793803967/50000000000000 : ℝ)*(sp5) + (5898639662773983/100000000000000 : ℝ)*(sp6) + (8904293584019/312500000000 : ℝ)*(sp7) + (8904293584019/312500000000 : ℝ)*(f.failure) + (5898683372731521/100000000000000 : ℝ)*(f.sum) + (745853347711/9085000000000000000000000000 : ℝ)*base66 + (7216941078551011873/908500000000000000000000000000000 : ℝ)*base68 + (3106461520798011873/908500000000000000000000000000000 : ℝ)*base70 + (17679301736355511873/908500000000000000000000000000000 : ℝ)*base72 + (8783456592297/4542500000000000000000000000 : ℝ)*base73 + (4396896701458011873/908500000000000000000000000000000 : ℝ)*base76 + (6484939386395511873/908500000000000000000000000000000 : ℝ)*base78 + (21588473343929511873/908500000000000000000000000000000 : ℝ)*base80 + (28889177298879/9085000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (375423/31250000000000000000 : ℝ)*base89 + (375423/31250000000000000000 : ℝ)*base91 + (375423/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11073/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1311_s7_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-517765227/2500000000 : ℝ)*x 0 + (2707125299/5000000000 : ℝ)*x 1 + (5243658397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517765227/2500000000 : ℝ)^4271 ≤ (1575621781231/12500000000000 : ℝ)^3247 := by
    have hnat : (517765227 : ℕ)^4271*12500000000000^3247 ≤ 1575621781231^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517765227 2500000000 1575621781231 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707125299/5000000000 : ℝ)^4271 ≤ (22308731285927/50000000000000 : ℝ)^3247 := by
    have hnat : (2707125299 : ℕ)^4271*50000000000000^3247 ≤ 22308731285927^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707125299 5000000000 22308731285927 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243658397/10000000000 : ℝ)^4271 ≤ (21388781580221/50000000000000 : ℝ)^3247 := by
    have hnat : (5243658397 : ℕ)^4271*50000000000000^3247 ≤ 21388781580221^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243658397 10000000000 21388781580221 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517765227/2500000000 : ℝ), (2707125299/5000000000 : ℝ), (5243658397/10000000000 : ℝ)] ![(1575621781231/12500000000000 : ℝ), (22308731285927/50000000000000 : ℝ), (21388781580221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517765227/2500000000 : ℝ)|^4271 ≤ (1575621781231/12500000000000 : ℝ)^3247
        have hw : |(-517765227/2500000000 : ℝ)|=(517765227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707125299/5000000000 : ℝ)|^4271 ≤ (22308731285927/50000000000000 : ℝ)^3247
        have hw : |(2707125299/5000000000 : ℝ)|=(2707125299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243658397/10000000000 : ℝ)|^4271 ≤ (21388781580221/50000000000000 : ℝ)^3247
        have hw : |(5243658397/10000000000 : ℝ)|=(5243658397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s7_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069898971/2000000000 : ℝ)*x 0 + (-2158003547/10000000000 : ℝ)*x 1 + (5243658751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069898971/2000000000 : ℝ)^4271 ≤ (43916862768461/100000000000000 : ℝ)^3247 := by
    have hnat : (1069898971 : ℕ)^4271*100000000000000^3247 ≤ 43916862768461^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069898971 2000000000 43916862768461 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158003547/10000000000 : ℝ)^4271 ≤ (266111405201/2000000000000 : ℝ)^3247 := by
    have hnat : (2158003547 : ℕ)^4271*2000000000000^3247 ≤ 266111405201^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158003547 10000000000 266111405201 2000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243658751/10000000000 : ℝ)^4271 ≤ (42777566959117/100000000000000 : ℝ)^3247 := by
    have hnat : (5243658751 : ℕ)^4271*100000000000000^3247 ≤ 42777566959117^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243658751 10000000000 42777566959117 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069898971/2000000000 : ℝ), (-2158003547/10000000000 : ℝ), (5243658751/10000000000 : ℝ)] ![(43916862768461/100000000000000 : ℝ), (266111405201/2000000000000 : ℝ), (42777566959117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069898971/2000000000 : ℝ)|^4271 ≤ (43916862768461/100000000000000 : ℝ)^3247
        have hw : |(1069898971/2000000000 : ℝ)|=(1069898971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2158003547/10000000000 : ℝ)|^4271 ≤ (266111405201/2000000000000 : ℝ)^3247
        have hw : |(-2158003547/10000000000 : ℝ)|=(2158003547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243658751/10000000000 : ℝ)|^4271 ≤ (42777566959117/100000000000000 : ℝ)^3247
        have hw : |(5243658751/10000000000 : ℝ)|=(5243658751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s7_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674747639/5000000000 : ℝ)*x 0 + (655457297/1250000000 : ℝ)*x 1 + (-2158003479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674747639/5000000000 : ℝ)^4271 ≤ (43916867336251/100000000000000 : ℝ)^3247 := by
    have hnat : (2674747639 : ℕ)^4271*100000000000000^3247 ≤ 43916867336251^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674747639 5000000000 43916867336251 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655457297/1250000000 : ℝ)^4271 ≤ (5347195366887/12500000000000 : ℝ)^3247 := by
    have hnat : (655457297 : ℕ)^4271*12500000000000^3247 ≤ 5347195366887^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655457297 1250000000 5347195366887 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158003479/10000000000 : ℝ)^4271 ≤ (166319621357/1250000000000 : ℝ)^3247 := by
    have hnat : (2158003479 : ℕ)^4271*1250000000000^3247 ≤ 166319621357^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158003479 10000000000 166319621357 1250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674747639/5000000000 : ℝ), (655457297/1250000000 : ℝ), (-2158003479/10000000000 : ℝ)] ![(43916867336251/100000000000000 : ℝ), (5347195366887/12500000000000 : ℝ), (166319621357/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674747639/5000000000 : ℝ)|^4271 ≤ (43916867336251/100000000000000 : ℝ)^3247
        have hw : |(2674747639/5000000000 : ℝ)|=(2674747639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655457297/1250000000 : ℝ)|^4271 ≤ (5347195366887/12500000000000 : ℝ)^3247
        have hw : |(655457297/1250000000 : ℝ)|=(655457297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2158003479/10000000000 : ℝ)|^4271 ≤ (166319621357/1250000000000 : ℝ)^3247
        have hw : |(-2158003479/10000000000 : ℝ)|=(2158003479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s7_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4334793219/10000000000 : ℝ)*x 0 + (260101571/625000000 : ℝ)*x 1 + (1128694613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334793219/10000000000 : ℝ)^4271 ≤ (2081420543841/6250000000000 : ℝ)^3247 := by
    have hnat : (4334793219 : ℕ)^4271*6250000000000^3247 ≤ 2081420543841^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334793219 10000000000 2081420543841 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260101571/625000000 : ℝ)^4271 ≤ (31563900546631/100000000000000 : ℝ)^3247 := by
    have hnat : (260101571 : ℕ)^4271*100000000000000^3247 ≤ 31563900546631^3247*625000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260101571 625000000 31563900546631 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128694613/2500000000 : ℝ)^4271 ≤ (17566685366663/50000000000000 : ℝ)^3247 := by
    have hnat : (1128694613 : ℕ)^4271*50000000000000^3247 ≤ 17566685366663^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128694613 2500000000 17566685366663 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334793219/10000000000 : ℝ), (260101571/625000000 : ℝ), (1128694613/2500000000 : ℝ)] ![(2081420543841/6250000000000 : ℝ), (31563900546631/100000000000000 : ℝ), (17566685366663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334793219/10000000000 : ℝ)|^4271 ≤ (2081420543841/6250000000000 : ℝ)^3247
        have hw : |(4334793219/10000000000 : ℝ)|=(4334793219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260101571/625000000 : ℝ)|^4271 ≤ (31563900546631/100000000000000 : ℝ)^3247
        have hw : |(260101571/625000000 : ℝ)|=(260101571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128694613/2500000000 : ℝ)|^4271 ≤ (17566685366663/50000000000000 : ℝ)^3247
        have hw : |(1128694613/2500000000 : ℝ)|=(1128694613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s7_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071073333/10000000000 : ℝ)*x 0 + (209770697/400000000 : ℝ)*x 1 + (541363849/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071073333/10000000000 : ℝ)^4271 ≤ (3151268430023/25000000000000 : ℝ)^3247 := by
    have hnat : (2071073333 : ℕ)^4271*25000000000000^3247 ≤ 3151268430023^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071073333 10000000000 3151268430023 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209770697/400000000 : ℝ)^4271 ≤ (21392049295059/50000000000000 : ℝ)^3247 := by
    have hnat : (209770697 : ℕ)^4271*50000000000000^3247 ≤ 21392049295059^3247*400000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209770697 400000000 21392049295059 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541363849/1000000000 : ℝ)^4271 ≤ (5576353459499/12500000000000 : ℝ)^3247 := by
    have hnat : (541363849 : ℕ)^4271*12500000000000^3247 ≤ 5576353459499^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541363849 1000000000 5576353459499 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071073333/10000000000 : ℝ), (209770697/400000000 : ℝ), (541363849/1000000000 : ℝ)] ![(3151268430023/25000000000000 : ℝ), (21392049295059/50000000000000 : ℝ), (5576353459499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071073333/10000000000 : ℝ)|^4271 ≤ (3151268430023/25000000000000 : ℝ)^3247
        have hw : |(-2071073333/10000000000 : ℝ)|=(2071073333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209770697/400000000 : ℝ)|^4271 ≤ (21392049295059/50000000000000 : ℝ)^3247
        have hw : |(209770697/400000000 : ℝ)|=(209770697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541363849/1000000000 : ℝ)|^4271 ≤ (5576353459499/12500000000000 : ℝ)^3247
        have hw : |(541363849/1000000000 : ℝ)|=(541363849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s7_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652858027/5000000000 : ℝ)*x 0 + (-994011637/5000000000 : ℝ)*x 1 + (1353409623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652858027/5000000000 : ℝ)^4271 ≤ (21722362993911/50000000000000 : ℝ)^3247 := by
    have hnat : (2652858027 : ℕ)^4271*50000000000000^3247 ≤ 21722362993911^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652858027 5000000000 21722362993911 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994011637/5000000000 : ℝ)^4271 ≤ (2388889260353/20000000000000 : ℝ)^3247 := by
    have hnat : (994011637 : ℕ)^4271*20000000000000^3247 ≤ 2388889260353^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994011637 5000000000 2388889260353 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353409623/2500000000 : ℝ)^4271 ≤ (4461082769767/10000000000000 : ℝ)^3247 := by
    have hnat : (1353409623 : ℕ)^4271*10000000000000^3247 ≤ 4461082769767^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353409623 2500000000 4461082769767 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652858027/5000000000 : ℝ), (-994011637/5000000000 : ℝ), (1353409623/2500000000 : ℝ)] ![(21722362993911/50000000000000 : ℝ), (2388889260353/20000000000000 : ℝ), (4461082769767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652858027/5000000000 : ℝ)|^4271 ≤ (21722362993911/50000000000000 : ℝ)^3247
        have hw : |(2652858027/5000000000 : ℝ)|=(2652858027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994011637/5000000000 : ℝ)|^4271 ≤ (2388889260353/20000000000000 : ℝ)^3247
        have hw : |(-994011637/5000000000 : ℝ)|=(994011637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353409623/2500000000 : ℝ)|^4271 ≤ (4461082769767/10000000000000 : ℝ)^3247
        have hw : |(1353409623/2500000000 : ℝ)|=(1353409623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s7_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326429013/2500000000 : ℝ)*x 0 + (1353409623/2500000000 : ℝ)*x 1 + (-1988023277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326429013/2500000000 : ℝ)^4271 ≤ (1086118149157/2500000000000 : ℝ)^3247 := by
    have hnat : (1326429013 : ℕ)^4271*2500000000000^3247 ≤ 1086118149157^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326429013 2500000000 1086118149157 2500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353409623/2500000000 : ℝ)^4271 ≤ (4461082769767/10000000000000 : ℝ)^3247 := by
    have hnat : (1353409623 : ℕ)^4271*10000000000000^3247 ≤ 4461082769767^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353409623 2500000000 4461082769767 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988023277/10000000000 : ℝ)^4271 ≤ (5972223162737/50000000000000 : ℝ)^3247 := by
    have hnat : (1988023277 : ℕ)^4271*50000000000000^3247 ≤ 5972223162737^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988023277 10000000000 5972223162737 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326429013/2500000000 : ℝ), (1353409623/2500000000 : ℝ), (-1988023277/10000000000 : ℝ)] ![(1086118149157/2500000000000 : ℝ), (4461082769767/10000000000000 : ℝ), (5972223162737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326429013/2500000000 : ℝ)|^4271 ≤ (1086118149157/2500000000000 : ℝ)^3247
        have hw : |(1326429013/2500000000 : ℝ)|=(1326429013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353409623/2500000000 : ℝ)|^4271 ≤ (4461082769767/10000000000000 : ℝ)^3247
        have hw : |(1353409623/2500000000 : ℝ)|=(1353409623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988023277/10000000000 : ℝ)|^4271 ≤ (5972223162737/50000000000000 : ℝ)^3247
        have hw : |(-1988023277/10000000000 : ℝ)|=(1988023277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s7_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4334819241/10000000000 : ℝ)*x 0 + (564189783/1250000000 : ℝ)*x 1 + (2081445819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334819241/10000000000 : ℝ)^4271 ≤ (33302991667577/100000000000000 : ℝ)^3247 := by
    have hnat : (4334819241 : ℕ)^4271*100000000000000^3247 ≤ 33302991667577^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334819241 10000000000 33302991667577 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564189783/1250000000 : ℝ)^4271 ≤ (35120472005437/100000000000000 : ℝ)^3247 := by
    have hnat : (564189783 : ℕ)^4271*100000000000000^3247 ≤ 35120472005437^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564189783 1250000000 35120472005437 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081445819/5000000000 : ℝ)^4271 ≤ (31576536316567/100000000000000 : ℝ)^3247 := by
    have hnat : (2081445819 : ℕ)^4271*100000000000000^3247 ≤ 31576536316567^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081445819 5000000000 31576536316567 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334819241/10000000000 : ℝ), (564189783/1250000000 : ℝ), (2081445819/5000000000 : ℝ)] ![(33302991667577/100000000000000 : ℝ), (35120472005437/100000000000000 : ℝ), (31576536316567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334819241/10000000000 : ℝ)|^4271 ≤ (33302991667577/100000000000000 : ℝ)^3247
        have hw : |(4334819241/10000000000 : ℝ)|=(4334819241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564189783/1250000000 : ℝ)|^4271 ≤ (35120472005437/100000000000000 : ℝ)^3247
        have hw : |(564189783/1250000000 : ℝ)|=(564189783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081445819/5000000000 : ℝ)|^4271 ≤ (31576536316567/100000000000000 : ℝ)^3247
        have hw : |(2081445819/5000000000 : ℝ)|=(2081445819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11073/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (443/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7343/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11073/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11073/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11073/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11073/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11073/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11073/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11073/100000 : ℝ) ^ (2135/512 : ℝ) ≤ (323229499021663/3125000000000000000 : ℝ) := by
    have hpowers : (11073/100000 : ℝ)^2135 ≤ (323229499021663/3125000000000000000 : ℝ)^512 := by
      have hnat : (11073 : ℕ)^2135*3125000000000000000^512 ≤ 323229499021663^512*100000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11073 100000 323229499021663 3125000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11073/100000 : ℝ)) (X := (323229499021663/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (459/3125 : ℝ) ^ (2135/512 : ℝ) ≤ (8399228531879787/25000000000000000000 : ℝ) := by
    have hpowers : (459/3125 : ℝ)^2135 ≤ (8399228531879787/25000000000000000000 : ℝ)^512 := by
      have hnat : (459 : ℕ)^2135*25000000000000000000^512 ≤ 8399228531879787^512*3125^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 3125 8399228531879787 25000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/3125 : ℝ)) (X := (8399228531879787/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562823229499021663/1562500000000000000 : ℝ) ≤ (2000099210787087/2000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (1562823229499021663/1562500000000000000 : ℝ)^512 ≤ (2000099210787087/2000000000000000 : ℝ)^2135 := by
      have hnat : (1562823229499021663 : ℕ)^512*2000000000000000^2135 ≤ 2000099210787087^2135*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562823229499021663 1562500000000000000 2000099210787087 2000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000099210787087/2000000000000000 : ℝ)) (X := (1562823229499021663/1562500000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010985064524053091/25000000000000000000 : ℝ) ≤ (5000526783506503/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (25010985064524053091/25000000000000000000 : ℝ)^512 ≤ (5000526783506503/5000000000000000 : ℝ)^2135 := by
      have hnat : (25010985064524053091 : ℕ)^512*5000000000000000^2135 ≤ 5000526783506503^2135*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010985064524053091 25000000000000000000 5000526783506503 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000526783506503/5000000000000000 : ℝ)) (X := (25010985064524053091/25000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508399228531879787/12500000000000000000 : ℝ) ≤ (10001611080090577/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (12508399228531879787/12500000000000000000 : ℝ)^512 ≤ (10001611080090577/10000000000000000 : ℝ)^2135 := by
      have hnat : (12508399228531879787 : ℕ)^512*10000000000000000^2135 ≤ 10001611080090577^2135*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508399228531879787 12500000000000000000 10001611080090577 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001611080090577/10000000000000000 : ℝ)) (X := (12508399228531879787/12500000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(323229499021663/3125000000000000000 : ℝ) ≤ ((12046482183453570053/12050000000000000000 : ℝ)+2*(557513077571/361500000000000 : ℝ)*(11073/100000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (12046482183453570053/12050000000000000000 : ℝ)+2*(557513077571/361500000000000 : ℝ)*(11073/100000 : ℝ)=(2000099210787087/2000000000000000 : ℝ) by norm_num, show 1+2*(323229499021663/3125000000000000000 : ℝ)=(1562823229499021663/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8399228531879787/25000000000000000000 : ℝ)+(323229499021663/3125000000000000000 : ℝ) ≤ ((12046482183453570053/12050000000000000000 : ℝ)+(557513077571/361500000000000 : ℝ)*((459/3125 : ℝ)+(11073/100000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (12046482183453570053/12050000000000000000 : ℝ)+(557513077571/361500000000000 : ℝ)*((459/3125 : ℝ)+(11073/100000 : ℝ))=(5000526783506503/5000000000000000 : ℝ) by norm_num, show 1+(8399228531879787/25000000000000000000 : ℝ)+(323229499021663/3125000000000000000 : ℝ)=(25010985064524053091/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8399228531879787/25000000000000000000 : ℝ) ≤ ((12046482183453570053/12050000000000000000 : ℝ)+2*(557513077571/361500000000000 : ℝ)*(459/3125 : ℝ))^(2135/512 : ℝ) := by
    rw [show (12046482183453570053/12050000000000000000 : ℝ)+2*(557513077571/361500000000000 : ℝ)*(459/3125 : ℝ)=(10001611080090577/10000000000000000 : ℝ) by norm_num, show 1+2*(8399228531879787/25000000000000000000 : ℝ)=(12508399228531879787/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12046482183453570053/12050000000000000000 : ℝ)*(X 1 0+X 2 0)+(557513077571/361500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (11073/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (12046482183453570053/12050000000000000000 : ℝ)) (alpha := (557513077571/361500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12046482183453570053/12050000000000000000 : ℝ)*(X 0 1+X 2 1)+(557513077571/361500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (11073/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (12046482183453570053/12050000000000000000 : ℝ)) (alpha := (557513077571/361500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12046482183453570053/12050000000000000000 : ℝ)*(X 0 2+X 1 2)+(557513077571/361500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (11073/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (12046482183453570053/12050000000000000000 : ℝ)) (alpha := (557513077571/361500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-517765227/2500000000 : ℝ)*X 0 0+(2707125299/5000000000 : ℝ)*X 0 1+(5243658397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069898971/2000000000 : ℝ)*X 1 0+(-2158003547/10000000000 : ℝ)*X 1 1+(5243658751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674747639/5000000000 : ℝ)*X 2 0+(655457297/1250000000 : ℝ)*X 2 1+(-2158003479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4334793219/10000000000 : ℝ)*X 0 0+(260101571/625000000 : ℝ)*X 0 1+(1128694613/2500000000 : ℝ)*X 0 2+(4334793219/10000000000 : ℝ)*X 1 0+(260101571/625000000 : ℝ)*X 1 1+(1128694613/2500000000 : ℝ)*X 1 2+(4334793219/10000000000 : ℝ)*X 2 0+(260101571/625000000 : ℝ)*X 2 1+(1128694613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2071073333/10000000000 : ℝ)*X 0 0+(209770697/400000000 : ℝ)*X 0 1+(541363849/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652858027/5000000000 : ℝ)*X 1 0+(-994011637/5000000000 : ℝ)*X 1 1+(1353409623/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326429013/2500000000 : ℝ)*X 2 0+(1353409623/2500000000 : ℝ)*X 2 1+(-1988023277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334819241/10000000000 : ℝ)*X 0 0+(564189783/1250000000 : ℝ)*X 0 1+(2081445819/5000000000 : ℝ)*X 0 2+(4334819241/10000000000 : ℝ)*X 1 0+(564189783/1250000000 : ℝ)*X 1 1+(2081445819/5000000000 : ℝ)*X 1 2+(4334819241/10000000000 : ℝ)*X 2 0+(564189783/1250000000 : ℝ)*X 2 1+(2081445819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1348192246429648563222162679/150625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (368422789/50000000000000 : ℝ)*(base19) + (231447923/20000000000000 : ℝ)*(base23) + (55861783/50000000000000 : ℝ)*(upper3) + (11535981/50000000000000 : ℝ)*(upper4) + (245469247/100000000000000 : ℝ)*(upper5) + (1086702329487427/25000000000000 : ℝ)*(major0) + (1086702329487427/25000000000000 : ℝ)*(major1) + (1086702329487427/25000000000000 : ℝ)*(major2) + (5861949752578661/100000000000000 : ℝ)*(sp0) + (586197526935363/10000000000000 : ℝ)*(sp1) + (5861974848959593/100000000000000 : ℝ)*(sp2) + (707909216141381/25000000000000 : ℝ)*(sp3) + (6563405137/25000000000000 : ℝ)*(sp4) + (683347443/12500000000000 : ℝ)*(sp7) + (707910582836267/25000000000000 : ℝ)*(f.failure) + (732747000774901/12500000000000 : ℝ)*(f.sum) + (2353384015771/2259375000000000000000000000 : ℝ)*base65 + (15321847531004129107/903750000000000000000000000000000 : ℝ)*base68 + (15482678699350379107/903750000000000000000000000000000 : ℝ)*base70 + (6286896514499129107/903750000000000000000000000000000 : ℝ)*base72 + (42720367927991/9037500000000000000000000000 : ℝ)*base74 + (11325209262524129107/903750000000000000000000000000000 : ℝ)*base76 + (9093698378864129107/903750000000000000000000000000000 : ℝ)*base78 + (5535737777466629107/903750000000000000000000000000000 : ℝ)*base80 + (26366865244793/18075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (17359339/2500000000000000000000 : ℝ)*base89 + (17359339/2500000000000000000000 : ℝ)*base91 + (17359339/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5062273509639957548612529433/602500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (740009767/50000000000000 : ℝ)*(base19) + (802819399/50000000000000 : ℝ)*(base23) + (507801299/100000000000000 : ℝ)*(lower1) + (86085001/50000000000000 : ℝ)*(upper3) + (58155107/100000000000000 : ℝ)*(lower4) + (171280117/100000000000000 : ℝ)*(upper5) + (4378093544898487/100000000000000 : ℝ)*(major0) + (4378093544898487/100000000000000 : ℝ)*(major1) + (4378093544898487/100000000000000 : ℝ)*(major2) + (110506057/5000000000000 : ℝ)*(sp2) + (2952082495996119/50000000000000 : ℝ)*(sp4) + (5904163511972703/100000000000000 : ℝ)*(sp5) + (5904161176232299/100000000000000 : ℝ)*(sp6) + (142601090886713/5000000000000 : ℝ)*(sp7) + (142601090886713/5000000000000 : ℝ)*(f.failure) + (2952082495996119/50000000000000 : ℝ)*(f.sum) + (64162610171627/18075000000000000000000000000 : ℝ)*base65 + (209959343810457670567/3615000000000000000000000000000000 : ℝ)*base68 + (44907433267107670567/3615000000000000000000000000000000 : ℝ)*base70 + (39711999088137670567/3615000000000000000000000000000000 : ℝ)*base72 + (76528266415273/18075000000000000000000000000 : ℝ)*base74 + (185020870362452329433/3615000000000000000000000000000000 : ℝ)*base75 + (5030652507327670567/3615000000000000000000000000000000 : ℝ)*base78 + (51985455517772329433/3615000000000000000000000000000000 : ℝ)*base79 + (56028360505349/9037500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3963321/500000000000000000000 : ℝ)*base89 + (3963321/500000000000000000000 : ℝ)*base91 + (3963321/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11073/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1311_s8_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349491059/10000000000 : ℝ)*x 0 + (1310918661/2500000000 : ℝ)*x 1 + (-539496893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349491059/10000000000 : ℝ)^4271 ≤ (21958410888567/50000000000000 : ℝ)^3247 := by
    have hnat : (5349491059 : ℕ)^4271*50000000000000^3247 ≤ 21958410888567^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349491059 10000000000 21958410888567 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310918661/2500000000 : ℝ)^4271 ≤ (42777737502563/100000000000000 : ℝ)^3247 := by
    have hnat : (1310918661 : ℕ)^4271*100000000000000^3247 ≤ 42777737502563^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310918661 2500000000 42777737502563 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539496893/2500000000 : ℝ)^4271 ≤ (6652720350317/50000000000000 : ℝ)^3247 := by
    have hnat : (539496893 : ℕ)^4271*50000000000000^3247 ≤ 6652720350317^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539496893 2500000000 6652720350317 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349491059/10000000000 : ℝ), (1310918661/2500000000 : ℝ), (-539496893/2500000000 : ℝ)] ![(21958410888567/50000000000000 : ℝ), (42777737502563/100000000000000 : ℝ), (6652720350317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349491059/10000000000 : ℝ)|^4271 ≤ (21958410888567/50000000000000 : ℝ)^3247
        have hw : |(5349491059/10000000000 : ℝ)|=(5349491059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310918661/2500000000 : ℝ)|^4271 ≤ (42777737502563/100000000000000 : ℝ)^3247
        have hw : |(1310918661/2500000000 : ℝ)|=(1310918661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539496893/2500000000 : ℝ)|^4271 ≤ (6652720350317/50000000000000 : ℝ)^3247
        have hw : |(-539496893/2500000000 : ℝ)|=(539496893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s8_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-517768729/2500000000 : ℝ)*x 0 + (1311070863/2500000000 : ℝ)*x 1 + (2706810727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517768729/2500000000 : ℝ)^4271 ≤ (2521017278611/20000000000000 : ℝ)^3247 := by
    have hnat : (517768729 : ℕ)^4271*20000000000000^3247 ≤ 2521017278611^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517768729 2500000000 2521017278611 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311070863/2500000000 : ℝ)^4271 ≤ (42784270577777/100000000000000 : ℝ)^3247 := by
    have hnat : (1311070863 : ℕ)^4271*100000000000000^3247 ≤ 42784270577777^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311070863 2500000000 42784270577777 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706810727/5000000000 : ℝ)^4271 ≤ (11152660754753/25000000000000 : ℝ)^3247 := by
    have hnat : (2706810727 : ℕ)^4271*25000000000000^3247 ≤ 11152660754753^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706810727 5000000000 11152660754753 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517768729/2500000000 : ℝ), (1311070863/2500000000 : ℝ), (2706810727/5000000000 : ℝ)] ![(2521017278611/20000000000000 : ℝ), (42784270577777/100000000000000 : ℝ), (11152660754753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517768729/2500000000 : ℝ)|^4271 ≤ (2521017278611/20000000000000 : ℝ)^3247
        have hw : |(-517768729/2500000000 : ℝ)|=(517768729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311070863/2500000000 : ℝ)|^4271 ≤ (42784270577777/100000000000000 : ℝ)^3247
        have hw : |(1311070863/2500000000 : ℝ)|=(1311070863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706810727/5000000000 : ℝ)|^4271 ≤ (11152660754753/25000000000000 : ℝ)^3247
        have hw : |(2706810727/5000000000 : ℝ)|=(2706810727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s8_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652860121/5000000000 : ℝ)*x 0 + (-248505113/1250000000 : ℝ)*x 1 + (1353405369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652860121/5000000000 : ℝ)^4271 ≤ (21722385547573/50000000000000 : ℝ)^3247 := by
    have hnat : (2652860121 : ℕ)^4271*50000000000000^3247 ≤ 21722385547573^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652860121 5000000000 21722385547573 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248505113/1250000000 : ℝ)^4271 ≤ (2986146407951/25000000000000 : ℝ)^3247 := by
    have hnat : (248505113 : ℕ)^4271*25000000000000^3247 ≤ 2986146407951^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248505113 1250000000 2986146407951 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353405369/2500000000 : ℝ)^4271 ≤ (22305321628737/50000000000000 : ℝ)^3247 := by
    have hnat : (1353405369 : ℕ)^4271*50000000000000^3247 ≤ 22305321628737^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353405369 2500000000 22305321628737 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652860121/5000000000 : ℝ), (-248505113/1250000000 : ℝ), (1353405369/2500000000 : ℝ)] ![(21722385547573/50000000000000 : ℝ), (2986146407951/25000000000000 : ℝ), (22305321628737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652860121/5000000000 : ℝ)|^4271 ≤ (21722385547573/50000000000000 : ℝ)^3247
        have hw : |(2652860121/5000000000 : ℝ)|=(2652860121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248505113/1250000000 : ℝ)|^4271 ≤ (2986146407951/25000000000000 : ℝ)^3247
        have hw : |(-248505113/1250000000 : ℝ)|=(248505113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353405369/2500000000 : ℝ)|^4271 ≤ (22305321628737/50000000000000 : ℝ)^3247
        have hw : |(1353405369/2500000000 : ℝ)|=(1353405369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s8_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663215037/1250000000 : ℝ)*x 0 + (5413621451/10000000000 : ℝ)*x 1 + (-397608173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663215037/1250000000 : ℝ)^4271 ≤ (43444771676759/100000000000000 : ℝ)^3247 := by
    have hnat : (663215037 : ℕ)^4271*100000000000000^3247 ≤ 43444771676759^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663215037 1250000000 43444771676759 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413621451/10000000000 : ℝ)^4271 ≤ (22305321493247/50000000000000 : ℝ)^3247 := by
    have hnat : (5413621451 : ℕ)^4271*50000000000000^3247 ≤ 22305321493247^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413621451 10000000000 22305321493247 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397608173/2000000000 : ℝ)^4271 ≤ (11944585323587/100000000000000 : ℝ)^3247 := by
    have hnat : (397608173 : ℕ)^4271*100000000000000^3247 ≤ 11944585323587^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397608173 2000000000 11944585323587 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663215037/1250000000 : ℝ), (5413621451/10000000000 : ℝ), (-397608173/2000000000 : ℝ)] ![(43444771676759/100000000000000 : ℝ), (22305321493247/50000000000000 : ℝ), (11944585323587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663215037/1250000000 : ℝ)|^4271 ≤ (43444771676759/100000000000000 : ℝ)^3247
        have hw : |(663215037/1250000000 : ℝ)|=(663215037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413621451/10000000000 : ℝ)|^4271 ≤ (22305321493247/50000000000000 : ℝ)^3247
        have hw : |(5413621451/10000000000 : ℝ)|=(5413621451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397608173/2000000000 : ℝ)|^4271 ≤ (11944585323587/100000000000000 : ℝ)^3247
        have hw : |(-397608173/2000000000 : ℝ)|=(397608173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s8_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4334820399/10000000000 : ℝ)*x 0 + (564185487/1250000000 : ℝ)*x 1 + (4162925721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334820399/10000000000 : ℝ)^4271 ≤ (33303003369793/100000000000000 : ℝ)^3247 := by
    have hnat : (4334820399 : ℕ)^4271*100000000000000^3247 ≤ 33303003369793^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334820399 10000000000 33303003369793 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564185487/1250000000 : ℝ)^4271 ≤ (17560060122837/50000000000000 : ℝ)^3247 := by
    have hnat : (564185487 : ℕ)^4271*50000000000000^3247 ≤ 17560060122837^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564185487 1250000000 17560060122837 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162925721/10000000000 : ℝ)^4271 ≤ (31576876376169/100000000000000 : ℝ)^3247 := by
    have hnat : (4162925721 : ℕ)^4271*100000000000000^3247 ≤ 31576876376169^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162925721 10000000000 31576876376169 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334820399/10000000000 : ℝ), (564185487/1250000000 : ℝ), (4162925721/10000000000 : ℝ)] ![(33303003369793/100000000000000 : ℝ), (17560060122837/50000000000000 : ℝ), (31576876376169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334820399/10000000000 : ℝ)|^4271 ≤ (33303003369793/100000000000000 : ℝ)^3247
        have hw : |(4334820399/10000000000 : ℝ)|=(4334820399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564185487/1250000000 : ℝ)|^4271 ≤ (17560060122837/50000000000000 : ℝ)^3247
        have hw : |(564185487/1250000000 : ℝ)|=(564185487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162925721/10000000000 : ℝ)|^4271 ≤ (31576876376169/100000000000000 : ℝ)^3247
        have hw : |(4162925721/10000000000 : ℝ)|=(4162925721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (443/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2937/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (443/4000 : ℝ) ^ (2135/512 : ℝ) ≤ (646946030523153/6250000000000000000 : ℝ) := by
    have hpowers : (443/4000 : ℝ)^2135 ≤ (646946030523153/6250000000000000000 : ℝ)^512 := by
      have hnat : (443 : ℕ)^2135*6250000000000000000^512 ≤ 646946030523153^512*4000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        443 4000 646946030523153 6250000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (443/4000 : ℝ)) (X := (646946030523153/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7343/50000 : ℝ) ^ (2135/512 : ℝ) ≤ (33577841922330461/100000000000000000000 : ℝ) := by
    have hpowers : (7343/50000 : ℝ)^2135 ≤ (33577841922330461/100000000000000000000 : ℝ)^512 := by
      have hnat : (7343 : ℕ)^2135*100000000000000000000^512 ≤ 33577841922330461^512*50000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7343 50000 33577841922330461 100000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7343/50000 : ℝ)) (X := (33577841922330461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125646946030523153/3125000000000000000 : ℝ) ≤ (5000248213812801/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (3125646946030523153/3125000000000000000 : ℝ)^512 ≤ (5000248213812801/5000000000000000 : ℝ)^2135 := by
      have hnat : (3125646946030523153 : ℕ)^512*5000000000000000^2135 ≤ 5000248213812801^2135*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125646946030523153 3125000000000000000 5000248213812801 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000248213812801/5000000000000000 : ℝ)) (X := (3125646946030523153/3125000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043928978410700909/100000000000000000000 : ℝ) ≤ (10001053296602191/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (100043928978410700909/100000000000000000000 : ℝ)^512 ≤ (10001053296602191/10000000000000000 : ℝ)^2135 := by
      have hnat : (100043928978410700909 : ℕ)^512*10000000000000000^2135 ≤ 10001053296602191^2135*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043928978410700909 100000000000000000000 10001053296602191 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001053296602191/10000000000000000 : ℝ)) (X := (100043928978410700909/100000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033577841922330461/50000000000000000000 : ℝ) ≤ (500080508278939/500000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50033577841922330461/50000000000000000000 : ℝ)^512 ≤ (500080508278939/500000000000000 : ℝ)^2135 := by
      have hnat : (50033577841922330461 : ℕ)^512*500000000000000^2135 ≤ 500080508278939^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033577841922330461 50000000000000000000 500080508278939 500000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500080508278939/500000000000000 : ℝ)) (X := (50033577841922330461/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(646946030523153/6250000000000000000 : ℝ) ≤ ((4512432244040575309/4513750000000000000 : ℝ)+2*(556868976589/361100000000000 : ℝ)*(443/4000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (4512432244040575309/4513750000000000000 : ℝ)+2*(556868976589/361100000000000 : ℝ)*(443/4000 : ℝ)=(5000248213812801/5000000000000000 : ℝ) by norm_num, show 1+2*(646946030523153/6250000000000000000 : ℝ)=(3125646946030523153/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33577841922330461/100000000000000000000 : ℝ)+(646946030523153/6250000000000000000 : ℝ) ≤ ((4512432244040575309/4513750000000000000 : ℝ)+(556868976589/361100000000000 : ℝ)*((7343/50000 : ℝ)+(443/4000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (4512432244040575309/4513750000000000000 : ℝ)+(556868976589/361100000000000 : ℝ)*((7343/50000 : ℝ)+(443/4000 : ℝ))=(10001053296602191/10000000000000000 : ℝ) by norm_num, show 1+(33577841922330461/100000000000000000000 : ℝ)+(646946030523153/6250000000000000000 : ℝ)=(100043928978410700909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33577841922330461/100000000000000000000 : ℝ) ≤ ((4512432244040575309/4513750000000000000 : ℝ)+2*(556868976589/361100000000000 : ℝ)*(7343/50000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (4512432244040575309/4513750000000000000 : ℝ)+2*(556868976589/361100000000000 : ℝ)*(7343/50000 : ℝ)=(500080508278939/500000000000000 : ℝ) by norm_num, show 1+2*(33577841922330461/100000000000000000000 : ℝ)=(50033577841922330461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4512432244040575309/4513750000000000000 : ℝ)*(X 1 0+X 2 0)+(556868976589/361100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4512432244040575309/4513750000000000000 : ℝ)) (alpha := (556868976589/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4512432244040575309/4513750000000000000 : ℝ)*(X 0 1+X 2 1)+(556868976589/361100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4512432244040575309/4513750000000000000 : ℝ)) (alpha := (556868976589/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4512432244040575309/4513750000000000000 : ℝ)*(X 0 2+X 1 2)+(556868976589/361100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4512432244040575309/4513750000000000000 : ℝ)) (alpha := (556868976589/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5349491059/10000000000 : ℝ)*X 2 0+(1310918661/2500000000 : ℝ)*X 2 1+(-539496893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-517768729/2500000000 : ℝ)*X 0 0+(1311070863/2500000000 : ℝ)*X 0 1+(2706810727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2652860121/5000000000 : ℝ)*X 1 0+(-248505113/1250000000 : ℝ)*X 1 1+(1353405369/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((663215037/1250000000 : ℝ)*X 2 0+(5413621451/10000000000 : ℝ)*X 2 1+(-397608173/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4334820399/10000000000 : ℝ)*X 0 0+(564185487/1250000000 : ℝ)*X 0 1+(4162925721/10000000000 : ℝ)*X 0 2+(4334820399/10000000000 : ℝ)*X 1 0+(564185487/1250000000 : ℝ)*X 1 1+(4162925721/10000000000 : ℝ)*X 1 2+(4334820399/10000000000 : ℝ)*X 2 0+(564185487/1250000000 : ℝ)*X 2 1+(4162925721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64885230627178141823286057/22568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75263239/100000000000000 : ℝ)*(base19) + (157456247/50000000000000 : ℝ)*(base23) + (2347263/10000000000000 : ℝ)*(lower1) + (1502357/6250000000000 : ℝ)*(upper3) + (75507539/100000000000000 : ℝ)*(lower4) + (719871/2500000000000 : ℝ)*(upper5) + (437896975054691/10000000000000 : ℝ)*(major0) + (437896975054691/10000000000000 : ℝ)*(major1) + (437896975054691/10000000000000 : ℝ)*(major2) + (2256618387/50000000000000 : ℝ)*(sp0) + (11533880470337/195312500000 : ℝ)*(sp1) + (1181069345109861/20000000000000 : ℝ)*(sp2) + (236213678906531/4000000000000 : ℝ)*(sp3) + (1426296302223907/50000000000000 : ℝ)*(sp4) + (1426296302223907/50000000000000 : ℝ)*(f.failure) + (11533880470337/195312500000 : ℝ)*(f.sum) + (1684598012281/225687500000000000000000000 : ℝ)*base65 + (2004290922667687981/45137500000000000000000000000000 : ℝ)*base68 + (509364801302912981/45137500000000000000000000000000 : ℝ)*base70 + (305879532102262019/45137500000000000000000000000000 : ℝ)*base71 + (9340347231867/1805500000000000000000000000 : ℝ)*base73 + (3435013768176537019/45137500000000000000000000000000 : ℝ)*base75 + (95699834590437981/45137500000000000000000000000000 : ℝ)*base78 + (680807451034225481/45137500000000000000000000000000 : ℝ)*base80 + (3996698490803/3611000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (43125219/5000000000000000000000 : ℝ)*base89 + (43125219/5000000000000000000000 : ℝ)*base91 + (43125219/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1311_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1311_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1311_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1311_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
