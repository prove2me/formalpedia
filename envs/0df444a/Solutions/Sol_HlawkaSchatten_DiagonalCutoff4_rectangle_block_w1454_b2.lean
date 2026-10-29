-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:00:24.092992+00:00
-- url     : https://prove2.me/submissions/518c8c9a-d999-4097-a946-ce6a8c6650d5

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
theorem support_rectangle_w1454_s6_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-121939029/625000000 : ℝ)*x 0 + (5406935657/10000000000 : ℝ)*x 1 + (1311858349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121939029/625000000 : ℝ)^2207 ≤ (11909019198209/100000000000000 : ℝ)^1695 := by
    have hnat : (121939029 : ℕ)^2207*100000000000000^1695 ≤ 11909019198209^1695*625000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121939029 625000000 11909019198209 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406935657/10000000000 : ℝ)^2207 ≤ (11226002701069/25000000000000 : ℝ)^1695 := by
    have hnat : (5406935657 : ℕ)^2207*25000000000000^1695 ≤ 11226002701069^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406935657 10000000000 11226002701069 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311858349/2500000000 : ℝ)^2207 ≤ (43186969974889/100000000000000 : ℝ)^1695 := by
    have hnat : (1311858349 : ℕ)^2207*100000000000000^1695 ≤ 43186969974889^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311858349 2500000000 43186969974889 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121939029/625000000 : ℝ), (5406935657/10000000000 : ℝ), (1311858349/2500000000 : ℝ)] ![(11909019198209/100000000000000 : ℝ), (11226002701069/25000000000000 : ℝ), (43186969974889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121939029/625000000 : ℝ)|^2207 ≤ (11909019198209/100000000000000 : ℝ)^1695
        have hw : |(-121939029/625000000 : ℝ)|=(121939029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406935657/10000000000 : ℝ)|^2207 ≤ (11226002701069/25000000000000 : ℝ)^1695
        have hw : |(5406935657/10000000000 : ℝ)|=(5406935657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311858349/2500000000 : ℝ)|^2207 ≤ (43186969974889/100000000000000 : ℝ)^1695
        have hw : |(1311858349/2500000000 : ℝ)|=(1311858349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s6_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673395419/5000000000 : ℝ)*x 0 + (-1016106047/5000000000 : ℝ)*x 1 + (2623716819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673395419/5000000000 : ℝ)^2207 ≤ (44254729880851/100000000000000 : ℝ)^1695 := by
    have hnat : (2673395419 : ℕ)^2207*100000000000000^1695 ≤ 44254729880851^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673395419 5000000000 44254729880851 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016106047/5000000000 : ℝ)^2207 ≤ (6279148771577/50000000000000 : ℝ)^1695 := by
    have hnat : (1016106047 : ℕ)^2207*50000000000000^1695 ≤ 6279148771577^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016106047 5000000000 6279148771577 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623716819/5000000000 : ℝ)^2207 ≤ (8637394513639/20000000000000 : ℝ)^1695 := by
    have hnat : (2623716819 : ℕ)^2207*20000000000000^1695 ≤ 8637394513639^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623716819 5000000000 8637394513639 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673395419/5000000000 : ℝ), (-1016106047/5000000000 : ℝ), (2623716819/5000000000 : ℝ)] ![(44254729880851/100000000000000 : ℝ), (6279148771577/50000000000000 : ℝ), (8637394513639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673395419/5000000000 : ℝ)|^2207 ≤ (44254729880851/100000000000000 : ℝ)^1695
        have hw : |(2673395419/5000000000 : ℝ)|=(2673395419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016106047/5000000000 : ℝ)|^2207 ≤ (6279148771577/50000000000000 : ℝ)^1695
        have hw : |(-1016106047/5000000000 : ℝ)|=(1016106047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623716819/5000000000 : ℝ)|^2207 ≤ (8637394513639/20000000000000 : ℝ)^1695
        have hw : |(2623716819/5000000000 : ℝ)|=(2623716819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s6_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069358047/2000000000 : ℝ)*x 0 + (1049486819/2000000000 : ℝ)*x 1 + (-508053073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069358047/2000000000 : ℝ)^2207 ≤ (44254723382301/100000000000000 : ℝ)^1695 := by
    have hnat : (1069358047 : ℕ)^2207*100000000000000^1695 ≤ 44254723382301^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069358047 2000000000 44254723382301 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049486819/2000000000 : ℝ)^2207 ≤ (337398261449/781250000000 : ℝ)^1695 := by
    have hnat : (1049486819 : ℕ)^2207*781250000000^1695 ≤ 337398261449^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049486819 2000000000 337398261449 781250000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508053073/2500000000 : ℝ)^2207 ≤ (6279149568157/50000000000000 : ℝ)^1695 := by
    have hnat : (508053073 : ℕ)^2207*50000000000000^1695 ≤ 6279149568157^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508053073 2500000000 6279149568157 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069358047/2000000000 : ℝ), (1049486819/2000000000 : ℝ), (-508053073/2500000000 : ℝ)] ![(44254723382301/100000000000000 : ℝ), (337398261449/781250000000 : ℝ), (6279149568157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069358047/2000000000 : ℝ)|^2207 ≤ (44254723382301/100000000000000 : ℝ)^1695
        have hw : |(1069358047/2000000000 : ℝ)|=(1069358047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049486819/2000000000 : ℝ)|^2207 ≤ (337398261449/781250000000 : ℝ)^1695
        have hw : |(1049486819/2000000000 : ℝ)|=(1049486819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508053073/2500000000 : ℝ)|^2207 ≤ (6279149568157/50000000000000 : ℝ)^1695
        have hw : |(-508053073/2500000000 : ℝ)|=(508053073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s6_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2149080539/5000000000 : ℝ)*x 0 + (4127189703/10000000000 : ℝ)*x 1 + (4475408143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149080539/5000000000 : ℝ)^2207 ≤ (3330506302479/10000000000000 : ℝ)^1695 := by
    have hnat : (2149080539 : ℕ)^2207*10000000000000^1695 ≤ 3330506302479^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149080539 5000000000 3330506302479 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127189703/10000000000 : ℝ)^2207 ≤ (1974409100707/6250000000000 : ℝ)^1695 := by
    have hnat : (4127189703 : ℕ)^2207*6250000000000^1695 ≤ 1974409100707^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127189703 10000000000 1974409100707 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475408143/10000000000 : ℝ)^2207 ≤ (3510439135069/10000000000000 : ℝ)^1695 := by
    have hnat : (4475408143 : ℕ)^2207*10000000000000^1695 ≤ 3510439135069^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475408143 10000000000 3510439135069 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149080539/5000000000 : ℝ), (4127189703/10000000000 : ℝ), (4475408143/10000000000 : ℝ)] ![(3330506302479/10000000000000 : ℝ), (1974409100707/6250000000000 : ℝ), (3510439135069/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149080539/5000000000 : ℝ)|^2207 ≤ (3330506302479/10000000000000 : ℝ)^1695
        have hw : |(2149080539/5000000000 : ℝ)|=(2149080539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127189703/10000000000 : ℝ)|^2207 ≤ (1974409100707/6250000000000 : ℝ)^1695
        have hw : |(4127189703/10000000000 : ℝ)|=(4127189703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475408143/10000000000 : ℝ)|^2207 ≤ (3510439135069/10000000000000 : ℝ)^1695
        have hw : |(4475408143/10000000000 : ℝ)|=(4475408143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s6_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-975517487/5000000000 : ℝ)*x 0 + (2624004963/5000000000 : ℝ)*x 1 + (216254263/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975517487/5000000000 : ℝ)^2207 ≤ (11909102729459/100000000000000 : ℝ)^1695 := by
    have hnat : (975517487 : ℕ)^2207*100000000000000^1695 ≤ 11909102729459^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975517487 5000000000 11909102729459 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624004963/5000000000 : ℝ)^2207 ≤ (8638629650867/20000000000000 : ℝ)^1695 := by
    have hnat : (2624004963 : ℕ)^2207*20000000000000^1695 ≤ 8638629650867^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624004963 5000000000 8638629650867 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216254263/400000000 : ℝ)^2207 ≤ (44897748998349/100000000000000 : ℝ)^1695 := by
    have hnat : (216254263 : ℕ)^2207*100000000000000^1695 ≤ 44897748998349^1695*400000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216254263 400000000 44897748998349 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975517487/5000000000 : ℝ), (2624004963/5000000000 : ℝ), (216254263/400000000 : ℝ)] ![(11909102729459/100000000000000 : ℝ), (8638629650867/20000000000000 : ℝ), (44897748998349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975517487/5000000000 : ℝ)|^2207 ≤ (11909102729459/100000000000000 : ℝ)^1695
        have hw : |(-975517487/5000000000 : ℝ)|=(975517487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624004963/5000000000 : ℝ)|^2207 ≤ (8638629650867/20000000000000 : ℝ)^1695
        have hw : |(2624004963/5000000000 : ℝ)|=(2624004963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216254263/400000000 : ℝ)|^2207 ≤ (44897748998349/100000000000000 : ℝ)^1695
        have hw : |(216254263/400000000 : ℝ)|=(216254263/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s6_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305225091/10000000000 : ℝ)*x 0 + (-468322411/2500000000 : ℝ)*x 1 + (1351589071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305225091/10000000000 : ℝ)^2207 ≤ (547591268091/1250000000000 : ℝ)^1695 := by
    have hnat : (5305225091 : ℕ)^2207*1250000000000^1695 ≤ 547591268091^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305225091 10000000000 547591268091 1250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468322411/2500000000 : ℝ)^2207 ≤ (11294952690619/100000000000000 : ℝ)^1695 := by
    have hnat : (468322411 : ℕ)^2207*100000000000000^1695 ≤ 11294952690619^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468322411 2500000000 11294952690619 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351589071/2500000000 : ℝ)^2207 ≤ (1122443646293/2500000000000 : ℝ)^1695 := by
    have hnat : (1351589071 : ℕ)^2207*2500000000000^1695 ≤ 1122443646293^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351589071 2500000000 1122443646293 2500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305225091/10000000000 : ℝ), (-468322411/2500000000 : ℝ), (1351589071/2500000000 : ℝ)] ![(547591268091/1250000000000 : ℝ), (11294952690619/100000000000000 : ℝ), (1122443646293/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305225091/10000000000 : ℝ)|^2207 ≤ (547591268091/1250000000000 : ℝ)^1695
        have hw : |(5305225091/10000000000 : ℝ)|=(5305225091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468322411/2500000000 : ℝ)|^2207 ≤ (11294952690619/100000000000000 : ℝ)^1695
        have hw : |(-468322411/2500000000 : ℝ)|=(468322411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351589071/2500000000 : ℝ)|^2207 ≤ (1122443646293/2500000000000 : ℝ)^1695
        have hw : |(1351589071/2500000000 : ℝ)|=(1351589071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s6_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305226271/10000000000 : ℝ)*x 0 + (540635471/1000000000 : ℝ)*x 1 + (-374658039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305226271/10000000000 : ℝ)^2207 ≤ (43807314134233/100000000000000 : ℝ)^1695 := by
    have hnat : (5305226271 : ℕ)^2207*100000000000000^1695 ≤ 43807314134233^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305226271 10000000000 43807314134233 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540635471/1000000000 : ℝ)^2207 ≤ (11224432207953/25000000000000 : ℝ)^1695 := by
    have hnat : (540635471 : ℕ)^2207*25000000000000^1695 ≤ 11224432207953^1695*1000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540635471 1000000000 11224432207953 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374658039/2000000000 : ℝ)^2207 ≤ (11294957016393/100000000000000 : ℝ)^1695 := by
    have hnat : (374658039 : ℕ)^2207*100000000000000^1695 ≤ 11294957016393^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374658039 2000000000 11294957016393 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305226271/10000000000 : ℝ), (540635471/1000000000 : ℝ), (-374658039/2000000000 : ℝ)] ![(43807314134233/100000000000000 : ℝ), (11224432207953/25000000000000 : ℝ), (11294957016393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305226271/10000000000 : ℝ)|^2207 ≤ (43807314134233/100000000000000 : ℝ)^1695
        have hw : |(5305226271/10000000000 : ℝ)|=(5305226271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540635471/1000000000 : ℝ)|^2207 ≤ (11224432207953/25000000000000 : ℝ)^1695
        have hw : |(540635471/1000000000 : ℝ)|=(540635471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-374658039/2000000000 : ℝ)|^2207 ≤ (11294957016393/100000000000000 : ℝ)^1695
        have hw : |(-374658039/2000000000 : ℝ)|=(374658039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s6_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298185797/10000000000 : ℝ)*x 0 + (111853719/250000000 : ℝ)*x 1 + (4128455143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298185797/10000000000 : ℝ)^2207 ≤ (6661062484387/20000000000000 : ℝ)^1695 := by
    have hnat : (4298185797 : ℕ)^2207*20000000000000^1695 ≤ 6661062484387^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298185797 10000000000 6661062484387 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111853719/250000000 : ℝ)^2207 ≤ (8772882394739/25000000000000 : ℝ)^1695 := by
    have hnat : (111853719 : ℕ)^2207*25000000000000^1695 ≤ 8772882394739^1695*250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111853719 250000000 8772882394739 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128455143/10000000000 : ℝ)^2207 ≤ (31603157989761/100000000000000 : ℝ)^1695 := by
    have hnat : (4128455143 : ℕ)^2207*100000000000000^1695 ≤ 31603157989761^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128455143 10000000000 31603157989761 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298185797/10000000000 : ℝ), (111853719/250000000 : ℝ), (4128455143/10000000000 : ℝ)] ![(6661062484387/20000000000000 : ℝ), (8772882394739/25000000000000 : ℝ), (31603157989761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298185797/10000000000 : ℝ)|^2207 ≤ (6661062484387/20000000000000 : ℝ)^1695
        have hw : |(4298185797/10000000000 : ℝ)|=(4298185797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111853719/250000000 : ℝ)|^2207 ≤ (8772882394739/25000000000000 : ℝ)^1695
        have hw : |(111853719/250000000 : ℝ)|=(111853719/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128455143/10000000000 : ℝ)|^2207 ≤ (31603157989761/100000000000000 : ℝ)^1695
        have hw : |(4128455143/10000000000 : ℝ)|=(4128455143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11387/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (2145209096129541/25000000000000000000 : ℝ) := by
    have hpowers : (11387/100000 : ℝ)^4413 ≤ (2145209096129541/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11387 : ℕ)^4413*25000000000000000000^1024 ≤ 2145209096129541^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11387 100000 2145209096129541 25000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11387/100000 : ℝ)) (X := (2145209096129541/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (26349171036509449/100000000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^4413 ≤ (26349171036509449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14773 : ℕ)^4413*100000000000000000000^1024 ≤ 26349171036509449^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 26349171036509449 100000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (26349171036509449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502145209096129541/12500000000000000000 : ℝ) ≤ (125004977451559/125000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (12502145209096129541/12500000000000000000 : ℝ)^1024 ≤ (125004977451559/125000000000000 : ℝ)^4413 := by
      have hnat : (12502145209096129541 : ℕ)^1024*125000000000000^4413 ≤ 125004977451559^4413*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502145209096129541 12500000000000000000 125004977451559 125000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125004977451559/125000000000000 : ℝ)) (X := (12502145209096129541/12500000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034930007421027613/100000000000000000000 : ℝ) ≤ (2000162082624959/2000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (100034930007421027613/100000000000000000000 : ℝ)^1024 ≤ (2000162082624959/2000000000000000 : ℝ)^4413 := by
      have hnat : (100034930007421027613 : ℕ)^1024*2000000000000000^4413 ≤ 2000162082624959^4413*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034930007421027613 100000000000000000000 2000162082624959 2000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000162082624959/2000000000000000 : ℝ)) (X := (100034930007421027613/100000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026349171036509449/50000000000000000000 : ℝ) ≤ (1000122263012487/1000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (50026349171036509449/50000000000000000000 : ℝ)^1024 ≤ (1000122263012487/1000000000000000 : ℝ)^4413 := by
      have hnat : (50026349171036509449 : ℕ)^1024*1000000000000000^4413 ≤ 1000122263012487^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026349171036509449 50000000000000000000 1000122263012487 1000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000122263012487/1000000000000000 : ℝ)) (X := (50026349171036509449/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2145209096129541/25000000000000000000 : ℝ) ≤ ((3385196046211859387/3386000000000000000 : ℝ)+2*(16488680003/13544000000000 : ℝ)*(11387/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (3385196046211859387/3386000000000000000 : ℝ)+2*(16488680003/13544000000000 : ℝ)*(11387/100000 : ℝ)=(125004977451559/125000000000000 : ℝ) by norm_num, show 1+2*(2145209096129541/25000000000000000000 : ℝ)=(12502145209096129541/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26349171036509449/100000000000000000000 : ℝ)+(2145209096129541/25000000000000000000 : ℝ) ≤ ((3385196046211859387/3386000000000000000 : ℝ)+(16488680003/13544000000000 : ℝ)*((14773/100000 : ℝ)+(11387/100000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (3385196046211859387/3386000000000000000 : ℝ)+(16488680003/13544000000000 : ℝ)*((14773/100000 : ℝ)+(11387/100000 : ℝ))=(2000162082624959/2000000000000000 : ℝ) by norm_num, show 1+(26349171036509449/100000000000000000000 : ℝ)+(2145209096129541/25000000000000000000 : ℝ)=(100034930007421027613/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26349171036509449/100000000000000000000 : ℝ) ≤ ((3385196046211859387/3386000000000000000 : ℝ)+2*(16488680003/13544000000000 : ℝ)*(14773/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (3385196046211859387/3386000000000000000 : ℝ)+2*(16488680003/13544000000000 : ℝ)*(14773/100000 : ℝ)=(1000122263012487/1000000000000000 : ℝ) by norm_num, show 1+2*(26349171036509449/100000000000000000000 : ℝ)=(50026349171036509449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3385196046211859387/3386000000000000000 : ℝ)*(X 1 0+X 2 0)+(16488680003/13544000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (3385196046211859387/3386000000000000000 : ℝ)) (alpha := (16488680003/13544000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3385196046211859387/3386000000000000000 : ℝ)*(X 0 1+X 2 1)+(16488680003/13544000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (3385196046211859387/3386000000000000000 : ℝ)) (alpha := (16488680003/13544000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3385196046211859387/3386000000000000000 : ℝ)*(X 0 2+X 1 2)+(16488680003/13544000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (3385196046211859387/3386000000000000000 : ℝ)) (alpha := (16488680003/13544000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-121939029/625000000 : ℝ)*X 0 0+(5406935657/10000000000 : ℝ)*X 0 1+(1311858349/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673395419/5000000000 : ℝ)*X 1 0+(-1016106047/5000000000 : ℝ)*X 1 1+(2623716819/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069358047/2000000000 : ℝ)*X 2 0+(1049486819/2000000000 : ℝ)*X 2 1+(-508053073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149080539/5000000000 : ℝ)*X 0 0+(4127189703/10000000000 : ℝ)*X 0 1+(4475408143/10000000000 : ℝ)*X 0 2+(2149080539/5000000000 : ℝ)*X 1 0+(4127189703/10000000000 : ℝ)*X 1 1+(4475408143/10000000000 : ℝ)*X 1 2+(2149080539/5000000000 : ℝ)*X 2 0+(4127189703/10000000000 : ℝ)*X 2 1+(4475408143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975517487/5000000000 : ℝ)*X 0 0+(2624004963/5000000000 : ℝ)*X 0 1+(216254263/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305225091/10000000000 : ℝ)*X 1 0+(-468322411/2500000000 : ℝ)*X 1 1+(1351589071/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305226271/10000000000 : ℝ)*X 2 0+(540635471/1000000000 : ℝ)*X 2 1+(-374658039/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298185797/10000000000 : ℝ)*X 0 0+(111853719/250000000 : ℝ)*X 0 1+(4128455143/10000000000 : ℝ)*X 0 2+(4298185797/10000000000 : ℝ)*X 1 0+(111853719/250000000 : ℝ)*X 1 1+(4128455143/10000000000 : ℝ)*X 1 2+(4298185797/10000000000 : ℝ)*X 2 0+(111853719/250000000 : ℝ)*X 2 1+(4128455143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (227120498834236205950872201/33860000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140679521/6250000000000 : ℝ)*(base19) + (675567409/50000000000000 : ℝ)*(base23) + (27182977/100000000000000 : ℝ)*(upper2) + (101575987/20000000000000 : ℝ)*(upper3) + (130196041/100000000000000 : ℝ)*(upper4) + (914141696189453/20000000000000 : ℝ)*(major0) + (914141696189453/20000000000000 : ℝ)*(major1) + (914141696189453/20000000000000 : ℝ)*(major2) + (3134785587559517/50000000000000 : ℝ)*(sp0) + (3134806912806573/50000000000000 : ℝ)*(sp1) + (783701840668833/12500000000000 : ℝ)*(sp2) + (1435888834202667/50000000000000 : ℝ)*(sp3) + (2806335403/6250000000000 : ℝ)*(sp4) + (2299341589/10000000000000 : ℝ)*(sp7) + (358975082727653/12500000000000 : ℝ)*(f.failure) + (3134808038242741/50000000000000 : ℝ)*(f.sum) + (7673241004931/3386000000000000000000000000 : ℝ)*base65 + (1006124017962835311/67720000000000000000000000000000 : ℝ)*base67 + (9503560697075311/67720000000000000000000000000000 : ℝ)*base69 + (534993923202595311/67720000000000000000000000000000 : ℝ)*base71 + (17485935966467/3386000000000000000000000000 : ℝ)*base73 + (525573973008595311/67720000000000000000000000000000 : ℝ)*base75 + (639227890860355311/67720000000000000000000000000000 : ℝ)*base77 + (404558393821155311/67720000000000000000000000000000 : ℝ)*base79 + (694211348609/3386000000000000000000000000 : ℝ)*base82 + (9019233/625000000000000000000 : ℝ)*base90 + (9019233/625000000000000000000 : ℝ)*base92 + (9019233/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14432062275401301068571/1693000000000000000000000000 : ℝ) := by norm_num
    linear_combination (497829719/25000000000000 : ℝ)*(base19) + (3991613043/100000000000000 : ℝ)*(base23) + (421309729/50000000000000 : ℝ)*(lower1) + (11441577/3125000000000 : ℝ)*(lower4) + (68809971/20000000000000 : ℝ)*(upper5) + (2301991259075027/50000000000000 : ℝ)*(major0) + (2301991259075027/50000000000000 : ℝ)*(major1) + (2301991259075027/50000000000000 : ℝ)*(major2) + (4771444073/25000000000000 : ℝ)*(sp0) + (3015062877/25000000000000 : ℝ)*(sp1) + (3157619374225543/50000000000000 : ℝ)*(sp4) + (3157621891328497/50000000000000 : ℝ)*(sp5) + (3157626921307167/50000000000000 : ℝ)*(sp6) + (1446353458960537/50000000000000 : ℝ)*(sp7) + (1446353458960537/50000000000000 : ℝ)*(f.failure) + (3157628917113689/50000000000000 : ℝ)*(f.sum) + (5369272431713/1693000000000000000000000000 : ℝ)*base66 + (942165483481478449/169300000000000000000000000000000 : ℝ)*base67 + (1134811986037721551/169300000000000000000000000000000 : ℝ)*base70 + (380984177147321551/169300000000000000000000000000000 : ℝ)*base72 + (7641494149469/1693000000000000000000000000 : ℝ)*base73 + (141703526724878449/169300000000000000000000000000000 : ℝ)*base75 + (701375683818121551/169300000000000000000000000000000 : ℝ)*base78 + (2272712864043478449/169300000000000000000000000000000 : ℝ)*base79 + (12104757343831/1693000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19437643/2500000000000000000000 : ℝ)*base89 + (19437643/2500000000000000000000 : ℝ)*base91 + (19437643/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1454_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1454_s7_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-975513043/5000000000 : ℝ)*x 0 + (5406914769/10000000000 : ℝ)*x 1 + (5247453271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975513043/5000000000 : ℝ)^2207 ≤ (1488629011189/12500000000000 : ℝ)^1695 := by
    have hnat : (975513043 : ℕ)^2207*12500000000000^1695 ≤ 1488629011189^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975513043 5000000000 1488629011189 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406914769/10000000000 : ℝ)^2207 ≤ (71846055891/160000000000 : ℝ)^1695 := by
    have hnat : (5406914769 : ℕ)^2207*160000000000^1695 ≤ 71846055891^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406914769 10000000000 71846055891 160000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247453271/10000000000 : ℝ)^2207 ≤ (43187182958319/100000000000000 : ℝ)^1695 := by
    have hnat : (5247453271 : ℕ)^2207*100000000000000^1695 ≤ 43187182958319^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247453271 10000000000 43187182958319 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975513043/5000000000 : ℝ), (5406914769/10000000000 : ℝ), (5247453271/10000000000 : ℝ)] ![(1488629011189/12500000000000 : ℝ), (71846055891/160000000000 : ℝ), (43187182958319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975513043/5000000000 : ℝ)|^2207 ≤ (1488629011189/12500000000000 : ℝ)^1695
        have hw : |(-975513043/5000000000 : ℝ)|=(975513043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406914769/10000000000 : ℝ)|^2207 ≤ (71846055891/160000000000 : ℝ)^1695
        have hw : |(5406914769/10000000000 : ℝ)|=(5406914769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247453271/10000000000 : ℝ)|^2207 ≤ (43187182958319/100000000000000 : ℝ)^1695
        have hw : |(5247453271/10000000000 : ℝ)|=(5247453271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s7_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336696313/2500000000 : ℝ)*x 0 + (-2032193403/10000000000 : ℝ)*x 1 + (5247453289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336696313/2500000000 : ℝ)^2207 ≤ (8850933936073/20000000000000 : ℝ)^1695 := by
    have hnat : (1336696313 : ℕ)^2207*20000000000000^1695 ≤ 8850933936073^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336696313 2500000000 8850933936073 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2032193403/10000000000 : ℝ)^2207 ≤ (12558147150611/100000000000000 : ℝ)^1695 := by
    have hnat : (2032193403 : ℕ)^2207*100000000000000^1695 ≤ 12558147150611^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032193403 10000000000 12558147150611 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247453289/10000000000 : ℝ)^2207 ≤ (43187183151209/100000000000000 : ℝ)^1695 := by
    have hnat : (5247453289 : ℕ)^2207*100000000000000^1695 ≤ 43187183151209^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247453289 10000000000 43187183151209 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336696313/2500000000 : ℝ), (-2032193403/10000000000 : ℝ), (5247453289/10000000000 : ℝ)] ![(8850933936073/20000000000000 : ℝ), (12558147150611/100000000000000 : ℝ), (43187183151209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336696313/2500000000 : ℝ)|^2207 ≤ (8850933936073/20000000000000 : ℝ)^1695
        have hw : |(1336696313/2500000000 : ℝ)|=(1336696313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2032193403/10000000000 : ℝ)|^2207 ≤ (12558147150611/100000000000000 : ℝ)^1695
        have hw : |(-2032193403/10000000000 : ℝ)|=(2032193403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247453289/10000000000 : ℝ)|^2207 ≤ (43187183151209/100000000000000 : ℝ)^1695
        have hw : |(5247453289/10000000000 : ℝ)|=(5247453289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s7_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668348157/1250000000 : ℝ)*x 0 + (209898131/400000000 : ℝ)*x 1 + (-2032193417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668348157/1250000000 : ℝ)^2207 ≤ (22127334861737/50000000000000 : ℝ)^1695 := by
    have hnat : (668348157 : ℕ)^2207*50000000000000^1695 ≤ 22127334861737^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668348157 1250000000 22127334861737 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209898131/400000000 : ℝ)^2207 ≤ (43187183001183/100000000000000 : ℝ)^1695 := by
    have hnat : (209898131 : ℕ)^2207*100000000000000^1695 ≤ 43187183001183^1695*400000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209898131 400000000 43187183001183 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2032193417/10000000000 : ℝ)^2207 ≤ (12558147263259/100000000000000 : ℝ)^1695 := by
    have hnat : (2032193417 : ℕ)^2207*100000000000000^1695 ≤ 12558147263259^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032193417 10000000000 12558147263259 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668348157/1250000000 : ℝ), (209898131/400000000 : ℝ), (-2032193417/10000000000 : ℝ)] ![(22127334861737/50000000000000 : ℝ), (43187183001183/100000000000000 : ℝ), (12558147263259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668348157/1250000000 : ℝ)|^2207 ≤ (22127334861737/50000000000000 : ℝ)^1695
        have hw : |(668348157/1250000000 : ℝ)|=(668348157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209898131/400000000 : ℝ)|^2207 ≤ (43187183001183/100000000000000 : ℝ)^1695
        have hw : |(209898131/400000000 : ℝ)|=(209898131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2032193417/10000000000 : ℝ)|^2207 ≤ (12558147263259/100000000000000 : ℝ)^1695
        have hw : |(-2032193417/10000000000 : ℝ)|=(2032193417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s7_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268635153/625000000 : ℝ)*x 0 + (4127233397/10000000000 : ℝ)*x 1 + (559420519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268635153/625000000 : ℝ)^2207 ≤ (6661015369421/20000000000000 : ℝ)^1695 := by
    have hnat : (268635153 : ℕ)^2207*20000000000000^1695 ≤ 6661015369421^1695*625000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268635153 625000000 6661015369421 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127233397/10000000000 : ℝ)^2207 ≤ (15795490540447/50000000000000 : ℝ)^1695 := by
    have hnat : (4127233397 : ℕ)^2207*50000000000000^1695 ≤ 15795490540447^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127233397 10000000000 15795490540447 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559420519/1250000000 : ℝ)^2207 ≤ (2193996378931/6250000000000 : ℝ)^1695 := by
    have hnat : (559420519 : ℕ)^2207*6250000000000^1695 ≤ 2193996378931^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559420519 1250000000 2193996378931 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268635153/625000000 : ℝ), (4127233397/10000000000 : ℝ), (559420519/1250000000 : ℝ)] ![(6661015369421/20000000000000 : ℝ), (15795490540447/50000000000000 : ℝ), (2193996378931/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268635153/625000000 : ℝ)|^2207 ≤ (6661015369421/20000000000000 : ℝ)^1695
        have hw : |(268635153/625000000 : ℝ)|=(268635153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127233397/10000000000 : ℝ)|^2207 ≤ (15795490540447/50000000000000 : ℝ)^1695
        have hw : |(4127233397/10000000000 : ℝ)|=(4127233397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559420519/1250000000 : ℝ)|^2207 ≤ (2193996378931/6250000000000 : ℝ)^1695
        have hw : |(559420519/1250000000 : ℝ)|=(559420519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s7_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951037209/10000000000 : ℝ)*x 0 + (5248029603/10000000000 : ℝ)*x 1 + (5406335431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951037209/10000000000 : ℝ)^2207 ≤ (5954560246391/50000000000000 : ℝ)^1695 := by
    have hnat : (1951037209 : ℕ)^2207*50000000000000^1695 ≤ 5954560246391^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951037209 10000000000 5954560246391 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5248029603/10000000000 : ℝ)^2207 ≤ (10798339780741/25000000000000 : ℝ)^1695 := by
    have hnat : (5248029603 : ℕ)^2207*25000000000000^1695 ≤ 10798339780741^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248029603 10000000000 10798339780741 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406335431/10000000000 : ℝ)^2207 ≤ (4489752036509/10000000000000 : ℝ)^1695 := by
    have hnat : (5406335431 : ℕ)^2207*10000000000000^1695 ≤ 4489752036509^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406335431 10000000000 4489752036509 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951037209/10000000000 : ℝ), (5248029603/10000000000 : ℝ), (5406335431/10000000000 : ℝ)] ![(5954560246391/50000000000000 : ℝ), (10798339780741/25000000000000 : ℝ), (4489752036509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951037209/10000000000 : ℝ)|^2207 ≤ (5954560246391/50000000000000 : ℝ)^1695
        have hw : |(-1951037209/10000000000 : ℝ)|=(1951037209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5248029603/10000000000 : ℝ)|^2207 ≤ (10798339780741/25000000000000 : ℝ)^1695
        have hw : |(5248029603/10000000000 : ℝ)|=(5248029603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406335431/10000000000 : ℝ)|^2207 ≤ (4489752036509/10000000000000 : ℝ)^1695
        have hw : |(5406335431/10000000000 : ℝ)|=(5406335431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s7_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305230247/10000000000 : ℝ)*x 0 + (-374662257/2000000000 : ℝ)*x 1 + (1081267089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305230247/10000000000 : ℝ)^2207 ≤ (43807356882821/100000000000000 : ℝ)^1695 := by
    have hnat : (5305230247 : ℕ)^2207*100000000000000^1695 ≤ 43807356882821^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305230247 10000000000 43807356882821 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374662257/2000000000 : ℝ)^2207 ≤ (18072196143/160000000000 : ℝ)^1695 := by
    have hnat : (374662257 : ℕ)^2207*160000000000^1695 ≤ 18072196143^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374662257 2000000000 18072196143 160000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081267089/2000000000 : ℝ)^2207 ≤ (22448760258237/50000000000000 : ℝ)^1695 := by
    have hnat : (1081267089 : ℕ)^2207*50000000000000^1695 ≤ 22448760258237^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081267089 2000000000 22448760258237 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305230247/10000000000 : ℝ), (-374662257/2000000000 : ℝ), (1081267089/2000000000 : ℝ)] ![(43807356882821/100000000000000 : ℝ), (18072196143/160000000000 : ℝ), (22448760258237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305230247/10000000000 : ℝ)|^2207 ≤ (43807356882821/100000000000000 : ℝ)^1695
        have hw : |(5305230247/10000000000 : ℝ)|=(5305230247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374662257/2000000000 : ℝ)|^2207 ≤ (18072196143/160000000000 : ℝ)^1695
        have hw : |(-374662257/2000000000 : ℝ)|=(374662257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081267089/2000000000 : ℝ)|^2207 ≤ (22448760258237/50000000000000 : ℝ)^1695
        have hw : |(1081267089/2000000000 : ℝ)|=(1081267089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s7_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305230287/10000000000 : ℝ)*x 0 + (67579193/125000000 : ℝ)*x 1 + (-468327809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305230287/10000000000 : ℝ)^2207 ≤ (43807357312887/100000000000000 : ℝ)^1695 := by
    have hnat : (5305230287 : ℕ)^2207*100000000000000^1695 ≤ 43807357312887^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305230287 10000000000 43807357312887 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67579193/125000000 : ℝ)^2207 ≤ (5612190057801/12500000000000 : ℝ)^1695 := by
    have hnat : (67579193 : ℕ)^2207*12500000000000^1695 ≤ 5612190057801^1695*125000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67579193 125000000 5612190057801 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468327809/2500000000 : ℝ)^2207 ≤ (5647561102343/50000000000000 : ℝ)^1695 := by
    have hnat : (468327809 : ℕ)^2207*50000000000000^1695 ≤ 5647561102343^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468327809 2500000000 5647561102343 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305230287/10000000000 : ℝ), (67579193/125000000 : ℝ), (-468327809/2500000000 : ℝ)] ![(43807357312887/100000000000000 : ℝ), (5612190057801/12500000000000 : ℝ), (5647561102343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305230287/10000000000 : ℝ)|^2207 ≤ (43807357312887/100000000000000 : ℝ)^1695
        have hw : |(5305230287/10000000000 : ℝ)|=(5305230287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67579193/125000000 : ℝ)|^2207 ≤ (5612190057801/12500000000000 : ℝ)^1695
        have hw : |(67579193/125000000 : ℝ)|=(67579193/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468327809/2500000000 : ℝ)|^2207 ≤ (5647561102343/50000000000000 : ℝ)^1695
        have hw : |(-468327809/2500000000 : ℝ)|=(468327809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s7_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298186661/10000000000 : ℝ)*x 0 + (4474105989/10000000000 : ℝ)*x 1 + (4128498091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298186661/10000000000 : ℝ)^2207 ≤ (33305321139089/100000000000000 : ℝ)^1695 := by
    have hnat : (4298186661 : ℕ)^2207*100000000000000^1695 ≤ 33305321139089^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298186661 10000000000 33305321139089 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474105989/10000000000 : ℝ)^2207 ≤ (35091092788353/100000000000000 : ℝ)^1695 := by
    have hnat : (4474105989 : ℕ)^2207*100000000000000^1695 ≤ 35091092788353^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474105989 10000000000 35091092788353 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128498091/10000000000 : ℝ)^2207 ≤ (1264143442563/4000000000000 : ℝ)^1695 := by
    have hnat : (4128498091 : ℕ)^2207*4000000000000^1695 ≤ 1264143442563^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128498091 10000000000 1264143442563 4000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298186661/10000000000 : ℝ), (4474105989/10000000000 : ℝ), (4128498091/10000000000 : ℝ)] ![(33305321139089/100000000000000 : ℝ), (35091092788353/100000000000000 : ℝ), (1264143442563/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298186661/10000000000 : ℝ)|^2207 ≤ (33305321139089/100000000000000 : ℝ)^1695
        have hw : |(4298186661/10000000000 : ℝ)|=(4298186661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474105989/10000000000 : ℝ)|^2207 ≤ (35091092788353/100000000000000 : ℝ)^1695
        have hw : |(4474105989/10000000000 : ℝ)|=(4474105989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128498091/10000000000 : ℝ)|^2207 ≤ (1264143442563/4000000000000 : ℝ)^1695
        have hw : |(4128498091/10000000000 : ℝ)|=(4128498091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11391/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1139/10000 : ℝ) ^ (4413/1024 : ℝ) ≤ (536911452969059/6250000000000000000 : ℝ) := by
    have hpowers : (1139/10000 : ℝ)^4413 ≤ (536911452969059/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1139 : ℕ)^4413*6250000000000000000^1024 ≤ 536911452969059^1024*10000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1139 10000 536911452969059 6250000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1139/10000 : ℝ)) (X := (536911452969059/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (4413/1024 : ℝ) ≤ (26326119093290997/100000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^4413 ≤ (26326119093290997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1477 : ℕ)^4413*100000000000000000000^1024 ≤ 26326119093290997^1024*10000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 26326119093290997 100000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (26326119093290997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125536911452969059/3125000000000000000 : ℝ) ≤ (10000398648400801/10000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (3125536911452969059/3125000000000000000 : ℝ)^1024 ≤ (10000398648400801/10000000000000000 : ℝ)^4413 := by
      have hnat : (3125536911452969059 : ℕ)^1024*10000000000000000^4413 ≤ 10000398648400801^4413*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125536911452969059 3125000000000000000 10000398648400801 10000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000398648400801/10000000000000000 : ℝ)) (X := (3125536911452969059/3125000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034916702340795941/100000000000000000000 : ℝ) ≤ (5000405052237117/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (100034916702340795941/100000000000000000000 : ℝ)^1024 ≤ (5000405052237117/5000000000000000 : ℝ)^4413 := by
      have hnat : (100034916702340795941 : ℕ)^1024*5000000000000000^4413 ≤ 5000405052237117^4413*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034916702340795941 100000000000000000000 5000405052237117 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000405052237117/5000000000000000 : ℝ)) (X := (100034916702340795941/100000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026326119093290997/50000000000000000000 : ℝ) ≤ (10001221560547667/10000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (50026326119093290997/50000000000000000000 : ℝ)^1024 ≤ (10001221560547667/10000000000000000 : ℝ)^4413 := by
      have hnat : (50026326119093290997 : ℕ)^1024*10000000000000000^4413 ≤ 10001221560547667^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026326119093290997 50000000000000000000 10001221560547667 10000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001221560547667/10000000000000000 : ℝ)) (X := (50026326119093290997/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(536911452969059/6250000000000000000 : ℝ) ≤ ((844799361556047591/845000000000000000 : ℝ)+2*(411456073433/338000000000000 : ℝ)*(1139/10000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (844799361556047591/845000000000000000 : ℝ)+2*(411456073433/338000000000000 : ℝ)*(1139/10000 : ℝ)=(10000398648400801/10000000000000000 : ℝ) by norm_num, show 1+2*(536911452969059/6250000000000000000 : ℝ)=(3125536911452969059/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26326119093290997/100000000000000000000 : ℝ)+(536911452969059/6250000000000000000 : ℝ) ≤ ((844799361556047591/845000000000000000 : ℝ)+(411456073433/338000000000000 : ℝ)*((1477/10000 : ℝ)+(1139/10000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (844799361556047591/845000000000000000 : ℝ)+(411456073433/338000000000000 : ℝ)*((1477/10000 : ℝ)+(1139/10000 : ℝ))=(5000405052237117/5000000000000000 : ℝ) by norm_num, show 1+(26326119093290997/100000000000000000000 : ℝ)+(536911452969059/6250000000000000000 : ℝ)=(100034916702340795941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26326119093290997/100000000000000000000 : ℝ) ≤ ((844799361556047591/845000000000000000 : ℝ)+2*(411456073433/338000000000000 : ℝ)*(1477/10000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (844799361556047591/845000000000000000 : ℝ)+2*(411456073433/338000000000000 : ℝ)*(1477/10000 : ℝ)=(10001221560547667/10000000000000000 : ℝ) by norm_num, show 1+2*(26326119093290997/100000000000000000000 : ℝ)=(50026326119093290997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (844799361556047591/845000000000000000 : ℝ)*(X 1 0+X 2 0)+(411456073433/338000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (844799361556047591/845000000000000000 : ℝ)) (alpha := (411456073433/338000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (844799361556047591/845000000000000000 : ℝ)*(X 0 1+X 2 1)+(411456073433/338000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (844799361556047591/845000000000000000 : ℝ)) (alpha := (411456073433/338000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (844799361556047591/845000000000000000 : ℝ)*(X 0 2+X 1 2)+(411456073433/338000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (844799361556047591/845000000000000000 : ℝ)) (alpha := (411456073433/338000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-975513043/5000000000 : ℝ)*X 0 0+(5406914769/10000000000 : ℝ)*X 0 1+(5247453271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336696313/2500000000 : ℝ)*X 1 0+(-2032193403/10000000000 : ℝ)*X 1 1+(5247453289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668348157/1250000000 : ℝ)*X 2 0+(209898131/400000000 : ℝ)*X 2 1+(-2032193417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((268635153/625000000 : ℝ)*X 0 0+(4127233397/10000000000 : ℝ)*X 0 1+(559420519/1250000000 : ℝ)*X 0 2+(268635153/625000000 : ℝ)*X 1 0+(4127233397/10000000000 : ℝ)*X 1 1+(559420519/1250000000 : ℝ)*X 1 2+(268635153/625000000 : ℝ)*X 2 0+(4127233397/10000000000 : ℝ)*X 2 1+(559420519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1951037209/10000000000 : ℝ)*X 0 0+(5248029603/10000000000 : ℝ)*X 0 1+(5406335431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305230247/10000000000 : ℝ)*X 1 0+(-374662257/2000000000 : ℝ)*X 1 1+(1081267089/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305230287/10000000000 : ℝ)*X 2 0+(67579193/125000000 : ℝ)*X 2 1+(-468327809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298186661/10000000000 : ℝ)*X 0 0+(4474105989/10000000000 : ℝ)*X 0 1+(4128498091/10000000000 : ℝ)*X 0 2+(4298186661/10000000000 : ℝ)*X 1 0+(4474105989/10000000000 : ℝ)*X 1 1+(4128498091/10000000000 : ℝ)*X 1 2+(4298186661/10000000000 : ℝ)*X 2 0+(4474105989/10000000000 : ℝ)*X 2 1+(4128498091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19263522562558927842774381/8450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216962273/50000000000000 : ℝ)*(base19) + (411322927/100000000000000 : ℝ)*(base23) + (291861/2000000000000 : ℝ)*(lower2) + (16356979/25000000000000 : ℝ)*(upper3) + (28783993/100000000000000 : ℝ)*(upper5) + (914361890258299/20000000000000 : ℝ)*(major0) + (914361890258299/20000000000000 : ℝ)*(major1) + (914361890258299/20000000000000 : ℝ)*(major2) + (1254223369404509/20000000000000 : ℝ)*(sp0) + (3135562992636333/50000000000000 : ℝ)*(sp1) + (1567781501968571/25000000000000 : ℝ)*(sp2) + (718121954719859/25000000000000 : ℝ)*(sp3) + (9572174667/100000000000000 : ℝ)*(sp4) + (4588516109/100000000000000 : ℝ)*(sp7) + (1436246203697773/50000000000000 : ℝ)*(f.failure) + (6271126419197211/100000000000000 : ℝ)*(f.sum) + (1705606921053/3380000000000000000000000000 : ℝ)*base66 + (3194172935401907/1300000000000000000000000000000 : ℝ)*base68 + (1651868748601907/1300000000000000000000000000000 : ℝ)*base70 + (2514049348401907/1300000000000000000000000000000 : ℝ)*base72 + (16473958357367/3380000000000000000000000000 : ℝ)*base73 + (4862579241201907/1300000000000000000000000000000 : ℝ)*base76 + (4886854682001907/1300000000000000000000000000000 : ℝ)*base78 + (106602467601907/1300000000000000000000000000000 : ℝ)*base80 + (13664978031527/3380000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (16557447/2500000000000000000000 : ℝ)*base89 + (16557447/2500000000000000000000 : ℝ)*base91 + (16557447/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126145367171081573020559127/21125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8137073/800000000000 : ℝ)*(base19) + (225332059/20000000000000 : ℝ)*(base23) + (33810437/10000000000000 : ℝ)*(lower1) + (68988269/50000000000000 : ℝ)*(upper3) + (18244079/100000000000000 : ℝ)*(lower4) + (120310943/100000000000000 : ℝ)*(upper5) + (4605154049510951/100000000000000 : ℝ)*(major0) + (4605154049510951/100000000000000 : ℝ)*(major1) + (4605154049510951/100000000000000 : ℝ)*(major2) + (3512127751/100000000000000 : ℝ)*(sp2) + (3158432451307593/50000000000000 : ℝ)*(sp4) + (6316863885481061/100000000000000 : ℝ)*(sp5) + (6316860263827139/100000000000000 : ℝ)*(sp6) + (2893442997360747/100000000000000 : ℝ)*(sp7) + (2893442997360747/100000000000000 : ℝ)*(f.failure) + (3158432451307593/50000000000000 : ℝ)*(f.sum) + (11018009473083/16900000000000000000000000000 : ℝ)*base65 + (76850578206086657/6500000000000000000000000000000 : ℝ)*base67 + (19242870893086657/6500000000000000000000000000000 : ℝ)*base69 + (1010330639401586657/6500000000000000000000000000000 : ℝ)*base71 + (37125120938583/16900000000000000000000000000 : ℝ)*base73 + (21902466970413343/6500000000000000000000000000000 : ℝ)*base76 + (63750289868586657/6500000000000000000000000000000 : ℝ)*base77 + (125161896280586657/6500000000000000000000000000000 : ℝ)*base79 + (10381532936617/16900000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31343167/5000000000000000000000 : ℝ)*base90 + (31343167/5000000000000000000000 : ℝ)*base92 + (31343167/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1454_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1454_box_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1750148/9765625 : ℝ)*x 0 + (336573857/625000000 : ℝ)*x 1 + (673147701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1750148/9765625 : ℝ)^2207 ≤ (2132433242163/20000000000000 : ℝ)^1695 := by
    have hnat : (1750148 : ℕ)^2207*20000000000000^1695 ≤ 2132433242163^1695*9765625^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750148 9765625 2132433242163 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336573857/625000000 : ℝ)^2207 ≤ (44668917445909/100000000000000 : ℝ)^1695 := by
    have hnat : (336573857 : ℕ)^2207*100000000000000^1695 ≤ 44668917445909^1695*625000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336573857 625000000 44668917445909 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673147701/1250000000 : ℝ)^2207 ≤ (44668916322673/100000000000000 : ℝ)^1695 := by
    have hnat : (673147701 : ℕ)^2207*100000000000000^1695 ≤ 44668916322673^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673147701 1250000000 44668916322673 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1750148/9765625 : ℝ), (336573857/625000000 : ℝ), (673147701/1250000000 : ℝ)] ![(2132433242163/20000000000000 : ℝ), (44668917445909/100000000000000 : ℝ), (44668916322673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1750148/9765625 : ℝ)|^2207 ≤ (2132433242163/20000000000000 : ℝ)^1695
        have hw : |(-1750148/9765625 : ℝ)|=(1750148/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336573857/625000000 : ℝ)|^2207 ≤ (44668917445909/100000000000000 : ℝ)^1695
        have hw : |(336573857/625000000 : ℝ)|=(336573857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673147701/1250000000 : ℝ)|^2207 ≤ (44668916322673/100000000000000 : ℝ)^1695
        have hw : |(673147701/1250000000 : ℝ)|=(673147701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643110911/5000000000 : ℝ)*x 0 + (-1928206433/10000000000 : ℝ)*x 1 + (5385181653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643110911/5000000000 : ℝ)^2207 ≤ (21801547741793/50000000000000 : ℝ)^1695 := by
    have hnat : (2643110911 : ℕ)^2207*50000000000000^1695 ≤ 21801547741793^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643110911 5000000000 21801547741793 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928206433/10000000000 : ℝ)^2207 ≤ (366499615371/3125000000000 : ℝ)^1695 := by
    have hnat : (1928206433 : ℕ)^2207*3125000000000^1695 ≤ 366499615371^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928206433 10000000000 366499615371 3125000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385181653/10000000000 : ℝ)^2207 ≤ (44668916808689/100000000000000 : ℝ)^1695 := by
    have hnat : (5385181653 : ℕ)^2207*100000000000000^1695 ≤ 44668916808689^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385181653 10000000000 44668916808689 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643110911/5000000000 : ℝ), (-1928206433/10000000000 : ℝ), (5385181653/10000000000 : ℝ)] ![(21801547741793/50000000000000 : ℝ), (366499615371/3125000000000 : ℝ), (44668916808689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643110911/5000000000 : ℝ)|^2207 ≤ (21801547741793/50000000000000 : ℝ)^1695
        have hw : |(2643110911/5000000000 : ℝ)|=(2643110911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1928206433/10000000000 : ℝ)|^2207 ≤ (366499615371/3125000000000 : ℝ)^1695
        have hw : |(-1928206433/10000000000 : ℝ)|=(1928206433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385181653/10000000000 : ℝ)|^2207 ≤ (44668916808689/100000000000000 : ℝ)^1695
        have hw : |(5385181653/10000000000 : ℝ)|=(5385181653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286221919/10000000000 : ℝ)*x 0 + (1346295411/2500000000 : ℝ)*x 1 + (-964103157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286221919/10000000000 : ℝ)^2207 ≤ (43603096525367/100000000000000 : ℝ)^1695 := by
    have hnat : (5286221919 : ℕ)^2207*100000000000000^1695 ≤ 43603096525367^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286221919 10000000000 43603096525367 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346295411/2500000000 : ℝ)^2207 ≤ (8933783342297/20000000000000 : ℝ)^1695 := by
    have hnat : (1346295411 : ℕ)^2207*20000000000000^1695 ≤ 8933783342297^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346295411 2500000000 8933783342297 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964103157/5000000000 : ℝ)^2207 ≤ (11727986749441/100000000000000 : ℝ)^1695 := by
    have hnat : (964103157 : ℕ)^2207*100000000000000^1695 ≤ 11727986749441^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964103157 5000000000 11727986749441 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286221919/10000000000 : ℝ), (1346295411/2500000000 : ℝ), (-964103157/5000000000 : ℝ)] ![(43603096525367/100000000000000 : ℝ), (8933783342297/20000000000000 : ℝ), (11727986749441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286221919/10000000000 : ℝ)|^2207 ≤ (43603096525367/100000000000000 : ℝ)^1695
        have hw : |(5286221919/10000000000 : ℝ)|=(5286221919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346295411/2500000000 : ℝ)|^2207 ≤ (8933783342297/20000000000000 : ℝ)^1695
        have hw : |(1346295411/2500000000 : ℝ)|=(1346295411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964103157/5000000000 : ℝ)|^2207 ≤ (11727986749441/100000000000000 : ℝ)^1695
        have hw : |(-964103157/5000000000 : ℝ)|=(964103157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2221984509/5000000000 : ℝ)*x 0 + (825961/1953125 : ℝ)*x 1 + (2114460249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221984509/5000000000 : ℝ)^2207 ≤ (34783638812709/100000000000000 : ℝ)^1695 := by
    have hnat : (2221984509 : ℕ)^2207*100000000000000^1695 ≤ 34783638812709^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221984509 5000000000 34783638812709 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825961/1953125 : ℝ)^2207 ≤ (509502807729/1562500000000 : ℝ)^1695 := by
    have hnat : (825961 : ℕ)^2207*1562500000000^1695 ≤ 509502807729^1695*1953125^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825961 1953125 509502807729 1562500000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114460249/5000000000 : ℝ)^2207 ≤ (32608181481759/100000000000000 : ℝ)^1695 := by
    have hnat : (2114460249 : ℕ)^2207*100000000000000^1695 ≤ 32608181481759^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114460249 5000000000 32608181481759 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221984509/5000000000 : ℝ), (825961/1953125 : ℝ), (2114460249/5000000000 : ℝ)] ![(34783638812709/100000000000000 : ℝ), (509502807729/1562500000000 : ℝ), (32608181481759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221984509/5000000000 : ℝ)|^2207 ≤ (34783638812709/100000000000000 : ℝ)^1695
        have hw : |(2221984509/5000000000 : ℝ)|=(2221984509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825961/1953125 : ℝ)|^2207 ≤ (509502807729/1562500000000 : ℝ)^1695
        have hw : |(825961/1953125 : ℝ)|=(825961/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114460249/5000000000 : ℝ)|^2207 ≤ (32608181481759/100000000000000 : ℝ)^1695
        have hw : |(2114460249/5000000000 : ℝ)|=(2114460249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112631579/10000000000 : ℝ)*x 0 + (5266872427/10000000000 : ℝ)*x 1 + (5266872229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112631579/10000000000 : ℝ)^2207 ≤ (1320920645701/10000000000000 : ℝ)^1695 := by
    have hnat : (2112631579 : ℕ)^2207*10000000000000^1695 ≤ 1320920645701^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112631579 10000000000 1320920645701 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266872427/10000000000 : ℝ)^2207 ≤ (21697698913347/50000000000000 : ℝ)^1695 := by
    have hnat : (5266872427 : ℕ)^2207*50000000000000^1695 ≤ 21697698913347^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266872427 10000000000 21697698913347 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266872229/10000000000 : ℝ)^2207 ≤ (43395395702527/100000000000000 : ℝ)^1695 := by
    have hnat : (5266872229 : ℕ)^2207*100000000000000^1695 ≤ 43395395702527^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266872229 10000000000 43395395702527 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112631579/10000000000 : ℝ), (5266872427/10000000000 : ℝ), (5266872229/10000000000 : ℝ)] ![(1320920645701/10000000000000 : ℝ), (21697698913347/50000000000000 : ℝ), (43395395702527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112631579/10000000000 : ℝ)|^2207 ≤ (1320920645701/10000000000000 : ℝ)^1695
        have hw : |(-2112631579/10000000000 : ℝ)|=(2112631579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266872427/10000000000 : ℝ)|^2207 ≤ (21697698913347/50000000000000 : ℝ)^1695
        have hw : |(5266872427/10000000000 : ℝ)|=(5266872427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266872229/10000000000 : ℝ)|^2207 ≤ (43395395702527/100000000000000 : ℝ)^1695
        have hw : |(5266872229/10000000000 : ℝ)|=(5266872229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684468403/5000000000 : ℝ)*x 0 + (-1976395101/10000000000 : ℝ)*x 1 + (5266872523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684468403/5000000000 : ℝ)^2207 ≤ (44493546821547/100000000000000 : ℝ)^1695 := by
    have hnat : (2684468403 : ℕ)^2207*100000000000000^1695 ≤ 44493546821547^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684468403 5000000000 44493546821547 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976395101/10000000000 : ℝ)^2207 ≤ (12111054301523/100000000000000 : ℝ)^1695 := by
    have hnat : (1976395101 : ℕ)^2207*100000000000000^1695 ≤ 12111054301523^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976395101 10000000000 12111054301523 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266872523/10000000000 : ℝ)^2207 ≤ (43395398856593/100000000000000 : ℝ)^1695 := by
    have hnat : (5266872523 : ℕ)^2207*100000000000000^1695 ≤ 43395398856593^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266872523 10000000000 43395398856593 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684468403/5000000000 : ℝ), (-1976395101/10000000000 : ℝ), (5266872523/10000000000 : ℝ)] ![(44493546821547/100000000000000 : ℝ), (12111054301523/100000000000000 : ℝ), (43395398856593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684468403/5000000000 : ℝ)|^2207 ≤ (44493546821547/100000000000000 : ℝ)^1695
        have hw : |(2684468403/5000000000 : ℝ)|=(2684468403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1976395101/10000000000 : ℝ)|^2207 ≤ (12111054301523/100000000000000 : ℝ)^1695
        have hw : |(-1976395101/10000000000 : ℝ)|=(1976395101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266872523/10000000000 : ℝ)|^2207 ≤ (43395398856593/100000000000000 : ℝ)^1695
        have hw : |(5266872523/10000000000 : ℝ)|=(5266872523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1342234191/2500000000 : ℝ)*x 0 + (1053374451/2000000000 : ℝ)*x 1 + (-988197759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342234191/2500000000 : ℝ)^2207 ≤ (22246773184173/50000000000000 : ℝ)^1695 := by
    have hnat : (1342234191 : ℕ)^2207*50000000000000^1695 ≤ 22246773184173^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342234191 2500000000 22246773184173 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053374451/2000000000 : ℝ)^2207 ≤ (21697697990729/50000000000000 : ℝ)^1695 := by
    have hnat : (1053374451 : ℕ)^2207*50000000000000^1695 ≤ 21697697990729^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053374451 2000000000 21697697990729 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988197759/5000000000 : ℝ)^2207 ≤ (12111057628707/100000000000000 : ℝ)^1695 := by
    have hnat : (988197759 : ℕ)^2207*100000000000000^1695 ≤ 12111057628707^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988197759 5000000000 12111057628707 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342234191/2500000000 : ℝ), (1053374451/2000000000 : ℝ), (-988197759/5000000000 : ℝ)] ![(22246773184173/50000000000000 : ℝ), (21697697990729/50000000000000 : ℝ), (12111057628707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342234191/2500000000 : ℝ)|^2207 ≤ (22246773184173/50000000000000 : ℝ)^1695
        have hw : |(1342234191/2500000000 : ℝ)|=(1342234191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053374451/2000000000 : ℝ)|^2207 ≤ (21697697990729/50000000000000 : ℝ)^1695
        have hw : |(1053374451/2000000000 : ℝ)|=(1053374451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988197759/5000000000 : ℝ)|^2207 ≤ (12111057628707/100000000000000 : ℝ)^1695
        have hw : |(-988197759/5000000000 : ℝ)|=(988197759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2075637399/5000000000 : ℝ)*x 0 + (4375217339/10000000000 : ℝ)*x 1 + (2187608661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075637399/5000000000 : ℝ)^2207 ≤ (15915398465691/50000000000000 : ℝ)^1695 := by
    have hnat : (2075637399 : ℕ)^2207*50000000000000^1695 ≤ 15915398465691^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075637399 5000000000 15915398465691 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4375217339/10000000000 : ℝ)^2207 ≤ (8521150402797/25000000000000 : ℝ)^1695 := by
    have hnat : (4375217339 : ℕ)^2207*25000000000000^1695 ≤ 8521150402797^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375217339 10000000000 8521150402797 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187608661/5000000000 : ℝ)^2207 ≤ (34084601438747/100000000000000 : ℝ)^1695 := by
    have hnat : (2187608661 : ℕ)^2207*100000000000000^1695 ≤ 34084601438747^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187608661 5000000000 34084601438747 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2075637399/5000000000 : ℝ), (4375217339/10000000000 : ℝ), (2187608661/5000000000 : ℝ)] ![(15915398465691/50000000000000 : ℝ), (8521150402797/25000000000000 : ℝ), (34084601438747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2075637399/5000000000 : ℝ)|^2207 ≤ (15915398465691/50000000000000 : ℝ)^1695
        have hw : |(2075637399/5000000000 : ℝ)|=(2075637399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4375217339/10000000000 : ℝ)|^2207 ≤ (8521150402797/25000000000000 : ℝ)^1695
        have hw : |(4375217339/10000000000 : ℝ)|=(4375217339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2187608661/5000000000 : ℝ)|^2207 ≤ (34084601438747/100000000000000 : ℝ)^1695
        have hw : |(2187608661/5000000000 : ℝ)|=(2187608661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_8 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-409015243/2000000000 : ℝ)*x 0 + (2592464349/5000000000 : ℝ)*x 1 + (5399139589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409015243/2000000000 : ℝ)^2207 ≤ (24730282211/195312500000 : ℝ)^1695 := by
    have hnat : (409015243 : ℕ)^2207*195312500000^1695 ≤ 24730282211^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409015243 2000000000 24730282211 195312500000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592464349/5000000000 : ℝ)^2207 ≤ (21259184578551/50000000000000 : ℝ)^1695 := by
    have hnat : (2592464349 : ℕ)^2207*50000000000000^1695 ≤ 21259184578551^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592464349 5000000000 21259184578551 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399139589/10000000000 : ℝ)^2207 ≤ (22409863166793/50000000000000 : ℝ)^1695 := by
    have hnat : (5399139589 : ℕ)^2207*50000000000000^1695 ≤ 22409863166793^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399139589 10000000000 22409863166793 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409015243/2000000000 : ℝ), (2592464349/5000000000 : ℝ), (5399139589/10000000000 : ℝ)] ![(24730282211/195312500000 : ℝ), (21259184578551/50000000000000 : ℝ), (22409863166793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409015243/2000000000 : ℝ)|^2207 ≤ (24730282211/195312500000 : ℝ)^1695
        have hw : |(-409015243/2000000000 : ℝ)|=(409015243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592464349/5000000000 : ℝ)|^2207 ≤ (21259184578551/50000000000000 : ℝ)^1695
        have hw : |(2592464349/5000000000 : ℝ)|=(2592464349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399139589/10000000000 : ℝ)|^2207 ≤ (22409863166793/50000000000000 : ℝ)^1695
        have hw : |(5399139589/10000000000 : ℝ)|=(5399139589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_9 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638229927/5000000000 : ℝ)*x 0 + (-1922396147/10000000000 : ℝ)*x 1 + (5399139491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638229927/5000000000 : ℝ)^2207 ≤ (43498281132117/100000000000000 : ℝ)^1695 := by
    have hnat : (2638229927 : ℕ)^2207*100000000000000^1695 ≤ 43498281132117^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638229927 5000000000 43498281132117 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1922396147/10000000000 : ℝ)^2207 ≤ (5840996787717/50000000000000 : ℝ)^1695 := by
    have hnat : (1922396147 : ℕ)^2207*50000000000000^1695 ≤ 5840996787717^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922396147 10000000000 5840996787717 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399139491/10000000000 : ℝ)^2207 ≤ (1792789010973/4000000000000 : ℝ)^1695 := by
    have hnat : (5399139491 : ℕ)^2207*4000000000000^1695 ≤ 1792789010973^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399139491 10000000000 1792789010973 4000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638229927/5000000000 : ℝ), (-1922396147/10000000000 : ℝ), (5399139491/10000000000 : ℝ)] ![(43498281132117/100000000000000 : ℝ), (5840996787717/50000000000000 : ℝ), (1792789010973/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638229927/5000000000 : ℝ)|^2207 ≤ (43498281132117/100000000000000 : ℝ)^1695
        have hw : |(2638229927/5000000000 : ℝ)|=(2638229927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1922396147/10000000000 : ℝ)|^2207 ≤ (5840996787717/50000000000000 : ℝ)^1695
        have hw : |(-1922396147/10000000000 : ℝ)|=(1922396147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399139491/10000000000 : ℝ)|^2207 ≤ (1792789010973/4000000000000 : ℝ)^1695
        have hw : |(5399139491/10000000000 : ℝ)|=(5399139491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_10 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276459843/10000000000 : ℝ)*x 0 + (2699569731/5000000000 : ℝ)*x 1 + (-961198101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276459843/10000000000 : ℝ)^2207 ≤ (43498281014043/100000000000000 : ℝ)^1695 := by
    have hnat : (5276459843 : ℕ)^2207*100000000000000^1695 ≤ 43498281014043^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276459843 10000000000 43498281014043 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699569731/5000000000 : ℝ)^2207 ≤ (4481972496087/10000000000000 : ℝ)^1695 := by
    have hnat : (2699569731 : ℕ)^2207*10000000000000^1695 ≤ 4481972496087^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699569731 5000000000 4481972496087 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961198101/5000000000 : ℝ)^2207 ≤ (2336398802123/20000000000000 : ℝ)^1695 := by
    have hnat : (961198101 : ℕ)^2207*20000000000000^1695 ≤ 2336398802123^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961198101 5000000000 2336398802123 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276459843/10000000000 : ℝ), (2699569731/5000000000 : ℝ), (-961198101/5000000000 : ℝ)] ![(43498281014043/100000000000000 : ℝ), (4481972496087/10000000000000 : ℝ), (2336398802123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276459843/10000000000 : ℝ)|^2207 ≤ (43498281014043/100000000000000 : ℝ)^1695
        have hw : |(5276459843/10000000000 : ℝ)|=(5276459843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699569731/5000000000 : ℝ)|^2207 ≤ (4481972496087/10000000000000 : ℝ)^1695
        have hw : |(2699569731/5000000000 : ℝ)|=(2699569731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-961198101/5000000000 : ℝ)|^2207 ≤ (2336398802123/20000000000000 : ℝ)^1695
        have hw : |(-961198101/5000000000 : ℝ)|=(961198101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_11 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2238972069/5000000000 : ℝ)*x 0 + (526455727/1250000000 : ℝ)*x 1 + (26322787/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238972069/5000000000 : ℝ)^2207 ≤ (35130294166953/100000000000000 : ℝ)^1695 := by
    have hnat : (2238972069 : ℕ)^2207*100000000000000^1695 ≤ 35130294166953^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238972069 5000000000 35130294166953 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526455727/1250000000 : ℝ)^2207 ≤ (16217426192393/50000000000000 : ℝ)^1695 := by
    have hnat : (526455727 : ℕ)^2207*50000000000000^1695 ≤ 16217426192393^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526455727 1250000000 16217426192393 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26322787/62500000 : ℝ)^2207 ≤ (16217426713823/50000000000000 : ℝ)^1695 := by
    have hnat : (26322787 : ℕ)^2207*50000000000000^1695 ≤ 16217426713823^1695*62500000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26322787 62500000 16217426713823 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238972069/5000000000 : ℝ), (526455727/1250000000 : ℝ), (26322787/62500000 : ℝ)] ![(35130294166953/100000000000000 : ℝ), (16217426192393/50000000000000 : ℝ), (16217426713823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238972069/5000000000 : ℝ)|^2207 ≤ (35130294166953/100000000000000 : ℝ)^1695
        have hw : |(2238972069/5000000000 : ℝ)|=(2238972069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526455727/1250000000 : ℝ)|^2207 ≤ (16217426192393/50000000000000 : ℝ)^1695
        have hw : |(526455727/1250000000 : ℝ)|=(526455727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26322787/62500000 : ℝ)|^2207 ≤ (16217426713823/50000000000000 : ℝ)^1695
        have hw : |(26322787/62500000 : ℝ)|=(26322787/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_12 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1859846393/10000000000 : ℝ)*x 0 + (2732574691/5000000000 : ℝ)*x 1 + (262786721/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1859846393/10000000000 : ℝ)^2207 ≤ (559476371697/5000000000000 : ℝ)^1695 := by
    have hnat : (1859846393 : ℕ)^2207*5000000000000^1695 ≤ 559476371697^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859846393 10000000000 559476371697 5000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732574691/5000000000 : ℝ)^2207 ≤ (45534526385099/100000000000000 : ℝ)^1695 := by
    have hnat : (2732574691 : ℕ)^2207*100000000000000^1695 ≤ 45534526385099^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732574691 5000000000 45534526385099 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262786721/500000000 : ℝ)^2207 ≤ (43275946166219/100000000000000 : ℝ)^1695 := by
    have hnat : (262786721 : ℕ)^2207*100000000000000^1695 ≤ 43275946166219^1695*500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262786721 500000000 43275946166219 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1859846393/10000000000 : ℝ), (2732574691/5000000000 : ℝ), (262786721/500000000 : ℝ)] ![(559476371697/5000000000000 : ℝ), (45534526385099/100000000000000 : ℝ), (43275946166219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1859846393/10000000000 : ℝ)|^2207 ≤ (559476371697/5000000000000 : ℝ)^1695
        have hw : |(-1859846393/10000000000 : ℝ)|=(1859846393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732574691/5000000000 : ℝ)|^2207 ≤ (45534526385099/100000000000000 : ℝ)^1695
        have hw : |(2732574691/5000000000 : ℝ)|=(2732574691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262786721/500000000 : ℝ)|^2207 ≤ (43275946166219/100000000000000 : ℝ)^1695
        have hw : |(262786721/500000000 : ℝ)|=(262786721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_13 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5376722187/10000000000 : ℝ)*x 0 + (-123802051/625000000 : ℝ)*x 1 + (2627867503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376722187/10000000000 : ℝ)^2207 ≤ (44577573328173/100000000000000 : ℝ)^1695 := by
    have hnat : (5376722187 : ℕ)^2207*100000000000000^1695 ≤ 44577573328173^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376722187 10000000000 44577573328173 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123802051/625000000 : ℝ)^2207 ≤ (12146474206983/100000000000000 : ℝ)^1695 := by
    have hnat : (123802051 : ℕ)^2207*100000000000000^1695 ≤ 12146474206983^1695*625000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123802051 625000000 12146474206983 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627867503/5000000000 : ℝ)^2207 ≤ (43275952448877/100000000000000 : ℝ)^1695 := by
    have hnat : (2627867503 : ℕ)^2207*100000000000000^1695 ≤ 43275952448877^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627867503 5000000000 43275952448877 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376722187/10000000000 : ℝ), (-123802051/625000000 : ℝ), (2627867503/5000000000 : ℝ)] ![(44577573328173/100000000000000 : ℝ), (12146474206983/100000000000000 : ℝ), (43275952448877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376722187/10000000000 : ℝ)|^2207 ≤ (44577573328173/100000000000000 : ℝ)^1695
        have hw : |(5376722187/10000000000 : ℝ)|=(5376722187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123802051/625000000 : ℝ)|^2207 ≤ (12146474206983/100000000000000 : ℝ)^1695
        have hw : |(-123802051/625000000 : ℝ)|=(123802051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627867503/5000000000 : ℝ)|^2207 ≤ (43275952448877/100000000000000 : ℝ)^1695
        have hw : |(2627867503/5000000000 : ℝ)|=(2627867503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_14 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2688361173/5000000000 : ℝ)*x 0 + (5255734317/10000000000 : ℝ)*x 1 + (-1980833527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688361173/5000000000 : ℝ)^2207 ≤ (44577575044613/100000000000000 : ℝ)^1695 := by
    have hnat : (2688361173 : ℕ)^2207*100000000000000^1695 ≤ 44577575044613^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688361173 5000000000 44577575044613 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255734317/10000000000 : ℝ)^2207 ≤ (4327594506193/10000000000000 : ℝ)^1695 := by
    have hnat : (5255734317 : ℕ)^2207*10000000000000^1695 ≤ 4327594506193^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255734317 10000000000 4327594506193 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980833527/10000000000 : ℝ)^2207 ≤ (12146479883797/100000000000000 : ℝ)^1695 := by
    have hnat : (1980833527 : ℕ)^2207*100000000000000^1695 ≤ 12146479883797^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980833527 10000000000 12146479883797 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688361173/5000000000 : ℝ), (5255734317/10000000000 : ℝ), (-1980833527/10000000000 : ℝ)] ![(44577575044613/100000000000000 : ℝ), (4327594506193/10000000000000 : ℝ), (12146479883797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688361173/5000000000 : ℝ)|^2207 ≤ (44577575044613/100000000000000 : ℝ)^1695
        have hw : |(2688361173/5000000000 : ℝ)|=(2688361173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255734317/10000000000 : ℝ)|^2207 ≤ (4327594506193/10000000000000 : ℝ)^1695
        have hw : |(5255734317/10000000000 : ℝ)|=(5255734317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980833527/10000000000 : ℝ)|^2207 ≤ (12146479883797/100000000000000 : ℝ)^1695
        have hw : |(-1980833527/10000000000 : ℝ)|=(1980833527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_box_15 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (412327177/1000000000 : ℝ)*x 0 + (877795629/2000000000 : ℝ)*x 1 + (4388977437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412327177/1000000000 : ℝ)^2207 ≤ (15775751896057/50000000000000 : ℝ)^1695 := by
    have hnat : (412327177 : ℕ)^2207*50000000000000^1695 ≤ 15775751896057^1695*1000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412327177 1000000000 15775751896057 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877795629/2000000000 : ℝ)^2207 ≤ (34224251692761/100000000000000 : ℝ)^1695 := by
    have hnat : (877795629 : ℕ)^2207*100000000000000^1695 ≤ 34224251692761^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877795629 2000000000 34224251692761 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388977437/10000000000 : ℝ)^2207 ≤ (34224244504291/100000000000000 : ℝ)^1695 := by
    have hnat : (4388977437 : ℕ)^2207*100000000000000^1695 ≤ 34224244504291^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388977437 10000000000 34224244504291 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412327177/1000000000 : ℝ), (877795629/2000000000 : ℝ), (4388977437/10000000000 : ℝ)] ![(15775751896057/50000000000000 : ℝ), (34224251692761/100000000000000 : ℝ), (34224244504291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412327177/1000000000 : ℝ)|^2207 ≤ (15775751896057/50000000000000 : ℝ)^1695
        have hw : |(412327177/1000000000 : ℝ)|=(412327177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877795629/2000000000 : ℝ)|^2207 ≤ (34224251692761/100000000000000 : ℝ)^1695
        have hw : |(877795629/2000000000 : ℝ)|=(877795629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4388977437/10000000000 : ℝ)|^2207 ≤ (34224244504291/100000000000000 : ℝ)^1695
        have hw : |(4388977437/10000000000 : ℝ)|=(4388977437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15729/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14791/25000 : ℝ) ∧ (16117/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42389/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11391/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (1718766818097289/20000000000000000000 : ℝ) := by
    have hpowers : (11391/100000 : ℝ)^4413 ≤ (1718766818097289/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11391 : ℕ)^4413*20000000000000000000^1024 ≤ 1718766818097289^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11391 100000 1718766818097289 20000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11391/100000 : ℝ)) (X := (1718766818097289/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (2631843855497783/10000000000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^4413 ≤ (2631843855497783/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14769 : ℕ)^4413*10000000000000000000^1024 ≤ 2631843855497783^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 2631843855497783 10000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (2631843855497783/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001718766818097289/10000000000000000000 : ℝ) ≤ (5000199399623559/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (10001718766818097289/10000000000000000000 : ℝ)^1024 ≤ (5000199399623559/5000000000000000 : ℝ)^4413 := by
      have hnat : (10001718766818097289 : ℕ)^1024*5000000000000000^4413 ≤ 5000199399623559^4413*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001718766818097289 10000000000000000000 5000199399623559 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000199399623559/5000000000000000 : ℝ)) (X := (10001718766818097289/10000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001396490905818571/4000000000000000000 : ℝ) ≤ (625050625107149/625000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (4001396490905818571/4000000000000000000 : ℝ)^1024 ≤ (625050625107149/625000000000000 : ℝ)^4413 := by
      have hnat : (4001396490905818571 : ℕ)^1024*625000000000000^4413 ≤ 625050625107149^4413*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001396490905818571 4000000000000000000 625050625107149 625000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625050625107149/625000000000000 : ℝ)) (X := (4001396490905818571/4000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002631843855497783/5000000000000000000 : ℝ) ≤ (200024424083633/200000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (5002631843855497783/5000000000000000000 : ℝ)^1024 ≤ (200024424083633/200000000000000 : ℝ)^4413 := by
      have hnat : (5002631843855497783 : ℕ)^1024*200000000000000^4413 ≤ 200024424083633^4413*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002631843855497783 5000000000000000000 200024424083633 200000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200024424083633/200000000000000 : ℝ)) (X := (5002631843855497783/5000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1718766818097289/20000000000000000000 : ℝ) ≤ ((175895724631497451/175937500000000000 : ℝ)+2*(205601233633/168900000000000 : ℝ)*(11391/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (175895724631497451/175937500000000000 : ℝ)+2*(205601233633/168900000000000 : ℝ)*(11391/100000 : ℝ)=(5000199399623559/5000000000000000 : ℝ) by norm_num, show 1+2*(1718766818097289/20000000000000000000 : ℝ)=(10001718766818097289/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2631843855497783/10000000000000000000 : ℝ)+(1718766818097289/20000000000000000000 : ℝ) ≤ ((175895724631497451/175937500000000000 : ℝ)+(205601233633/168900000000000 : ℝ)*((14769/100000 : ℝ)+(11391/100000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (175895724631497451/175937500000000000 : ℝ)+(205601233633/168900000000000 : ℝ)*((14769/100000 : ℝ)+(11391/100000 : ℝ))=(625050625107149/625000000000000 : ℝ) by norm_num, show 1+(2631843855497783/10000000000000000000 : ℝ)+(1718766818097289/20000000000000000000 : ℝ)=(4001396490905818571/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2631843855497783/10000000000000000000 : ℝ) ≤ ((175895724631497451/175937500000000000 : ℝ)+2*(205601233633/168900000000000 : ℝ)*(14769/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (175895724631497451/175937500000000000 : ℝ)+2*(205601233633/168900000000000 : ℝ)*(14769/100000 : ℝ)=(200024424083633/200000000000000 : ℝ) by norm_num, show 1+2*(2631843855497783/10000000000000000000 : ℝ)=(5002631843855497783/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (175895724631497451/175937500000000000 : ℝ)*(X 1 0+X 2 0)+(205601233633/168900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (175895724631497451/175937500000000000 : ℝ)) (alpha := (205601233633/168900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (175895724631497451/175937500000000000 : ℝ)*(X 0 1+X 2 1)+(205601233633/168900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (175895724631497451/175937500000000000 : ℝ)) (alpha := (205601233633/168900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (175895724631497451/175937500000000000 : ℝ)*(X 0 2+X 1 2)+(205601233633/168900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (175895724631497451/175937500000000000 : ℝ)) (alpha := (205601233633/168900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1750148/9765625 : ℝ)*X 0 0+(336573857/625000000 : ℝ)*X 0 1+(673147701/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643110911/5000000000 : ℝ)*X 1 0+(-1928206433/10000000000 : ℝ)*X 1 1+(5385181653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286221919/10000000000 : ℝ)*X 2 0+(1346295411/2500000000 : ℝ)*X 2 1+(-964103157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2221984509/5000000000 : ℝ)*X 0 0+(825961/1953125 : ℝ)*X 0 1+(2114460249/5000000000 : ℝ)*X 0 2+(2221984509/5000000000 : ℝ)*X 1 0+(825961/1953125 : ℝ)*X 1 1+(2114460249/5000000000 : ℝ)*X 1 2+(2221984509/5000000000 : ℝ)*X 2 0+(825961/1953125 : ℝ)*X 2 1+(2114460249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2112631579/10000000000 : ℝ)*X 0 0+(5266872427/10000000000 : ℝ)*X 0 1+(5266872229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684468403/5000000000 : ℝ)*X 1 0+(-1976395101/10000000000 : ℝ)*X 1 1+(5266872523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1342234191/2500000000 : ℝ)*X 2 0+(1053374451/2000000000 : ℝ)*X 2 1+(-988197759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2075637399/5000000000 : ℝ)*X 0 0+(4375217339/10000000000 : ℝ)*X 0 1+(2187608661/5000000000 : ℝ)*X 0 2+(2075637399/5000000000 : ℝ)*X 1 0+(4375217339/10000000000 : ℝ)*X 1 1+(2187608661/5000000000 : ℝ)*X 1 2+(2075637399/5000000000 : ℝ)*X 2 0+(4375217339/10000000000 : ℝ)*X 2 1+(2187608661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-409015243/2000000000 : ℝ)*X 0 0+(2592464349/5000000000 : ℝ)*X 0 1+(5399139589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638229927/5000000000 : ℝ)*X 1 0+(-1922396147/10000000000 : ℝ)*X 1 1+(5399139491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276459843/10000000000 : ℝ)*X 2 0+(2699569731/5000000000 : ℝ)*X 2 1+(-961198101/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2238972069/5000000000 : ℝ)*X 0 0+(526455727/1250000000 : ℝ)*X 0 1+(26322787/62500000 : ℝ)*X 0 2+(2238972069/5000000000 : ℝ)*X 1 0+(526455727/1250000000 : ℝ)*X 1 1+(26322787/62500000 : ℝ)*X 1 2+(2238972069/5000000000 : ℝ)*X 2 0+(526455727/1250000000 : ℝ)*X 2 1+(26322787/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1859846393/10000000000 : ℝ)*X 0 0+(2732574691/5000000000 : ℝ)*X 0 1+(262786721/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5376722187/10000000000 : ℝ)*X 1 0+(-123802051/625000000 : ℝ)*X 1 1+(2627867503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688361173/5000000000 : ℝ)*X 2 0+(5255734317/10000000000 : ℝ)*X 2 1+(-1980833527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((412327177/1000000000 : ℝ)*X 0 0+(877795629/2000000000 : ℝ)*X 0 1+(4388977437/10000000000 : ℝ)*X 0 2+(412327177/1000000000 : ℝ)*X 1 0+(877795629/2000000000 : ℝ)*X 1 1+(4388977437/10000000000 : ℝ)*X 1 2+(412327177/1000000000 : ℝ)*X 2 0+(877795629/2000000000 : ℝ)*X 2 1+(4388977437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15729/25000 : ℝ) ≤ (-2767191234006172173862069206053/4398437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (46210401/100000000000000 : ℝ)*(upper1) + (49962497/50000000000000 : ℝ)*(upper2) + (9243911/10000000000000 : ℝ)*(upper3) + (23162507/50000000000000 : ℝ)*(lower4) + (17333351/50000000000000 : ℝ)*(upper5) + (3043977284670401/100000000000000 : ℝ)*(major0) + (3043977284670401/100000000000000 : ℝ)*(major1) + (3043977284670401/100000000000000 : ℝ)*(major2) + (1806186471/20000000000000 : ℝ)*(sp2) + (4196378326566557/100000000000000 : ℝ)*(sp4) + (4196309060846707/100000000000000 : ℝ)*(sp5) + (2098184647817101/50000000000000 : ℝ)*(sp6) + (382509451964591/20000000000000 : ℝ)*(sp7) + (1385314397/2000000000000 : ℝ)*(sp13) + (382509451964591/20000000000000 : ℝ)*(f.failure) + (4196378326566557/100000000000000 : ℝ)*(f.sum) + (21792387270191/4222500000000000000000000000 : ℝ)*base66 + (1590660007101661/26390625000000000000000000000000 : ℝ)*base68 + (102631127310603491/6597656250000000000000000000000 : ℝ)*base69 + (42699213800367089/26390625000000000000000000000000 : ℝ)*base71 + (21179785455577/8445000000000000000000000000 : ℝ)*base74 + (8157787146632077/824707031250000000000000000000 : ℝ)*base75 + (3658975996540991/6597656250000000000000000000000 : ℝ)*base77 + (10189397326262683/3298828125000000000000000000000 : ℝ)*base79 + (63825949035053/8445000000000000000000000000 : ℝ)*base81 + (267149/1000000000000000000000 : ℝ)*base89 + (267149/1000000000000000000000 : ℝ)*base91 + (267149/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14791/25000 : ℝ) ≤ (5204770919071223626776704809209/8796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82026219/100000000000000 : ℝ)*(upper0) + (34583827/50000000000000 : ℝ)*(upper2) + (6593879/10000000000000 : ℝ)*(upper3) + (146904541/100000000000000 : ℝ)*(upper4) + (47745731/100000000000000 : ℝ)*(upper5) + (1558209075889143/50000000000000 : ℝ)*(major0) + (1558209075889143/50000000000000 : ℝ)*(major1) + (1558209075889143/50000000000000 : ℝ)*(major2) + (265940750833451/6250000000000 : ℝ)*(sp0) + (1063754622548641/25000000000000 : ℝ)*(sp1) + (265940722591097/6250000000000 : ℝ)*(sp2) + (979031122647069/50000000000000 : ℝ)*(sp3) + (90375533/20000000000000 : ℝ)*(sp6) + (33523140653/100000000000000 : ℝ)*(sp9) + (979031122647069/50000000000000 : ℝ)*(f.failure) + (265940750833451/6250000000000 : ℝ)*(f.sum) + (2436956919983/1407500000000000000000000000 : ℝ)*base65 + (19914633213317441/4398437500000000000000000000000 : ℝ)*base68 + (64965120081213809/4398437500000000000000000000000 : ℝ)*base69 + (2971426428065171/1099609375000000000000000000000 : ℝ)*base71 + (36812823035391/2815000000000000000000000000 : ℝ)*base73 + (20223931842411993/8796875000000000000000000000000 : ℝ)*base75 + (44315217916057559/4398437500000000000000000000000 : ℝ)*base77 + (153442561345661993/8796875000000000000000000000000 : ℝ)*base79 + (637248693291/175937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1893591/2500000000000000000000 : ℝ)*base89 + (1893591/2500000000000000000000 : ℝ)*base91 + (1893591/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16117/20000 : ℝ) ≤ (22153744674774235742851803467/27490234375000000000000000000 : ℝ) := by norm_num
    linear_combination (14136191/50000000000000 : ℝ)*(upper0) + (13529279/100000000000000 : ℝ)*(lower1) + (5135127/100000000000000 : ℝ)*(upper2) + (53599077/100000000000000 : ℝ)*(lower3) + (12338717/12500000000000 : ℝ)*(lower5) + (85572251446613/2500000000000 : ℝ)*(major0) + (85572251446613/2500000000000 : ℝ)*(major1) + (85572251446613/2500000000000 : ℝ)*(major2) + (4069010993/100000000000000 : ℝ)*(sp0) + (25251799051/100000000000000 : ℝ)*(sp3) + (466829329540419/10000000000000 : ℝ)*(sp8) + (291768585275949/6250000000000 : ℝ)*(sp9) + (291768585275949/6250000000000 : ℝ)*(sp10) + (537648734101029/25000000000000 : ℝ)*(sp11) + (2150620188203167/100000000000000 : ℝ)*(f.failure) + (291768585275949/6250000000000 : ℝ)*(f.sum) + (750678230893/422250000000000000000000000 : ℝ)*base65 + (40802215168944139/1319531250000000000000000000000 : ℝ)*base67 + (22978845847662889/1319531250000000000000000000000 : ℝ)*base69 + (10451089567497653/2639062500000000000000000000000 : ℝ)*base71 + (283024540229/42225000000000000000000000 : ℝ)*base74 + (11614873100627347/2639062500000000000000000000000 : ℝ)*base76 + (13112760979272653/2639062500000000000000000000000 : ℝ)*base77 + (1249356314866993/659765625000000000000000000000 : ℝ)*base80 + (112997608841/844500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (13066787/5000000000000000000000 : ℝ)*base90 + (13066787/5000000000000000000000 : ℝ)*base92 + (13066787/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42389/50000 : ℝ) ≤ (-1864398514265092529579219439123/2199218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (79758791/100000000000000 : ℝ)*(lower0) + (288662479/100000000000000 : ℝ)*(upper3) + (71711601/50000000000000 : ℝ)*(lower4) + (1730332796270091/50000000000000 : ℝ)*(major0) + (1730332796270091/50000000000000 : ℝ)*(major1) + (1730332796270091/50000000000000 : ℝ)*(major2) + (8841417889/50000000000000 : ℝ)*(sp0) + (2134524677/1000000000000 : ℝ)*(sp5) + (123796241459/25000000000000 : ℝ)*(sp6) + (41078192123/100000000000000 : ℝ)*(sp7) + (2387608620121271/50000000000000 : ℝ)*(sp12) + (4775021470610619/100000000000000 : ℝ)*(sp13) + (4774739738112483/100000000000000 : ℝ)*(sp14) + (2174313681125003/100000000000000 : ℝ)*(sp15) + (1087177379658563/50000000000000 : ℝ)*(f.failure) + (59690436538479/1250000000000 : ℝ)*(f.sum) + (667195332443/703750000000000000000000000 : ℝ)*base65 + (54231827605645583/4398437500000000000000000000000 : ℝ)*base67 + (16882114711318209/8796875000000000000000000000000 : ℝ)*base70 + (41357835184494291/8796875000000000000000000000000 : ℝ)*base71 + (570613188959/1407500000000000000000000000 : ℝ)*base74 + (70726234797275541/8796875000000000000000000000000 : ℝ)*base75 + (4795734435783729/2199218750000000000000000000000 : ℝ)*base77 + (174139731319213041/8796875000000000000000000000000 : ℝ)*base79 + (4048689253959/1407500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7517257/2500000000000000000000 : ℝ)*base89 + (7517257/2500000000000000000000 : ℝ)*base91 + (7517257/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1454_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15729/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14791/25000 : ℝ) else (16117/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42389/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1454_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1454_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15729/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14791/25000 : ℝ) else (16117/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42389/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1454_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1454_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1454_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15729/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14791/25000 : ℝ) else (16117/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42389/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
