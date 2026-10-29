-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:00:23.02986+00:00
-- url     : https://prove2.me/submissions/dd7b9e8a-ee80-4cf1-bf76-49f49a377093

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
theorem support_rectangle_w1454_s3_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-487528083/2500000000 : ℝ)*x 0 + (5414834521/10000000000 : ℝ)*x 1 + (5240135921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487528083/2500000000 : ℝ)^2207 ≤ (2380354056889/20000000000000 : ℝ)^1695 := by
    have hnat : (487528083 : ℕ)^2207*20000000000000^1695 ≤ 2380354056889^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487528083 2500000000 2380354056889 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414834521/10000000000 : ℝ)^2207 ≤ (11247361016071/25000000000000 : ℝ)^1695 := by
    have hnat : (5414834521 : ℕ)^2207*25000000000000^1695 ≤ 11247361016071^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414834521 10000000000 11247361016071 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240135921/10000000000 : ℝ)^2207 ≤ (21554392816109/50000000000000 : ℝ)^1695 := by
    have hnat : (5240135921 : ℕ)^2207*50000000000000^1695 ≤ 21554392816109^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240135921 10000000000 21554392816109 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487528083/2500000000 : ℝ), (5414834521/10000000000 : ℝ), (5240135921/10000000000 : ℝ)] ![(2380354056889/20000000000000 : ℝ), (11247361016071/25000000000000 : ℝ), (21554392816109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487528083/2500000000 : ℝ)|^2207 ≤ (2380354056889/20000000000000 : ℝ)^1695
        have hw : |(-487528083/2500000000 : ℝ)|=(487528083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414834521/10000000000 : ℝ)|^2207 ≤ (11247361016071/25000000000000 : ℝ)^1695
        have hw : |(5414834521/10000000000 : ℝ)|=(5414834521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240135921/10000000000 : ℝ)|^2207 ≤ (21554392816109/50000000000000 : ℝ)^1695
        have hw : |(5240135921/10000000000 : ℝ)|=(5240135921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s3_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674418341/5000000000 : ℝ)*x 0 + (-2039185301/10000000000 : ℝ)*x 1 + (262006797/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674418341/5000000000 : ℝ)^2207 ≤ (44276779278977/100000000000000 : ℝ)^1695 := by
    have hnat : (2674418341 : ℕ)^2207*100000000000000^1695 ≤ 44276779278977^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674418341 5000000000 44276779278977 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039185301/10000000000 : ℝ)^2207 ≤ (3153608718443/25000000000000 : ℝ)^1695 := by
    have hnat : (2039185301 : ℕ)^2207*25000000000000^1695 ≤ 3153608718443^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039185301 10000000000 3153608718443 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262006797/500000000 : ℝ)^2207 ≤ (43108785835739/100000000000000 : ℝ)^1695 := by
    have hnat : (262006797 : ℕ)^2207*100000000000000^1695 ≤ 43108785835739^1695*500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262006797 500000000 43108785835739 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674418341/5000000000 : ℝ), (-2039185301/10000000000 : ℝ), (262006797/500000000 : ℝ)] ![(44276779278977/100000000000000 : ℝ), (3153608718443/25000000000000 : ℝ), (43108785835739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674418341/5000000000 : ℝ)|^2207 ≤ (44276779278977/100000000000000 : ℝ)^1695
        have hw : |(2674418341/5000000000 : ℝ)|=(2674418341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039185301/10000000000 : ℝ)|^2207 ≤ (3153608718443/25000000000000 : ℝ)^1695
        have hw : |(-2039185301/10000000000 : ℝ)|=(2039185301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262006797/500000000 : ℝ)|^2207 ≤ (43108785835739/100000000000000 : ℝ)^1695
        have hw : |(262006797/500000000 : ℝ)|=(262006797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s3_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674418371/5000000000 : ℝ)*x 0 + (2620067907/5000000000 : ℝ)*x 1 + (-509796347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674418371/5000000000 : ℝ)^2207 ≤ (44276779925673/100000000000000 : ℝ)^1695 := by
    have hnat : (2674418371 : ℕ)^2207*100000000000000^1695 ≤ 44276779925673^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674418371 5000000000 44276779925673 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620067907/5000000000 : ℝ)^2207 ≤ (43108784486073/100000000000000 : ℝ)^1695 := by
    have hnat : (2620067907 : ℕ)^2207*100000000000000^1695 ≤ 43108784486073^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620067907 5000000000 43108784486073 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509796347/2500000000 : ℝ)^2207 ≤ (6307217787261/50000000000000 : ℝ)^1695 := by
    have hnat : (509796347 : ℕ)^2207*50000000000000^1695 ≤ 6307217787261^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509796347 2500000000 6307217787261 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674418371/5000000000 : ℝ), (2620067907/5000000000 : ℝ), (-509796347/2500000000 : ℝ)] ![(44276779925673/100000000000000 : ℝ), (43108784486073/100000000000000 : ℝ), (6307217787261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674418371/5000000000 : ℝ)|^2207 ≤ (44276779925673/100000000000000 : ℝ)^1695
        have hw : |(2674418371/5000000000 : ℝ)|=(2674418371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620067907/5000000000 : ℝ)|^2207 ≤ (43108784486073/100000000000000 : ℝ)^1695
        have hw : |(2620067907/5000000000 : ℝ)|=(2620067907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-509796347/2500000000 : ℝ)|^2207 ≤ (6307217787261/50000000000000 : ℝ)^1695
        have hw : |(-509796347/2500000000 : ℝ)|=(509796347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s3_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297602287/10000000000 : ℝ)*x 0 + (4110667309/10000000000 : ℝ)*x 1 + (4492064069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297602287/10000000000 : ℝ)^2207 ≤ (16649712668131/50000000000000 : ℝ)^1695 := by
    have hnat : (4297602287 : ℕ)^2207*50000000000000^1695 ≤ 16649712668131^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297602287 10000000000 16649712668131 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4110667309/10000000000 : ℝ)^2207 ≤ (7856494403039/25000000000000 : ℝ)^1695 := by
    have hnat : (4110667309 : ℕ)^2207*25000000000000^1695 ≤ 7856494403039^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110667309 10000000000 7856494403039 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492064069/10000000000 : ℝ)^2207 ≤ (17637298514849/50000000000000 : ℝ)^1695 := by
    have hnat : (4492064069 : ℕ)^2207*50000000000000^1695 ≤ 17637298514849^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492064069 10000000000 17637298514849 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297602287/10000000000 : ℝ), (4110667309/10000000000 : ℝ), (4492064069/10000000000 : ℝ)] ![(16649712668131/50000000000000 : ℝ), (7856494403039/25000000000000 : ℝ), (17637298514849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297602287/10000000000 : ℝ)|^2207 ≤ (16649712668131/50000000000000 : ℝ)^1695
        have hw : |(4297602287/10000000000 : ℝ)|=(4297602287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4110667309/10000000000 : ℝ)|^2207 ≤ (7856494403039/25000000000000 : ℝ)^1695
        have hw : |(4110667309/10000000000 : ℝ)|=(4110667309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492064069/10000000000 : ℝ)|^2207 ≤ (17637298514849/50000000000000 : ℝ)^1695
        have hw : |(4492064069/10000000000 : ℝ)|=(4492064069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s3_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950126341/10000000000 : ℝ)*x 0 + (524082737/1000000000 : ℝ)*x 1 + (5414139571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950126341/10000000000 : ℝ)^2207 ≤ (11901881609309/100000000000000 : ℝ)^1695 := by
    have hnat : (1950126341 : ℕ)^2207*100000000000000^1695 ≤ 11901881609309^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950126341 10000000000 11901881609309 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524082737/1000000000 : ℝ)^2207 ≤ (43116192330867/100000000000000 : ℝ)^1695 := by
    have hnat : (524082737 : ℕ)^2207*100000000000000^1695 ≤ 43116192330867^1695*1000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524082737 1000000000 43116192330867 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414139571/10000000000 : ℝ)^2207 ≤ (1124548151223/2500000000000 : ℝ)^1695 := by
    have hnat : (5414139571 : ℕ)^2207*2500000000000^1695 ≤ 1124548151223^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414139571 10000000000 1124548151223 2500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950126341/10000000000 : ℝ), (524082737/1000000000 : ℝ), (5414139571/10000000000 : ℝ)] ![(11901881609309/100000000000000 : ℝ), (43116192330867/100000000000000 : ℝ), (1124548151223/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950126341/10000000000 : ℝ)|^2207 ≤ (11901881609309/100000000000000 : ℝ)^1695
        have hw : |(-1950126341/10000000000 : ℝ)|=(1950126341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524082737/1000000000 : ℝ)|^2207 ≤ (43116192330867/100000000000000 : ℝ)^1695
        have hw : |(524082737/1000000000 : ℝ)|=(524082737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414139571/10000000000 : ℝ)|^2207 ≤ (1124548151223/2500000000000 : ℝ)^1695
        have hw : |(5414139571/10000000000 : ℝ)|=(5414139571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s3_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060662339/2000000000 : ℝ)*x 0 + (-466295523/2500000000 : ℝ)*x 1 + (1082827909/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060662339/2000000000 : ℝ)^2207 ≤ (8757346078893/20000000000000 : ℝ)^1695 := by
    have hnat : (1060662339 : ℕ)^2207*20000000000000^1695 ≤ 8757346078893^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060662339 2000000000 8757346078893 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466295523/2500000000 : ℝ)^2207 ≤ (701958989571/6250000000000 : ℝ)^1695 := by
    have hnat : (466295523 : ℕ)^2207*6250000000000^1695 ≤ 701958989571^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466295523 2500000000 701958989571 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082827909/2000000000 : ℝ)^2207 ≤ (5622740720957/12500000000000 : ℝ)^1695 := by
    have hnat : (1082827909 : ℕ)^2207*12500000000000^1695 ≤ 5622740720957^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082827909 2000000000 5622740720957 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060662339/2000000000 : ℝ), (-466295523/2500000000 : ℝ), (1082827909/2000000000 : ℝ)] ![(8757346078893/20000000000000 : ℝ), (701958989571/6250000000000 : ℝ), (5622740720957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060662339/2000000000 : ℝ)|^2207 ≤ (8757346078893/20000000000000 : ℝ)^1695
        have hw : |(1060662339/2000000000 : ℝ)|=(1060662339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466295523/2500000000 : ℝ)|^2207 ≤ (701958989571/6250000000000 : ℝ)^1695
        have hw : |(-466295523/2500000000 : ℝ)|=(466295523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082827909/2000000000 : ℝ)|^2207 ≤ (5622740720957/12500000000000 : ℝ)^1695
        have hw : |(1082827909/2000000000 : ℝ)|=(1082827909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s3_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26516553/50000000 : ℝ)*x 0 + (5414140401/10000000000 : ℝ)*x 1 + (-1865182411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26516553/50000000 : ℝ)^2207 ≤ (21893359311343/50000000000000 : ℝ)^1695 := by
    have hnat : (26516553 : ℕ)^2207*50000000000000^1695 ≤ 21893359311343^1695*50000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26516553 50000000 21893359311343 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414140401/10000000000 : ℝ)^2207 ≤ (22490967513871/50000000000000 : ℝ)^1695 := by
    have hnat : (5414140401 : ℕ)^2207*50000000000000^1695 ≤ 22490967513871^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414140401 10000000000 22490967513871 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865182411/10000000000 : ℝ)^2207 ≤ (11231346334251/100000000000000 : ℝ)^1695 := by
    have hnat : (1865182411 : ℕ)^2207*100000000000000^1695 ≤ 11231346334251^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865182411 10000000000 11231346334251 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26516553/50000000 : ℝ), (5414140401/10000000000 : ℝ), (-1865182411/10000000000 : ℝ)] ![(21893359311343/50000000000000 : ℝ), (22490967513871/50000000000000 : ℝ), (11231346334251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26516553/50000000 : ℝ)|^2207 ≤ (21893359311343/50000000000000 : ℝ)^1695
        have hw : |(26516553/50000000 : ℝ)|=(26516553/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414140401/10000000000 : ℝ)|^2207 ≤ (22490967513871/50000000000000 : ℝ)^1695
        have hw : |(5414140401/10000000000 : ℝ)|=(5414140401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865182411/10000000000 : ℝ)|^2207 ≤ (11231346334251/100000000000000 : ℝ)^1695
        have hw : |(-1865182411/10000000000 : ℝ)|=(1865182411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s3_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (859526619/2000000000 : ℝ)*x 0 + (898111023/2000000000 : ℝ)*x 1 + (514023233/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859526619/2000000000 : ℝ)^2207 ≤ (665994723099/2000000000000 : ℝ)^1695 := by
    have hnat : (859526619 : ℕ)^2207*2000000000000^1695 ≤ 665994723099^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859526619 2000000000 665994723099 2000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898111023/2000000000 : ℝ)^2207 ≤ (35259169275363/100000000000000 : ℝ)^1695 := by
    have hnat : (898111023 : ℕ)^2207*100000000000000^1695 ≤ 35259169275363^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898111023 2000000000 35259169275363 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514023233/1250000000 : ℝ)^2207 ≤ (15720547275439/50000000000000 : ℝ)^1695 := by
    have hnat : (514023233 : ℕ)^2207*50000000000000^1695 ≤ 15720547275439^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514023233 1250000000 15720547275439 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859526619/2000000000 : ℝ), (898111023/2000000000 : ℝ), (514023233/1250000000 : ℝ)] ![(665994723099/2000000000000 : ℝ), (35259169275363/100000000000000 : ℝ), (15720547275439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859526619/2000000000 : ℝ)|^2207 ≤ (665994723099/2000000000000 : ℝ)^1695
        have hw : |(859526619/2000000000 : ℝ)|=(859526619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898111023/2000000000 : ℝ)|^2207 ≤ (35259169275363/100000000000000 : ℝ)^1695
        have hw : |(898111023/2000000000 : ℝ)|=(898111023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514023233/1250000000 : ℝ)|^2207 ≤ (15720547275439/50000000000000 : ℝ)^1695
        have hw : |(514023233/1250000000 : ℝ)|=(514023233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2987/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7863/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7863/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7863/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7863/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7863/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7863/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10497/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (3021215056156323/50000000000000000000 : ℝ) := by
    have hpowers : (10497/100000 : ℝ)^4413 ≤ (3021215056156323/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10497 : ℕ)^4413*50000000000000000000^1024 ≤ 3021215056156323^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10497 100000 3021215056156323 50000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10497/100000 : ℝ)) (X := (3021215056156323/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7863/50000 : ℝ) ^ (4413/1024 : ℝ) ≤ (1724804818821839/5000000000000000000 : ℝ) := by
    have hpowers : (7863/50000 : ℝ)^4413 ≤ (1724804818821839/5000000000000000000 : ℝ)^1024 := by
      have hnat : (7863 : ℕ)^4413*5000000000000000000^1024 ≤ 1724804818821839^1024*50000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7863 50000 1724804818821839 5000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7863/50000 : ℝ)) (X := (1724804818821839/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003021215056156323/25000000000000000000 : ℝ) ≤ (156254381345837/156250000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (25003021215056156323/25000000000000000000 : ℝ)^1024 ≤ (156254381345837/156250000000000 : ℝ)^4413 := by
      have hnat : (25003021215056156323 : ℕ)^1024*156250000000000^4413 ≤ 156254381345837^4413*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003021215056156323 25000000000000000000 156254381345837 156250000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156254381345837/156250000000000 : ℝ)) (X := (25003021215056156323/25000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020269263244374713/50000000000000000000 : ℝ) ≤ (5000470258225883/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (50020269263244374713/50000000000000000000 : ℝ)^1024 ≤ (5000470258225883/5000000000000000 : ℝ)^4413 := by
      have hnat : (50020269263244374713 : ℕ)^1024*5000000000000000^4413 ≤ 5000470258225883^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020269263244374713 50000000000000000000 5000470258225883 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000470258225883/5000000000000000 : ℝ)) (X := (50020269263244374713/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501724804818821839/2500000000000000000 : ℝ) ≤ (2500400156692491/2500000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (2501724804818821839/2500000000000000000 : ℝ)^1024 ≤ (2500400156692491/2500000000000000 : ℝ)^4413 := by
      have hnat : (2501724804818821839 : ℕ)^1024*2500000000000000^4413 ≤ 2500400156692491^4413*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501724804818821839 2500000000000000000 2500400156692491 2500000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500400156692491/2500000000000000 : ℝ)) (X := (2501724804818821839/2500000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3021215056156323/50000000000000000000 : ℝ) ≤ ((871293464794202971/871500000000000000 : ℝ)+2*(330055159099/261450000000000 : ℝ)*(10497/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (871293464794202971/871500000000000000 : ℝ)+2*(330055159099/261450000000000 : ℝ)*(10497/100000 : ℝ)=(156254381345837/156250000000000 : ℝ) by norm_num, show 1+2*(3021215056156323/50000000000000000000 : ℝ)=(25003021215056156323/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1724804818821839/5000000000000000000 : ℝ)+(3021215056156323/50000000000000000000 : ℝ) ≤ ((871293464794202971/871500000000000000 : ℝ)+(330055159099/261450000000000 : ℝ)*((7863/50000 : ℝ)+(10497/100000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (871293464794202971/871500000000000000 : ℝ)+(330055159099/261450000000000 : ℝ)*((7863/50000 : ℝ)+(10497/100000 : ℝ))=(5000470258225883/5000000000000000 : ℝ) by norm_num, show 1+(1724804818821839/5000000000000000000 : ℝ)+(3021215056156323/50000000000000000000 : ℝ)=(50020269263244374713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1724804818821839/5000000000000000000 : ℝ) ≤ ((871293464794202971/871500000000000000 : ℝ)+2*(330055159099/261450000000000 : ℝ)*(7863/50000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (871293464794202971/871500000000000000 : ℝ)+2*(330055159099/261450000000000 : ℝ)*(7863/50000 : ℝ)=(2500400156692491/2500000000000000 : ℝ) by norm_num, show 1+2*(1724804818821839/5000000000000000000 : ℝ)=(2501724804818821839/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (871293464794202971/871500000000000000 : ℝ)*(X 1 0+X 2 0)+(330055159099/261450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (7863/50000 : ℝ)) (c := (871293464794202971/871500000000000000 : ℝ)) (alpha := (330055159099/261450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (871293464794202971/871500000000000000 : ℝ)*(X 0 1+X 2 1)+(330055159099/261450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (7863/50000 : ℝ)) (c := (871293464794202971/871500000000000000 : ℝ)) (alpha := (330055159099/261450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (871293464794202971/871500000000000000 : ℝ)*(X 0 2+X 1 2)+(330055159099/261450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (7863/50000 : ℝ)) (c := (871293464794202971/871500000000000000 : ℝ)) (alpha := (330055159099/261450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-487528083/2500000000 : ℝ)*X 0 0+(5414834521/10000000000 : ℝ)*X 0 1+(5240135921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674418341/5000000000 : ℝ)*X 1 0+(-2039185301/10000000000 : ℝ)*X 1 1+(262006797/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674418371/5000000000 : ℝ)*X 2 0+(2620067907/5000000000 : ℝ)*X 2 1+(-509796347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297602287/10000000000 : ℝ)*X 0 0+(4110667309/10000000000 : ℝ)*X 0 1+(4492064069/10000000000 : ℝ)*X 0 2+(4297602287/10000000000 : ℝ)*X 1 0+(4110667309/10000000000 : ℝ)*X 1 1+(4492064069/10000000000 : ℝ)*X 1 2+(4297602287/10000000000 : ℝ)*X 2 0+(4110667309/10000000000 : ℝ)*X 2 1+(4492064069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1950126341/10000000000 : ℝ)*X 0 0+(524082737/1000000000 : ℝ)*X 0 1+(5414139571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060662339/2000000000 : ℝ)*X 1 0+(-466295523/2500000000 : ℝ)*X 1 1+(1082827909/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26516553/50000000 : ℝ)*X 2 0+(5414140401/10000000000 : ℝ)*X 2 1+(-1865182411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859526619/2000000000 : ℝ)*X 0 0+(898111023/2000000000 : ℝ)*X 0 1+(514023233/1250000000 : ℝ)*X 0 2+(859526619/2000000000 : ℝ)*X 1 0+(898111023/2000000000 : ℝ)*X 1 1+(514023233/1250000000 : ℝ)*X 1 2+(859526619/2000000000 : ℝ)*X 2 0+(898111023/2000000000 : ℝ)*X 2 1+(514023233/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2204441704580282649965307/259375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (518763047/25000000000000 : ℝ)*(base19) + (422784237/20000000000000 : ℝ)*(base23) + (1355497/10000000000000 : ℝ)*(lower2) + (28827893/10000000000000 : ℝ)*(upper3) + (176647887/100000000000000 : ℝ)*(upper5) + (521638444746797/12500000000000 : ℝ)*(major0) + (521638444746797/12500000000000 : ℝ)*(major1) + (521638444746797/12500000000000 : ℝ)*(major2) + (572418814335657/10000000000000 : ℝ)*(sp0) + (572422688892741/10000000000000 : ℝ)*(sp1) + (2862113425029207/50000000000000 : ℝ)*(sp2) + (2621962687004823/100000000000000 : ℝ)*(sp3) + (10205155757/25000000000000 : ℝ)*(sp4) + (11590831289/50000000000000 : ℝ)*(sp7) + (2621985868667401/100000000000000 : ℝ)*(f.failure) + (2862114481989799/50000000000000 : ℝ)*(f.sum) + (10384432109341/3735000000000000000000000000 : ℝ)*base66 + (1317741056601727/4668750000000000000000000000000 : ℝ)*base68 + (68225350002914227/4668750000000000000000000000000 : ℝ)*base70 + (56766877001151727/4668750000000000000000000000000 : ℝ)*base72 + (12514964776319/3735000000000000000000000000 : ℝ)*base73 + (23024792427248273/4668750000000000000000000000000 : ℝ)*base75 + (53994543221751727/4668750000000000000000000000000 : ℝ)*base78 + (27232149934739227/4668750000000000000000000000000 : ℝ)*base80 + (11302122445981/3735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (48947739/5000000000000000000000 : ℝ)*base89 + (48947739/5000000000000000000000 : ℝ)*base91 + (48947739/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19458522035118735445688519/1452500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (343074311/100000000000000 : ℝ)*(base21) + (35574141/20000000000000 : ℝ)*(upper2) + (70531033/25000000000000 : ℝ)*(lower4) + (57977353/100000000000000 : ℝ)*(upper5) + (420642042032189/10000000000000 : ℝ)*(major0) + (420642042032189/10000000000000 : ℝ)*(major1) + (420642042032189/10000000000000 : ℝ)*(major2) + (172430889/20000000000000 : ℝ)*(sp0) + (2346010223/100000000000000 : ℝ)*(sp2) + (43794323/6250000000000 : ℝ)*(sp3) + (180310094160091/3125000000000 : ℝ)*(sp4) + (5769923875277357/100000000000000 : ℝ)*(sp5) + (5769921186192823/100000000000000 : ℝ)*(sp6) + (132145790905241/5000000000000 : ℝ)*(sp7) + (660729129703497/25000000000000 : ℝ)*(f.failure) + (5769923875277357/100000000000000 : ℝ)*(f.sum) + (5447092141727/1307250000000000000000000000 : ℝ)*base65 + (253778196272654443/26145000000000000000000000000000 : ℝ)*base68 + (236710169579594443/26145000000000000000000000000000 : ℝ)*base70 + (224799606915557/26145000000000000000000000000000 : ℝ)*base71 + (5503882270357/1307250000000000000000000000 : ℝ)*base74 + (224592301127954443/26145000000000000000000000000000 : ℝ)*base76 + (25999868155979443/26145000000000000000000000000000 : ℝ)*base78 + (51342548634645557/26145000000000000000000000000000 : ℝ)*base79 + (4914663169289/5229000000000000000000000000 : ℝ)*base81 + (8450917/1250000000000000000000 : ℝ)*base90 + (8450917/1250000000000000000000 : ℝ)*base92 + (8450917/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1454_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2987/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1454_s4_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-975448071/5000000000 : ℝ)*x 0 + (5408080167/10000000000 : ℝ)*x 1 + (524637359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975448071/5000000000 : ℝ)^2207 ≤ (5953999666571/50000000000000 : ℝ)^1695 := by
    have hnat : (975448071 : ℕ)^2207*50000000000000^1695 ≤ 5953999666571^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975448071 5000000000 5953999666571 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408080167/10000000000 : ℝ)^2207 ≤ (22458193683367/50000000000000 : ℝ)^1695 := by
    have hnat : (5408080167 : ℕ)^2207*50000000000000^1695 ≤ 22458193683367^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408080167 10000000000 22458193683367 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524637359/1000000000 : ℝ)^2207 ≤ (8635122658103/20000000000000 : ℝ)^1695 := by
    have hnat : (524637359 : ℕ)^2207*20000000000000^1695 ≤ 8635122658103^1695*1000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524637359 1000000000 8635122658103 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975448071/5000000000 : ℝ), (5408080167/10000000000 : ℝ), (524637359/1000000000 : ℝ)] ![(5953999666571/50000000000000 : ℝ), (22458193683367/50000000000000 : ℝ), (8635122658103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975448071/5000000000 : ℝ)|^2207 ≤ (5953999666571/50000000000000 : ℝ)^1695
        have hw : |(-975448071/5000000000 : ℝ)|=(975448071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408080167/10000000000 : ℝ)|^2207 ≤ (22458193683367/50000000000000 : ℝ)^1695
        have hw : |(5408080167/10000000000 : ℝ)|=(5408080167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524637359/1000000000 : ℝ)|^2207 ≤ (8635122658103/20000000000000 : ℝ)^1695
        have hw : |(524637359/1000000000 : ℝ)|=(524637359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s4_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347087277/10000000000 : ℝ)*x 0 + (-1016613361/5000000000 : ℝ)*x 1 + (5246373583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347087277/10000000000 : ℝ)^2207 ≤ (44257924639877/100000000000000 : ℝ)^1695 := by
    have hnat : (5347087277 : ℕ)^2207*100000000000000^1695 ≤ 44257924639877^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347087277 10000000000 44257924639877 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016613361/5000000000 : ℝ)^2207 ≤ (785403882821/6250000000000 : ℝ)^1695 := by
    have hnat : (1016613361 : ℕ)^2207*6250000000000^1695 ≤ 785403882821^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016613361 5000000000 785403882821 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246373583/10000000000 : ℝ)^2207 ≤ (21587806607753/50000000000000 : ℝ)^1695 := by
    have hnat : (5246373583 : ℕ)^2207*50000000000000^1695 ≤ 21587806607753^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246373583 10000000000 21587806607753 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347087277/10000000000 : ℝ), (-1016613361/5000000000 : ℝ), (5246373583/10000000000 : ℝ)] ![(44257924639877/100000000000000 : ℝ), (785403882821/6250000000000 : ℝ), (21587806607753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347087277/10000000000 : ℝ)|^2207 ≤ (44257924639877/100000000000000 : ℝ)^1695
        have hw : |(5347087277/10000000000 : ℝ)|=(5347087277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016613361/5000000000 : ℝ)|^2207 ≤ (785403882821/6250000000000 : ℝ)^1695
        have hw : |(-1016613361/5000000000 : ℝ)|=(1016613361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246373583/10000000000 : ℝ)|^2207 ≤ (21587806607753/50000000000000 : ℝ)^1695
        have hw : |(5246373583/10000000000 : ℝ)|=(5246373583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s4_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336771821/2500000000 : ℝ)*x 0 + (2623186789/5000000000 : ℝ)*x 1 + (-2033226719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336771821/2500000000 : ℝ)^2207 ≤ (44257924715317/100000000000000 : ℝ)^1695 := by
    have hnat : (1336771821 : ℕ)^2207*100000000000000^1695 ≤ 44257924715317^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336771821 2500000000 44257924715317 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623186789/5000000000 : ℝ)^2207 ≤ (43175613161929/100000000000000 : ℝ)^1695 := by
    have hnat : (2623186789 : ℕ)^2207*100000000000000^1695 ≤ 43175613161929^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623186789 5000000000 43175613161929 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2033226719/10000000000 : ℝ)^2207 ≤ (12566462100993/100000000000000 : ℝ)^1695 := by
    have hnat : (2033226719 : ℕ)^2207*100000000000000^1695 ≤ 12566462100993^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033226719 10000000000 12566462100993 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336771821/2500000000 : ℝ), (2623186789/5000000000 : ℝ), (-2033226719/10000000000 : ℝ)] ![(44257924715317/100000000000000 : ℝ), (43175613161929/100000000000000 : ℝ), (12566462100993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336771821/2500000000 : ℝ)|^2207 ≤ (44257924715317/100000000000000 : ℝ)^1695
        have hw : |(1336771821/2500000000 : ℝ)|=(1336771821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623186789/5000000000 : ℝ)|^2207 ≤ (43175613161929/100000000000000 : ℝ)^1695
        have hw : |(2623186789/5000000000 : ℝ)|=(2623186789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2033226719/10000000000 : ℝ)|^2207 ≤ (12566462100993/100000000000000 : ℝ)^1695
        have hw : |(-2033226719/10000000000 : ℝ)|=(2033226719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s4_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (859616619/2000000000 : ℝ)*x 0 + (515599019/1250000000 : ℝ)*x 1 + (4477824377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859616619/2000000000 : ℝ)^2207 ≤ (8326069058643/25000000000000 : ℝ)^1695 := by
    have hnat : (859616619 : ℕ)^2207*25000000000000^1695 ≤ 8326069058643^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859616619 2000000000 8326069058643 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515599019/1250000000 : ℝ)^2207 ≤ (15783326460069/50000000000000 : ℝ)^1695 := by
    have hnat : (515599019 : ℕ)^2207*50000000000000^1695 ≤ 15783326460069^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515599019 1250000000 15783326460069 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477824377/10000000000 : ℝ)^2207 ≤ (1405162832827/4000000000000 : ℝ)^1695 := by
    have hnat : (4477824377 : ℕ)^2207*4000000000000^1695 ≤ 1405162832827^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477824377 10000000000 1405162832827 4000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859616619/2000000000 : ℝ), (515599019/1250000000 : ℝ), (4477824377/10000000000 : ℝ)] ![(8326069058643/25000000000000 : ℝ), (15783326460069/50000000000000 : ℝ), (1405162832827/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859616619/2000000000 : ℝ)|^2207 ≤ (8326069058643/25000000000000 : ℝ)^1695
        have hw : |(859616619/2000000000 : ℝ)|=(859616619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515599019/1250000000 : ℝ)|^2207 ≤ (15783326460069/50000000000000 : ℝ)^1695
        have hw : |(515599019/1250000000 : ℝ)|=(515599019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477824377/10000000000 : ℝ)|^2207 ≤ (1405162832827/4000000000000 : ℝ)^1695
        have hw : |(4477824377/10000000000 : ℝ)|=(4477824377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s4_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-487726921/2500000000 : ℝ)*x 0 + (5246966173/10000000000 : ℝ)*x 1 + (540748449/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487726921/2500000000 : ℝ)^2207 ≤ (11908091064693/100000000000000 : ℝ)^1695 := by
    have hnat : (487726921 : ℕ)^2207*100000000000000^1695 ≤ 11908091064693^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487726921 2500000000 11908091064693 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246966173/10000000000 : ℝ)^2207 ≤ (21590981607273/50000000000000 : ℝ)^1695 := by
    have hnat : (5246966173 : ℕ)^2207*50000000000000^1695 ≤ 21590981607273^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246966173 10000000000 21590981607273 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540748449/1000000000 : ℝ)^2207 ≤ (22454972852353/50000000000000 : ℝ)^1695 := by
    have hnat : (540748449 : ℕ)^2207*50000000000000^1695 ≤ 22454972852353^1695*1000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540748449 1000000000 22454972852353 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487726921/2500000000 : ℝ), (5246966173/10000000000 : ℝ), (540748449/1000000000 : ℝ)] ![(11908091064693/100000000000000 : ℝ), (21590981607273/50000000000000 : ℝ), (22454972852353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487726921/2500000000 : ℝ)|^2207 ≤ (11908091064693/100000000000000 : ℝ)^1695
        have hw : |(-487726921/2500000000 : ℝ)|=(487726921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246966173/10000000000 : ℝ)|^2207 ≤ (21590981607273/50000000000000 : ℝ)^1695
        have hw : |(5246966173/10000000000 : ℝ)|=(5246966173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540748449/1000000000 : ℝ)|^2207 ≤ (22454972852353/50000000000000 : ℝ)^1695
        have hw : |(540748449/1000000000 : ℝ)|=(540748449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s4_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652473703/5000000000 : ℝ)*x 0 + (-374423173/2000000000 : ℝ)*x 1 + (5407484479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652473703/5000000000 : ℝ)^2207 ≤ (43804315897587/100000000000000 : ℝ)^1695 := by
    have hnat : (2652473703 : ℕ)^2207*100000000000000^1695 ≤ 43804315897587^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652473703 5000000000 43804315897587 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374423173/2000000000 : ℝ)^2207 ≤ (5642869248409/50000000000000 : ℝ)^1695 := by
    have hnat : (374423173 : ℕ)^2207*50000000000000^1695 ≤ 5642869248409^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374423173 2000000000 5642869248409 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407484479/10000000000 : ℝ)^2207 ≤ (22454972792877/50000000000000 : ℝ)^1695 := by
    have hnat : (5407484479 : ℕ)^2207*50000000000000^1695 ≤ 22454972792877^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407484479 10000000000 22454972792877 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652473703/5000000000 : ℝ), (-374423173/2000000000 : ℝ), (5407484479/10000000000 : ℝ)] ![(43804315897587/100000000000000 : ℝ), (5642869248409/50000000000000 : ℝ), (22454972792877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652473703/5000000000 : ℝ)|^2207 ≤ (43804315897587/100000000000000 : ℝ)^1695
        have hw : |(2652473703/5000000000 : ℝ)|=(2652473703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374423173/2000000000 : ℝ)|^2207 ≤ (5642869248409/50000000000000 : ℝ)^1695
        have hw : |(-374423173/2000000000 : ℝ)|=(374423173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407484479/10000000000 : ℝ)|^2207 ≤ (22454972792877/50000000000000 : ℝ)^1695
        have hw : |(5407484479/10000000000 : ℝ)|=(5407484479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s4_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106098949/200000000 : ℝ)*x 0 + (675935557/1250000000 : ℝ)*x 1 + (-936057919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106098949/200000000 : ℝ)^2207 ≤ (10951079092663/25000000000000 : ℝ)^1695 := by
    have hnat : (106098949 : ℕ)^2207*25000000000000^1695 ≤ 10951079092663^1695*200000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106098949 200000000 10951079092663 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675935557/1250000000 : ℝ)^2207 ≤ (11227486334259/25000000000000 : ℝ)^1695 := by
    have hnat : (675935557 : ℕ)^2207*25000000000000^1695 ≤ 11227486334259^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675935557 1250000000 11227486334259 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936057919/5000000000 : ℝ)^2207 ≤ (11285738284887/100000000000000 : ℝ)^1695 := by
    have hnat : (936057919 : ℕ)^2207*100000000000000^1695 ≤ 11285738284887^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936057919 5000000000 11285738284887 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106098949/200000000 : ℝ), (675935557/1250000000 : ℝ), (-936057919/5000000000 : ℝ)] ![(10951079092663/25000000000000 : ℝ), (11227486334259/25000000000000 : ℝ), (11285738284887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106098949/200000000 : ℝ)|^2207 ≤ (10951079092663/25000000000000 : ℝ)^1695
        have hw : |(106098949/200000000 : ℝ)|=(106098949/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675935557/1250000000 : ℝ)|^2207 ≤ (11227486334259/25000000000000 : ℝ)^1695
        have hw : |(675935557/1250000000 : ℝ)|=(675935557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936057919/5000000000 : ℝ)|^2207 ≤ (11285738284887/100000000000000 : ℝ)^1695
        have hw : |(-936057919/5000000000 : ℝ)|=(936057919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s4_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298108371/10000000000 : ℝ)*x 0 + (4476530611/10000000000 : ℝ)*x 1 + (2063046351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298108371/10000000000 : ℝ)^2207 ≤ (33304531250059/100000000000000 : ℝ)^1695 := by
    have hnat : (4298108371 : ℕ)^2207*100000000000000^1695 ≤ 33304531250059^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298108371 10000000000 33304531250059 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476530611/10000000000 : ℝ)^2207 ≤ (35115855764379/100000000000000 : ℝ)^1695 := by
    have hnat : (4476530611 : ℕ)^2207*100000000000000^1695 ≤ 35115855764379^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476530611 10000000000 35115855764379 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063046351/5000000000 : ℝ)^2207 ≤ (31579612974679/100000000000000 : ℝ)^1695 := by
    have hnat : (2063046351 : ℕ)^2207*100000000000000^1695 ≤ 31579612974679^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063046351 5000000000 31579612974679 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298108371/10000000000 : ℝ), (4476530611/10000000000 : ℝ), (2063046351/5000000000 : ℝ)] ![(33304531250059/100000000000000 : ℝ), (35115855764379/100000000000000 : ℝ), (31579612974679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298108371/10000000000 : ℝ)|^2207 ≤ (33304531250059/100000000000000 : ℝ)^1695
        have hw : |(4298108371/10000000000 : ℝ)|=(4298108371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476530611/10000000000 : ℝ)|^2207 ≤ (35115855764379/100000000000000 : ℝ)^1695
        have hw : |(4476530611/10000000000 : ℝ)|=(4476530611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063046351/5000000000 : ℝ)|^2207 ≤ (31579612974679/100000000000000 : ℝ)^1695
        have hw : |(2063046351/5000000000 : ℝ)|=(2063046351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2987/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11367/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7397/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2987/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2987/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2987/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2987/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2987/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2987/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5617/50000 : ℝ) ^ (4413/1024 : ℝ) ≤ (4047448449454623/50000000000000000000 : ℝ) := by
    have hpowers : (5617/50000 : ℝ)^4413 ≤ (4047448449454623/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5617 : ℕ)^4413*50000000000000000000^1024 ≤ 4047448449454623^1024*50000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5617 50000 4047448449454623 50000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5617/50000 : ℝ)) (X := (4047448449454623/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2987/20000 : ℝ) ^ (4413/1024 : ℝ) ≤ (1726073874240373/6250000000000000000 : ℝ) := by
    have hpowers : (2987/20000 : ℝ)^4413 ≤ (1726073874240373/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2987 : ℕ)^4413*6250000000000000000^1024 ≤ 1726073874240373^1024*20000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2987 20000 1726073874240373 6250000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2987/20000 : ℝ)) (X := (1726073874240373/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004047448449454623/25000000000000000000 : ℝ) ≤ (10000375647367937/10000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (25004047448449454623/25000000000000000000 : ℝ)^1024 ≤ (10000375647367937/10000000000000000 : ℝ)^4413 := by
      have hnat : (25004047448449454623 : ℕ)^1024*10000000000000000^4413 ≤ 10000375647367937^4413*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004047448449454623 25000000000000000000 10000375647367937 10000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000375647367937/10000000000000000 : ℝ)) (X := (25004047448449454623/25000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017856039443377607/50000000000000000000 : ℝ) ≤ (5000414277761353/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (50017856039443377607/50000000000000000000 : ℝ)^1024 ≤ (5000414277761353/5000000000000000 : ℝ)^4413 := by
      have hnat : (50017856039443377607 : ℕ)^1024*5000000000000000^4413 ≤ 5000414277761353^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017856039443377607 50000000000000000000 5000414277761353 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000414277761353/5000000000000000 : ℝ)) (X := (50017856039443377607/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126726073874240373/3125000000000000000 : ℝ) ≤ (400051258547099/400000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (3126726073874240373/3125000000000000000 : ℝ)^1024 ≤ (400051258547099/400000000000000 : ℝ)^4413 := by
      have hnat : (3126726073874240373 : ℕ)^1024*400000000000000^4413 ≤ 400051258547099^4413*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126726073874240373 3125000000000000000 400051258547099 400000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400051258547099/400000000000000 : ℝ)) (X := (3126726073874240373/3125000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4047448449454623/50000000000000000000 : ℝ) ≤ ((7400242866097476989/7402000000000000000 : ℝ)+2*(452908154769/370100000000000 : ℝ)*(5617/50000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (7400242866097476989/7402000000000000000 : ℝ)+2*(452908154769/370100000000000 : ℝ)*(5617/50000 : ℝ)=(10000375647367937/10000000000000000 : ℝ) by norm_num, show 1+2*(4047448449454623/50000000000000000000 : ℝ)=(25004047448449454623/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1726073874240373/6250000000000000000 : ℝ)+(4047448449454623/50000000000000000000 : ℝ) ≤ ((7400242866097476989/7402000000000000000 : ℝ)+(452908154769/370100000000000 : ℝ)*((2987/20000 : ℝ)+(5617/50000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (7400242866097476989/7402000000000000000 : ℝ)+(452908154769/370100000000000 : ℝ)*((2987/20000 : ℝ)+(5617/50000 : ℝ))=(5000414277761353/5000000000000000 : ℝ) by norm_num, show 1+(1726073874240373/6250000000000000000 : ℝ)+(4047448449454623/50000000000000000000 : ℝ)=(50017856039443377607/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1726073874240373/6250000000000000000 : ℝ) ≤ ((7400242866097476989/7402000000000000000 : ℝ)+2*(452908154769/370100000000000 : ℝ)*(2987/20000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (7400242866097476989/7402000000000000000 : ℝ)+2*(452908154769/370100000000000 : ℝ)*(2987/20000 : ℝ)=(400051258547099/400000000000000 : ℝ) by norm_num, show 1+2*(1726073874240373/6250000000000000000 : ℝ)=(3126726073874240373/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7400242866097476989/7402000000000000000 : ℝ)*(X 1 0+X 2 0)+(452908154769/370100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (2987/20000 : ℝ)) (c := (7400242866097476989/7402000000000000000 : ℝ)) (alpha := (452908154769/370100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7400242866097476989/7402000000000000000 : ℝ)*(X 0 1+X 2 1)+(452908154769/370100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (2987/20000 : ℝ)) (c := (7400242866097476989/7402000000000000000 : ℝ)) (alpha := (452908154769/370100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7400242866097476989/7402000000000000000 : ℝ)*(X 0 2+X 1 2)+(452908154769/370100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (2987/20000 : ℝ)) (c := (7400242866097476989/7402000000000000000 : ℝ)) (alpha := (452908154769/370100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-975448071/5000000000 : ℝ)*X 0 0+(5408080167/10000000000 : ℝ)*X 0 1+(524637359/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347087277/10000000000 : ℝ)*X 1 0+(-1016613361/5000000000 : ℝ)*X 1 1+(5246373583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336771821/2500000000 : ℝ)*X 2 0+(2623186789/5000000000 : ℝ)*X 2 1+(-2033226719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((859616619/2000000000 : ℝ)*X 0 0+(515599019/1250000000 : ℝ)*X 0 1+(4477824377/10000000000 : ℝ)*X 0 2+(859616619/2000000000 : ℝ)*X 1 0+(515599019/1250000000 : ℝ)*X 1 1+(4477824377/10000000000 : ℝ)*X 1 2+(859616619/2000000000 : ℝ)*X 2 0+(515599019/1250000000 : ℝ)*X 2 1+(4477824377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-487726921/2500000000 : ℝ)*X 0 0+(5246966173/10000000000 : ℝ)*X 0 1+(540748449/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652473703/5000000000 : ℝ)*X 1 0+(-374423173/2000000000 : ℝ)*X 1 1+(5407484479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106098949/200000000 : ℝ)*X 2 0+(675935557/1250000000 : ℝ)*X 2 1+(-936057919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298108371/10000000000 : ℝ)*X 0 0+(4476530611/10000000000 : ℝ)*X 0 1+(2063046351/5000000000 : ℝ)*X 0 2+(4298108371/10000000000 : ℝ)*X 1 0+(4476530611/10000000000 : ℝ)*X 1 1+(2063046351/5000000000 : ℝ)*X 1 2+(4298108371/10000000000 : ℝ)*X 2 0+(4476530611/10000000000 : ℝ)*X 2 1+(2063046351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2186527045944194175946901379/185050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107099927/5000000000000 : ℝ)*(base19) + (125860563/6250000000000 : ℝ)*(base23) + (36447171/50000000000000 : ℝ)*(lower2) + (290168493/100000000000000 : ℝ)*(upper3) + (39206831/20000000000000 : ℝ)*(upper5) + (2254194183823163/50000000000000 : ℝ)*(major0) + (2254194183823163/50000000000000 : ℝ)*(major1) + (2254194183823163/50000000000000 : ℝ)*(major2) + (1236817364002371/20000000000000 : ℝ)*(sp0) + (6184129599163843/100000000000000 : ℝ)*(sp1) + (49473037819147/800000000000 : ℝ)*(sp2) + (1416311265519879/50000000000000 : ℝ)*(sp3) + (44921150527/100000000000000 : ℝ)*(sp4) + (22069228113/100000000000000 : ℝ)*(sp7) + (283264460026787/10000000000000 : ℝ)*(f.failure) + (6184131741162383/100000000000000 : ℝ)*(f.sum) + (118551599849081/18505000000000000000000000000 : ℝ)*base66 + (2748058720253136207/370100000000000000000000000000000 : ℝ)*base67 + (1899456964307436207/370100000000000000000000000000000 : ℝ)*base69 + (3742681514599763793/370100000000000000000000000000000 : ℝ)*base72 + (75490863779871/18505000000000000000000000000 : ℝ)*base74 + (890069560001463793/370100000000000000000000000000000 : ℝ)*base76 + (1000291367671336207/370100000000000000000000000000000 : ℝ)*base77 + (4127886712193736207/370100000000000000000000000000000 : ℝ)*base79 + (118731346538141/18505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3603607/500000000000000000000 : ℝ)*base90 + (3603607/500000000000000000000 : ℝ)*base92 + (3603607/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28443982488633097507227/2313125000000000000000000000 : ℝ) := by norm_num
    linear_combination (244331829/12500000000000 : ℝ)*(base19) + (2223455623/100000000000000 : ℝ)*(base23) + (112853189/50000000000000 : ℝ)*(upper3) + (98219243/100000000000000 : ℝ)*(lower4) + (267425241/100000000000000 : ℝ)*(upper5) + (4541695151450003/100000000000000 : ℝ)*(major0) + (4541695151450003/100000000000000 : ℝ)*(major1) + (4541695151450003/100000000000000 : ℝ)*(major2) + (5160412891/12500000000000 : ℝ)*(sp1) + (45309714437/100000000000000 : ℝ)*(sp2) + (155745461544367/2500000000000 : ℝ)*(sp4) + (155744380595423/2500000000000 : ℝ)*(sp5) + (311488546430231/5000000000000 : ℝ)*(sp6) + (2853571431232753/100000000000000 : ℝ)*(sp7) + (2853571431232753/100000000000000 : ℝ)*(f.failure) + (155745461544367/2500000000000 : ℝ)*(f.sum) + (6579088230949/2313125000000000000000000000 : ℝ)*base65 + (1427078681801979033/740200000000000000000000000000000 : ℝ)*base68 + (3580231719238579033/740200000000000000000000000000000 : ℝ)*base70 + (6182558065234820967/740200000000000000000000000000000 : ℝ)*base71 + (384907714033/1156562500000000000000000000 : ℝ)*base74 + (459059324019379033/740200000000000000000000000000000 : ℝ)*base76 + (5260915702328420967/740200000000000000000000000000000 : ℝ)*base77 + (117102378824820967/740200000000000000000000000000000 : ℝ)*base79 + (1424859772213/1156562500000000000000000000 : ℝ)*base82 + (42339667/5000000000000000000000 : ℝ)*base89 + (42339667/5000000000000000000000 : ℝ)*base91 + (42339667/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1454_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2987/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1454_s5_0 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951008383/10000000000 : ℝ)*x 0 + (5407079221/10000000000 : ℝ)*x 1 + (2623650227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951008383/10000000000 : ℝ)^2207 ≤ (744305711881/6250000000000 : ℝ)^1695 := by
    have hnat : (1951008383 : ℕ)^2207*6250000000000^1695 ≤ 744305711881^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951008383 10000000000 744305711881 6250000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407079221/10000000000 : ℝ)^2207 ≤ (4490556324081/10000000000000 : ℝ)^1695 := by
    have hnat : (5407079221 : ℕ)^2207*10000000000000^1695 ≤ 4490556324081^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407079221 10000000000 4490556324081 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623650227/5000000000 : ℝ)^2207 ≤ (43185545355087/100000000000000 : ℝ)^1695 := by
    have hnat : (2623650227 : ℕ)^2207*100000000000000^1695 ≤ 43185545355087^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623650227 5000000000 43185545355087 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951008383/10000000000 : ℝ), (5407079221/10000000000 : ℝ), (2623650227/5000000000 : ℝ)] ![(744305711881/6250000000000 : ℝ), (4490556324081/10000000000000 : ℝ), (43185545355087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951008383/10000000000 : ℝ)|^2207 ≤ (744305711881/6250000000000 : ℝ)^1695
        have hw : |(-1951008383/10000000000 : ℝ)|=(1951008383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407079221/10000000000 : ℝ)|^2207 ≤ (4490556324081/10000000000000 : ℝ)^1695
        have hw : |(5407079221/10000000000 : ℝ)|=(5407079221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623650227/5000000000 : ℝ)|^2207 ≤ (43185545355087/100000000000000 : ℝ)^1695
        have hw : |(2623650227/5000000000 : ℝ)|=(2623650227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s5_1 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336706919/2500000000 : ℝ)*x 0 + (-2032340127/10000000000 : ℝ)*x 1 + (1049460091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336706919/2500000000 : ℝ)^2207 ≤ (4425512688553/10000000000000 : ℝ)^1695 := by
    have hnat : (1336706919 : ℕ)^2207*10000000000000^1695 ≤ 4425512688553^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336706919 2500000000 4425512688553 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2032340127/10000000000 : ℝ)^2207 ≤ (1569915967561/12500000000000 : ℝ)^1695 := by
    have hnat : (2032340127 : ℕ)^2207*12500000000000^1695 ≤ 1569915967561^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032340127 10000000000 1569915967561 12500000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049460091/2000000000 : ℝ)^2207 ≤ (43185545365803/100000000000000 : ℝ)^1695 := by
    have hnat : (1049460091 : ℕ)^2207*100000000000000^1695 ≤ 43185545365803^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049460091 2000000000 43185545365803 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336706919/2500000000 : ℝ), (-2032340127/10000000000 : ℝ), (1049460091/2000000000 : ℝ)] ![(4425512688553/10000000000000 : ℝ), (1569915967561/12500000000000 : ℝ), (43185545365803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336706919/2500000000 : ℝ)|^2207 ≤ (4425512688553/10000000000000 : ℝ)^1695
        have hw : |(1336706919/2500000000 : ℝ)|=(1336706919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2032340127/10000000000 : ℝ)|^2207 ≤ (1569915967561/12500000000000 : ℝ)^1695
        have hw : |(-2032340127/10000000000 : ℝ)|=(2032340127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049460091/2000000000 : ℝ)|^2207 ≤ (43185545365803/100000000000000 : ℝ)^1695
        have hw : |(1049460091/2000000000 : ℝ)|=(1049460091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s5_2 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346827741/10000000000 : ℝ)*x 0 + (1049460077/2000000000 : ℝ)*x 1 + (-2032340133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346827741/10000000000 : ℝ)^2207 ≤ (22127563793019/50000000000000 : ℝ)^1695 := by
    have hnat : (5346827741 : ℕ)^2207*50000000000000^1695 ≤ 22127563793019^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346827741 10000000000 22127563793019 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049460077/2000000000 : ℝ)^2207 ≤ (43185544615679/100000000000000 : ℝ)^1695 := by
    have hnat : (1049460077 : ℕ)^2207*100000000000000^1695 ≤ 43185544615679^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049460077 2000000000 43185544615679 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2032340133/10000000000 : ℝ)^2207 ≤ (12559327788767/100000000000000 : ℝ)^1695 := by
    have hnat : (2032340133 : ℕ)^2207*100000000000000^1695 ≤ 12559327788767^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032340133 10000000000 12559327788767 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346827741/10000000000 : ℝ), (1049460077/2000000000 : ℝ), (-2032340133/10000000000 : ℝ)] ![(22127563793019/50000000000000 : ℝ), (43185544615679/100000000000000 : ℝ), (12559327788767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346827741/10000000000 : ℝ)|^2207 ≤ (22127563793019/50000000000000 : ℝ)^1695
        have hw : |(5346827741/10000000000 : ℝ)|=(5346827741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049460077/2000000000 : ℝ)|^2207 ≤ (43185544615679/100000000000000 : ℝ)^1695
        have hw : |(1049460077/2000000000 : ℝ)|=(1049460077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2032340133/10000000000 : ℝ)|^2207 ≤ (12559327788767/100000000000000 : ℝ)^1695
        have hw : |(-2032340133/10000000000 : ℝ)|=(2032340133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s5_3 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298151297/10000000000 : ℝ)*x 0 + (128965259/312500000 : ℝ)*x 1 + (559463991/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298151297/10000000000 : ℝ)^2207 ≤ (3330496434157/10000000000000 : ℝ)^1695 := by
    have hnat : (4298151297 : ℕ)^2207*10000000000000^1695 ≤ 3330496434157^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298151297 10000000000 3330496434157 10000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128965259/312500000 : ℝ)^2207 ≤ (6317508328531/20000000000000 : ℝ)^1695 := by
    have hnat : (128965259 : ℕ)^2207*20000000000000^1695 ≤ 6317508328531^1695*312500000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128965259 312500000 6317508328531 20000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559463991/1250000000 : ℝ)^2207 ≤ (17553746998279/50000000000000 : ℝ)^1695 := by
    have hnat : (559463991 : ℕ)^2207*50000000000000^1695 ≤ 17553746998279^1695*1250000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559463991 1250000000 17553746998279 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298151297/10000000000 : ℝ), (128965259/312500000 : ℝ), (559463991/1250000000 : ℝ)] ![(3330496434157/10000000000000 : ℝ), (6317508328531/20000000000000 : ℝ), (17553746998279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298151297/10000000000 : ℝ)|^2207 ≤ (3330496434157/10000000000000 : ℝ)^1695
        have hw : |(4298151297/10000000000 : ℝ)|=(4298151297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128965259/312500000 : ℝ)|^2207 ≤ (6317508328531/20000000000000 : ℝ)^1695
        have hw : |(128965259/312500000 : ℝ)|=(128965259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559463991/1250000000 : ℝ)|^2207 ≤ (17553746998279/50000000000000 : ℝ)^1695
        have hw : |(559463991/1250000000 : ℝ)|=(559463991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s5_4 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-975509797/5000000000 : ℝ)*x 0 + (1049575817/2000000000 : ℝ)*x 1 + (5406497549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975509797/5000000000 : ℝ)^2207 ≤ (11908980492529/100000000000000 : ℝ)^1695 := by
    have hnat : (975509797 : ℕ)^2207*100000000000000^1695 ≤ 11908980492529^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975509797 5000000000 11908980492529 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049575817/2000000000 : ℝ)^2207 ≤ (43191746102443/100000000000000 : ℝ)^1695 := by
    have hnat : (1049575817 : ℕ)^2207*100000000000000^1695 ≤ 43191746102443^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049575817 2000000000 43191746102443 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406497549/10000000000 : ℝ)^2207 ≤ (44899273378359/100000000000000 : ℝ)^1695 := by
    have hnat : (5406497549 : ℕ)^2207*100000000000000^1695 ≤ 44899273378359^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406497549 10000000000 44899273378359 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975509797/5000000000 : ℝ), (1049575817/2000000000 : ℝ), (5406497549/10000000000 : ℝ)] ![(11908980492529/100000000000000 : ℝ), (43191746102443/100000000000000 : ℝ), (44899273378359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975509797/5000000000 : ℝ)|^2207 ≤ (11908980492529/100000000000000 : ℝ)^1695
        have hw : |(-975509797/5000000000 : ℝ)|=(975509797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049575817/2000000000 : ℝ)|^2207 ≤ (43191746102443/100000000000000 : ℝ)^1695
        have hw : |(1049575817/2000000000 : ℝ)|=(1049575817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406497549/10000000000 : ℝ)|^2207 ≤ (44899273378359/100000000000000 : ℝ)^1695
        have hw : |(5406497549/10000000000 : ℝ)|=(5406497549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s5_5 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305189811/10000000000 : ℝ)*x 0 + (-468285791/2500000000 : ℝ)*x 1 + (337906107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305189811/10000000000 : ℝ)^2207 ≤ (10951730532319/25000000000000 : ℝ)^1695 := by
    have hnat : (5305189811 : ℕ)^2207*25000000000000^1695 ≤ 10951730532319^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305189811 10000000000 10951730532319 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468285791/2500000000 : ℝ)^2207 ≤ (11293802723781/100000000000000 : ℝ)^1695 := by
    have hnat : (468285791 : ℕ)^2207*100000000000000^1695 ≤ 11293802723781^1695*2500000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468285791 2500000000 11293802723781 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337906107/625000000 : ℝ)^2207 ≤ (22449637570459/50000000000000 : ℝ)^1695 := by
    have hnat : (337906107 : ℕ)^2207*50000000000000^1695 ≤ 22449637570459^1695*625000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337906107 625000000 22449637570459 50000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305189811/10000000000 : ℝ), (-468285791/2500000000 : ℝ), (337906107/625000000 : ℝ)] ![(10951730532319/25000000000000 : ℝ), (11293802723781/100000000000000 : ℝ), (22449637570459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305189811/10000000000 : ℝ)|^2207 ≤ (10951730532319/25000000000000 : ℝ)^1695
        have hw : |(5305189811/10000000000 : ℝ)|=(5305189811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468285791/2500000000 : ℝ)|^2207 ≤ (11293802723781/100000000000000 : ℝ)^1695
        have hw : |(-468285791/2500000000 : ℝ)|=(468285791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337906107/625000000 : ℝ)|^2207 ≤ (22449637570459/50000000000000 : ℝ)^1695
        have hw : |(337906107/625000000 : ℝ)|=(337906107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s5_6 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652595089/5000000000 : ℝ)*x 0 + (5406497729/10000000000 : ℝ)*x 1 + (-1873142637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652595089/5000000000 : ℝ)^2207 ≤ (350455408601/800000000000 : ℝ)^1695 := by
    have hnat : (2652595089 : ℕ)^2207*800000000000^1695 ≤ 350455408601^1695*5000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652595089 5000000000 350455408601 800000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406497729/10000000000 : ℝ)^2207 ≤ (44899275324743/100000000000000 : ℝ)^1695 := by
    have hnat : (5406497729 : ℕ)^2207*100000000000000^1695 ≤ 44899275324743^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406497729 10000000000 44899275324743 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873142637/10000000000 : ℝ)^2207 ≤ (2823449646631/25000000000000 : ℝ)^1695 := by
    have hnat : (1873142637 : ℕ)^2207*25000000000000^1695 ≤ 2823449646631^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873142637 10000000000 2823449646631 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652595089/5000000000 : ℝ), (5406497729/10000000000 : ℝ), (-1873142637/10000000000 : ℝ)] ![(350455408601/800000000000 : ℝ), (44899275324743/100000000000000 : ℝ), (2823449646631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652595089/5000000000 : ℝ)|^2207 ≤ (350455408601/800000000000 : ℝ)^1695
        have hw : |(2652595089/5000000000 : ℝ)|=(2652595089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406497729/10000000000 : ℝ)|^2207 ≤ (44899275324743/100000000000000 : ℝ)^1695
        have hw : |(5406497729/10000000000 : ℝ)|=(5406497729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873142637/10000000000 : ℝ)|^2207 ≤ (2823449646631/25000000000000 : ℝ)^1695
        have hw : |(-1873142637/10000000000 : ℝ)|=(1873142637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1454_s5_7 (p : ℝ) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298175783/10000000000 : ℝ)*x 0 + (894889727/2000000000 : ℝ)*x 1 + (165126321/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298175783/10000000000 : ℝ)^2207 ≤ (33305211387739/100000000000000 : ℝ)^1695 := by
    have hnat : (4298175783 : ℕ)^2207*100000000000000^1695 ≤ 33305211387739^1695*10000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298175783 10000000000 33305211387739 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894889727/2000000000 : ℝ)^2207 ≤ (8773648007521/25000000000000 : ℝ)^1695 := by
    have hnat : (894889727 : ℕ)^2207*25000000000000^1695 ≤ 8773648007521^1695*2000000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894889727 2000000000 8773648007521 25000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165126321/400000000 : ℝ)^2207 ≤ (31600196571261/100000000000000 : ℝ)^1695 := by
    have hnat : (165126321 : ℕ)^2207*100000000000000^1695 ≤ 31600196571261^1695*400000000^2207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165126321 400000000 31600196571261 100000000000000 2207 1695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2207/512 : ℝ)) 2207 1695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298175783/10000000000 : ℝ), (894889727/2000000000 : ℝ), (165126321/400000000 : ℝ)] ![(33305211387739/100000000000000 : ℝ), (8773648007521/25000000000000 : ℝ), (31600196571261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298175783/10000000000 : ℝ)|^2207 ≤ (33305211387739/100000000000000 : ℝ)^1695
        have hw : |(4298175783/10000000000 : ℝ)|=(4298175783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894889727/2000000000 : ℝ)|^2207 ≤ (8773648007521/25000000000000 : ℝ)^1695
        have hw : |(894889727/2000000000 : ℝ)|=(894889727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165126321/400000000 : ℝ)|^2207 ≤ (31600196571261/100000000000000 : ℝ)^1695
        have hw : |(165126321/400000000 : ℝ)|=(165126321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1454_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11387/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11367/100000 : ℝ) ^ (4413/1024 : ℝ) ≤ (8516074140862961/100000000000000000000 : ℝ) := by
    have hpowers : (11367/100000 : ℝ)^4413 ≤ (8516074140862961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11367 : ℕ)^4413*100000000000000000000^1024 ≤ 8516074140862961^1024*100000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11367 100000 8516074140862961 100000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11367/100000 : ℝ)) (X := (8516074140862961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7397/50000 : ℝ) ^ (4413/1024 : ℝ) ≤ (26510968992279323/100000000000000000000 : ℝ) := by
    have hpowers : (7397/50000 : ℝ)^4413 ≤ (26510968992279323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7397 : ℕ)^4413*100000000000000000000^1024 ≤ 26510968992279323^1024*50000^4413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7397 50000 26510968992279323 100000000000000000000 4413 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7397/50000 : ℝ)) (X := (26510968992279323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008516074140862961/50000000000000000000 : ℝ) ≤ (10000395191011117/10000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (50008516074140862961/50000000000000000000 : ℝ)^1024 ≤ (10000395191011117/10000000000000000 : ℝ)^4413 := by
      have hnat : (50008516074140862961 : ℕ)^1024*10000000000000000^4413 ≤ 10000395191011117^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008516074140862961 50000000000000000000 10000395191011117 10000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000395191011117/10000000000000000 : ℝ)) (X := (50008516074140862961/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008756760783285571/25000000000000000000 : ℝ) ≤ (5000406332076629/5000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (25008756760783285571/25000000000000000000 : ℝ)^1024 ≤ (5000406332076629/5000000000000000 : ℝ)^4413 := by
      have hnat : (25008756760783285571 : ℕ)^1024*5000000000000000^4413 ≤ 5000406332076629^4413*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008756760783285571 25000000000000000000 5000406332076629 5000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000406332076629/5000000000000000 : ℝ)) (X := (25008756760783285571/25000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026510968992279323/50000000000000000000 : ℝ) ≤ (10001230137295399/10000000000000000 : ℝ) ^ (4413/1024 : ℝ) := by
    have hpowers : (50026510968992279323/50000000000000000000 : ℝ)^1024 ≤ (10001230137295399/10000000000000000 : ℝ)^4413 := by
      have hnat : (50026510968992279323 : ℕ)^1024*10000000000000000^4413 ≤ 10001230137295399^4413*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026510968992279323 50000000000000000000 10001230137295399 10000000000000000 1024 4413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001230137295399/10000000000000000 : ℝ)) (X := (50026510968992279323/50000000000000000000 : ℝ)) (by norm_num) 4413 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8516074140862961/100000000000000000000 : ℝ) ≤ ((6852372697036332893/6854000000000000000 : ℝ)+2*(417473142141/342700000000000 : ℝ)*(11367/100000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (6852372697036332893/6854000000000000000 : ℝ)+2*(417473142141/342700000000000 : ℝ)*(11367/100000 : ℝ)=(10000395191011117/10000000000000000 : ℝ) by norm_num, show 1+2*(8516074140862961/100000000000000000000 : ℝ)=(50008516074140862961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26510968992279323/100000000000000000000 : ℝ)+(8516074140862961/100000000000000000000 : ℝ) ≤ ((6852372697036332893/6854000000000000000 : ℝ)+(417473142141/342700000000000 : ℝ)*((7397/50000 : ℝ)+(11367/100000 : ℝ)))^(4413/1024 : ℝ) := by
    rw [show (6852372697036332893/6854000000000000000 : ℝ)+(417473142141/342700000000000 : ℝ)*((7397/50000 : ℝ)+(11367/100000 : ℝ))=(5000406332076629/5000000000000000 : ℝ) by norm_num, show 1+(26510968992279323/100000000000000000000 : ℝ)+(8516074140862961/100000000000000000000 : ℝ)=(25008756760783285571/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26510968992279323/100000000000000000000 : ℝ) ≤ ((6852372697036332893/6854000000000000000 : ℝ)+2*(417473142141/342700000000000 : ℝ)*(7397/50000 : ℝ))^(4413/1024 : ℝ) := by
    rw [show (6852372697036332893/6854000000000000000 : ℝ)+2*(417473142141/342700000000000 : ℝ)*(7397/50000 : ℝ)=(10001230137295399/10000000000000000 : ℝ) by norm_num, show 1+2*(26510968992279323/100000000000000000000 : ℝ)=(50026510968992279323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6852372697036332893/6854000000000000000 : ℝ)*(X 1 0+X 2 0)+(417473142141/342700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (6852372697036332893/6854000000000000000 : ℝ)) (alpha := (417473142141/342700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6852372697036332893/6854000000000000000 : ℝ)*(X 0 1+X 2 1)+(417473142141/342700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (6852372697036332893/6854000000000000000 : ℝ)) (alpha := (417473142141/342700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6852372697036332893/6854000000000000000 : ℝ)*(X 0 2+X 1 2)+(417473142141/342700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4413/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (6852372697036332893/6854000000000000000 : ℝ)) (alpha := (417473142141/342700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1951008383/10000000000 : ℝ)*X 0 0+(5407079221/10000000000 : ℝ)*X 0 1+(2623650227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336706919/2500000000 : ℝ)*X 1 0+(-2032340127/10000000000 : ℝ)*X 1 1+(1049460091/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346827741/10000000000 : ℝ)*X 2 0+(1049460077/2000000000 : ℝ)*X 2 1+(-2032340133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298151297/10000000000 : ℝ)*X 0 0+(128965259/312500000 : ℝ)*X 0 1+(559463991/1250000000 : ℝ)*X 0 2+(4298151297/10000000000 : ℝ)*X 1 0+(128965259/312500000 : ℝ)*X 1 1+(559463991/1250000000 : ℝ)*X 1 2+(4298151297/10000000000 : ℝ)*X 2 0+(128965259/312500000 : ℝ)*X 2 1+(559463991/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975509797/5000000000 : ℝ)*X 0 0+(1049575817/2000000000 : ℝ)*X 0 1+(5406497549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305189811/10000000000 : ℝ)*X 1 0+(-468285791/2500000000 : ℝ)*X 1 1+(337906107/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652595089/5000000000 : ℝ)*X 2 0+(5406497729/10000000000 : ℝ)*X 2 1+(-1873142637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298175783/10000000000 : ℝ)*X 0 0+(894889727/2000000000 : ℝ)*X 0 1+(165126321/400000000 : ℝ)*X 0 2+(4298175783/10000000000 : ℝ)*X 1 0+(894889727/2000000000 : ℝ)*X 1 1+(165126321/400000000 : ℝ)*X 1 2+(4298175783/10000000000 : ℝ)*X 2 0+(894889727/2000000000 : ℝ)*X 2 1+(165126321/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1454_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1681358119653323307650105037/171350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425567783/25000000000000 : ℝ)*(base19) + (819726969/50000000000000 : ℝ)*(base23) + (3713449/5000000000000 : ℝ)*(lower2) + (242824359/100000000000000 : ℝ)*(upper3) + (146885263/100000000000000 : ℝ)*(upper5) + (4562769581768997/100000000000000 : ℝ)*(major0) + (4562769581768997/100000000000000 : ℝ)*(major1) + (4562769581768997/100000000000000 : ℝ)*(major2) + (6258690621417357/100000000000000 : ℝ)*(sp0) + (6258724525313291/100000000000000 : ℝ)*(sp1) + (1251744917626097/20000000000000 : ℝ)*(sp2) + (1433397094729089/50000000000000 : ℝ)*(sp3) + (17803083533/50000000000000 : ℝ)*(sp4) + (4604853683/25000000000000 : ℝ)*(sp7) + (2866812608872909/100000000000000 : ℝ)*(f.failure) + (6258726227584423/100000000000000 : ℝ)*(f.sum) + (1646817440099/535468750000000000000000000 : ℝ)*base66 + (797903131498858321/685400000000000000000000000000000 : ℝ)*base67 + (2998510602391858321/685400000000000000000000000000000 : ℝ)*base69 + (8055692732745058321/685400000000000000000000000000000 : ℝ)*base71 + (3982231671473/1070937500000000000000000000 : ℝ)*base74 + (3690133969750341679/685400000000000000000000000000000 : ℝ)*base76 + (1450943467412458321/685400000000000000000000000000000 : ℝ)*base77 + (1421560093881658321/685400000000000000000000000000000 : ℝ)*base79 + (207285108147/4283750000000000000000000000 : ℝ)*base82 + (8645351/5000000000000000000000 : ℝ)*base89 + (8645351/5000000000000000000000 : ℝ)*base91 + (8645351/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12668855932288264717521/1070937500000000000000000000 : ℝ) := by norm_num
    linear_combination (1578091747/100000000000000 : ℝ)*(base19) + (2411756763/100000000000000 : ℝ)*(base23) + (297533693/100000000000000 : ℝ)*(upper3) + (18100129/20000000000000 : ℝ)*(lower4) + (240115051/100000000000000 : ℝ)*(upper5) + (2298046921208879/50000000000000 : ℝ)*(major0) + (2298046921208879/50000000000000 : ℝ)*(major1) + (2298046921208879/50000000000000 : ℝ)*(major2) + (16649954967/50000000000000 : ℝ)*(sp1) + (62216763579/100000000000000 : ℝ)*(sp2) + (6304436869879269/100000000000000 : ℝ)*(sp4) + (6304401991877587/100000000000000 : ℝ)*(sp5) + (3152186120679463/50000000000000 : ℝ)*(sp6) + (1443875210316663/50000000000000 : ℝ)*(sp7) + (1443875210316663/50000000000000 : ℝ)*(f.failure) + (6304436869879269/100000000000000 : ℝ)*(f.sum) + (13114242803579/8567500000000000000000000000 : ℝ)*base65 + (2215586264432363053/342700000000000000000000000000000 : ℝ)*base68 + (1686514524846436947/342700000000000000000000000000000 : ℝ)*base69 + (1254612844382836947/342700000000000000000000000000000 : ℝ)*base71 + (57873283344931/8567500000000000000000000000 : ℝ)*base74 + (48366265302663053/342700000000000000000000000000000 : ℝ)*base76 + (902092301407363053/342700000000000000000000000000000 : ℝ)*base78 + (329520486326836947/342700000000000000000000000000000 : ℝ)*base79 + (7015870129943/17135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8893157/2500000000000000000000 : ℝ)*base89 + (8893157/2500000000000000000000 : ℝ)*base91 + (8893157/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1454_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1454_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1454_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1454_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1454_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1454_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
