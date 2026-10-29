-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1770_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:34:01.466387+00:00
-- url     : https://prove2.me/submissions/212c7521-fa93-4044-be28-4182c35b81b2

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
theorem support_rectangle_w1770_s0_0 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087465239/10000000000 : ℝ)*x 0 + (1393474079/2500000000 : ℝ)*x 1 + (1251183989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087465239/10000000000 : ℝ)^6095 ≤ (1736905882753/25000000000000 : ℝ)^5071 := by
    have hnat : (1087465239 : ℕ)^6095*25000000000000^5071 ≤ 1736905882753^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087465239 10000000000 1736905882753 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393474079/2500000000 : ℝ)^6095 ≤ (24766811841599/50000000000000 : ℝ)^5071 := by
    have hnat : (1393474079 : ℕ)^6095*50000000000000^5071 ≤ 24766811841599^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393474079 2500000000 24766811841599 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251183989/2500000000 : ℝ)^6095 ≤ (43518752777013/100000000000000 : ℝ)^5071 := by
    have hnat : (1251183989 : ℕ)^6095*100000000000000^5071 ≤ 43518752777013^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251183989 2500000000 43518752777013 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087465239/10000000000 : ℝ), (1393474079/2500000000 : ℝ), (1251183989/2500000000 : ℝ)] ![(1736905882753/25000000000000 : ℝ), (24766811841599/50000000000000 : ℝ), (43518752777013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087465239/10000000000 : ℝ)|^6095 ≤ (1736905882753/25000000000000 : ℝ)^5071
        have hw : |(-1087465239/10000000000 : ℝ)|=(1087465239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1393474079/2500000000 : ℝ)|^6095 ≤ (24766811841599/50000000000000 : ℝ)^5071
        have hw : |(1393474079/2500000000 : ℝ)|=(1393474079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251183989/2500000000 : ℝ)|^6095 ≤ (43518752777013/100000000000000 : ℝ)^5071
        have hw : |(1251183989/2500000000 : ℝ)|=(1251183989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s0_1 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349689809/10000000000 : ℝ)*x 0 + (-13901093/100000000 : ℝ)*x 1 + (1251183833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349689809/10000000000 : ℝ)^6095 ≤ (47148654175151/100000000000000 : ℝ)^5071 := by
    have hnat : (5349689809 : ℕ)^6095*100000000000000^5071 ≤ 47148654175151^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349689809 10000000000 47148654175151 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13901093/100000000 : ℝ)^6095 ≤ (9332599551221/100000000000000 : ℝ)^5071 := by
    have hnat : (13901093 : ℕ)^6095*100000000000000^5071 ≤ 9332599551221^5071*100000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13901093 100000000 9332599551221 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251183833/2500000000 : ℝ)^6095 ≤ (21759373127663/50000000000000 : ℝ)^5071 := by
    have hnat : (1251183833 : ℕ)^6095*50000000000000^5071 ≤ 21759373127663^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251183833 2500000000 21759373127663 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349689809/10000000000 : ℝ), (-13901093/100000000 : ℝ), (1251183833/2500000000 : ℝ)] ![(47148654175151/100000000000000 : ℝ), (9332599551221/100000000000000 : ℝ), (21759373127663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349689809/10000000000 : ℝ)|^6095 ≤ (47148654175151/100000000000000 : ℝ)^5071
        have hw : |(5349689809/10000000000 : ℝ)|=(5349689809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13901093/100000000 : ℝ)|^6095 ≤ (9332599551221/100000000000000 : ℝ)^5071
        have hw : |(-13901093/100000000 : ℝ)|=(13901093/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251183833/2500000000 : ℝ)|^6095 ≤ (21759373127663/50000000000000 : ℝ)^5071
        have hw : |(1251183833/2500000000 : ℝ)|=(1251183833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s0_2 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6687109/12500000 : ℝ)*x 0 + (5004737059/10000000000 : ℝ)*x 1 + (-173763811/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6687109/12500000 : ℝ)^6095 ≤ (471486265379/1000000000000 : ℝ)^5071 := by
    have hnat : (6687109 : ℕ)^6095*1000000000000^5071 ≤ 471486265379^5071*12500000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6687109 12500000 471486265379 1000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5004737059/10000000000 : ℝ)^6095 ≤ (43518764304931/100000000000000 : ℝ)^5071 := by
    have hnat : (5004737059 : ℕ)^6095*100000000000000^5071 ≤ 43518764304931^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004737059 10000000000 43518764304931 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173763811/1250000000 : ℝ)^6095 ≤ (291644035547/3125000000000 : ℝ)^5071 := by
    have hnat : (173763811 : ℕ)^6095*3125000000000^5071 ≤ 291644035547^5071*1250000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173763811 1250000000 291644035547 3125000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6687109/12500000 : ℝ), (5004737059/10000000000 : ℝ), (-173763811/1250000000 : ℝ)] ![(471486265379/1000000000000 : ℝ), (43518764304931/100000000000000 : ℝ), (291644035547/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6687109/12500000 : ℝ)|^6095 ≤ (471486265379/1000000000000 : ℝ)^5071
        have hw : |(6687109/12500000 : ℝ)|=(6687109/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5004737059/10000000000 : ℝ)|^6095 ≤ (43518764304931/100000000000000 : ℝ)^5071
        have hw : |(5004737059/10000000000 : ℝ)|=(5004737059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173763811/1250000000 : ℝ)|^6095 ≤ (291644035547/3125000000000 : ℝ)^5071
        have hw : |(-173763811/1250000000 : ℝ)|=(173763811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s0_3 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3948878229/10000000000 : ℝ)*x 0 + (750365181/2500000000 : ℝ)*x 1 + (5024722619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3948878229/10000000000 : ℝ)^6095 ≤ (16366607091851/50000000000000 : ℝ)^5071 := by
    have hnat : (3948878229 : ℕ)^6095*50000000000000^5071 ≤ 16366607091851^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948878229 10000000000 16366607091851 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750365181/2500000000 : ℝ)^6095 ≤ (2353905983639/10000000000000 : ℝ)^5071 := by
    have hnat : (750365181 : ℕ)^6095*10000000000000^5071 ≤ 2353905983639^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750365181 2500000000 2353905983639 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5024722619/10000000000 : ℝ)^6095 ≤ (1093193148937/2500000000000 : ℝ)^5071 := by
    have hnat : (5024722619 : ℕ)^6095*2500000000000^5071 ≤ 1093193148937^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024722619 10000000000 1093193148937 2500000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3948878229/10000000000 : ℝ), (750365181/2500000000 : ℝ), (5024722619/10000000000 : ℝ)] ![(16366607091851/50000000000000 : ℝ), (2353905983639/10000000000000 : ℝ), (1093193148937/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3948878229/10000000000 : ℝ)|^6095 ≤ (16366607091851/50000000000000 : ℝ)^5071
        have hw : |(3948878229/10000000000 : ℝ)|=(3948878229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(750365181/2500000000 : ℝ)|^6095 ≤ (2353905983639/10000000000000 : ℝ)^5071
        have hw : |(750365181/2500000000 : ℝ)|=(750365181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5024722619/10000000000 : ℝ)|^6095 ≤ (1093193148937/2500000000000 : ℝ)^5071
        have hw : |(5024722619/10000000000 : ℝ)|=(5024722619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s0_4 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-272119073/2500000000 : ℝ)*x 0 + (501878951/1000000000 : ℝ)*x 1 + (1111882099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272119073/2500000000 : ℝ)^6095 ≤ (434711754371/6250000000000 : ℝ)^5071 := by
    have hnat : (272119073 : ℕ)^6095*6250000000000^5071 ≤ 434711754371^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272119073 2500000000 434711754371 6250000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501878951/1000000000 : ℝ)^6095 ≤ (43665674007871/100000000000000 : ℝ)^5071 := by
    have hnat : (501878951 : ℕ)^6095*100000000000000^5071 ≤ 43665674007871^5071*1000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501878951 1000000000 43665674007871 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111882099/2000000000 : ℝ)^6095 ≤ (49378937908583/100000000000000 : ℝ)^5071 := by
    have hnat : (1111882099 : ℕ)^6095*100000000000000^5071 ≤ 49378937908583^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111882099 2000000000 49378937908583 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272119073/2500000000 : ℝ), (501878951/1000000000 : ℝ), (1111882099/2000000000 : ℝ)] ![(434711754371/6250000000000 : ℝ), (43665674007871/100000000000000 : ℝ), (49378937908583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272119073/2500000000 : ℝ)|^6095 ≤ (434711754371/6250000000000 : ℝ)^5071
        have hw : |(-272119073/2500000000 : ℝ)|=(272119073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501878951/1000000000 : ℝ)|^6095 ≤ (43665674007871/100000000000000 : ℝ)^5071
        have hw : |(501878951/1000000000 : ℝ)|=(501878951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1111882099/2000000000 : ℝ)|^6095 ≤ (49378937908583/100000000000000 : ℝ)^5071
        have hw : |(1111882099/2000000000 : ℝ)|=(1111882099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s0_5 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199320681/10000000000 : ℝ)*x 0 + (-417717973/5000000000 : ℝ)*x 1 + (5559410483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199320681/10000000000 : ℝ)^6095 ≤ (711880344249/1562500000000 : ℝ)^5071 := by
    have hnat : (5199320681 : ℕ)^6095*1562500000000^5071 ≤ 711880344249^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199320681 10000000000 711880344249 1562500000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417717973/5000000000 : ℝ)^6095 ≤ (506072017223/10000000000000 : ℝ)^5071 := by
    have hnat : (417717973 : ℕ)^6095*10000000000000^5071 ≤ 506072017223^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417717973 5000000000 506072017223 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5559410483/10000000000 : ℝ)^6095 ≤ (1975157511219/4000000000000 : ℝ)^5071 := by
    have hnat : (5559410483 : ℕ)^6095*4000000000000^5071 ≤ 1975157511219^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559410483 10000000000 1975157511219 4000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199320681/10000000000 : ℝ), (-417717973/5000000000 : ℝ), (5559410483/10000000000 : ℝ)] ![(711880344249/1562500000000 : ℝ), (506072017223/10000000000000 : ℝ), (1975157511219/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199320681/10000000000 : ℝ)|^6095 ≤ (711880344249/1562500000000 : ℝ)^5071
        have hw : |(5199320681/10000000000 : ℝ)|=(5199320681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417717973/5000000000 : ℝ)|^6095 ≤ (506072017223/10000000000000 : ℝ)^5071
        have hw : |(-417717973/5000000000 : ℝ)|=(417717973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5559410483/10000000000 : ℝ)|^6095 ≤ (1975157511219/4000000000000 : ℝ)^5071
        have hw : |(5559410483/10000000000 : ℝ)|=(5559410483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s0_6 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199321057/10000000000 : ℝ)*x 0 + (2779705159/5000000000 : ℝ)*x 1 + (-167087129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199321057/10000000000 : ℝ)^6095 ≤ (5695043249007/12500000000000 : ℝ)^5071 := by
    have hnat : (5199321057 : ℕ)^6095*12500000000000^5071 ≤ 5695043249007^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199321057 10000000000 5695043249007 12500000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779705159/5000000000 : ℝ)^6095 ≤ (24689468009499/50000000000000 : ℝ)^5071 := by
    have hnat : (2779705159 : ℕ)^6095*50000000000000^5071 ≤ 24689468009499^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779705159 5000000000 24689468009499 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167087129/2000000000 : ℝ)^6095 ≤ (1265179495177/25000000000000 : ℝ)^5071 := by
    have hnat : (167087129 : ℕ)^6095*25000000000000^5071 ≤ 1265179495177^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167087129 2000000000 1265179495177 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199321057/10000000000 : ℝ), (2779705159/5000000000 : ℝ), (-167087129/2000000000 : ℝ)] ![(5695043249007/12500000000000 : ℝ), (24689468009499/50000000000000 : ℝ), (1265179495177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199321057/10000000000 : ℝ)|^6095 ≤ (5695043249007/12500000000000 : ℝ)^5071
        have hw : |(5199321057/10000000000 : ℝ)|=(5199321057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779705159/5000000000 : ℝ)|^6095 ≤ (24689468009499/50000000000000 : ℝ)^5071
        have hw : |(2779705159/5000000000 : ℝ)|=(2779705159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-167087129/2000000000 : ℝ)|^6095 ≤ (1265179495177/25000000000000 : ℝ)^5071
        have hw : |(-167087129/2000000000 : ℝ)|=(167087129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s0_7 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1976234757/5000000000 : ℝ)*x 0 + (4974767163/10000000000 : ℝ)*x 1 + (3052953321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976234757/5000000000 : ℝ)^6095 ≤ (32768997842851/100000000000000 : ℝ)^5071 := by
    have hnat : (1976234757 : ℕ)^6095*100000000000000^5071 ≤ 32768997842851^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976234757 5000000000 32768997842851 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4974767163/10000000000 : ℝ)^6095 ≤ (43205725955921/100000000000000 : ℝ)^5071 := by
    have hnat : (4974767163 : ℕ)^6095*100000000000000^5071 ≤ 43205725955921^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974767163 10000000000 43205725955921 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3052953321/10000000000 : ℝ)^6095 ≤ (24025276187539/100000000000000 : ℝ)^5071 := by
    have hnat : (3052953321 : ℕ)^6095*100000000000000^5071 ≤ 24025276187539^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3052953321 10000000000 24025276187539 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1976234757/5000000000 : ℝ), (4974767163/10000000000 : ℝ), (3052953321/10000000000 : ℝ)] ![(32768997842851/100000000000000 : ℝ), (43205725955921/100000000000000 : ℝ), (24025276187539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1976234757/5000000000 : ℝ)|^6095 ≤ (32768997842851/100000000000000 : ℝ)^5071
        have hw : |(1976234757/5000000000 : ℝ)|=(1976234757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4974767163/10000000000 : ℝ)|^6095 ≤ (43205725955921/100000000000000 : ℝ)^5071
        have hw : |(4974767163/10000000000 : ℝ)|=(4974767163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3052953321/10000000000 : ℝ)|^6095 ≤ (24025276187539/100000000000000 : ℝ)^5071
        have hw : |(3052953321/10000000000 : ℝ)|=(3052953321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1770_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (7433/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9901/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (6079/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6079 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6079*1^1024 ≤ 0^1024*1^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6079/1024 : ℝ) ≤ (217065006776176289/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6079 ≤ (217065006776176289/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6079*50000000000000000000^1024 ≤ 217065006776176289^1024*5^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 217065006776176289 50000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (217065006776176289/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6079 := by
      have hnat : (1 : ℕ)^1024*1^6079 ≤ 1^6079*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50217065006776176289/50000000000000000000 : ℝ) ≤ (1250912462658169/1250000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (50217065006776176289/50000000000000000000 : ℝ)^1024 ≤ (1250912462658169/1250000000000000 : ℝ)^6079 := by
      have hnat : (50217065006776176289 : ℕ)^1024*1250000000000000^6079 ≤ 1250912462658169^6079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50217065006776176289 50000000000000000000 1250912462658169 1250000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250912462658169/1250000000000000 : ℝ)) (X := (50217065006776176289/50000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25217065006776176289/25000000000000000000 : ℝ) ≤ (625912462658169/625000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (25217065006776176289/25000000000000000000 : ℝ)^1024 ≤ (625912462658169/625000000000000 : ℝ)^6079 := by
      have hnat : (25217065006776176289 : ℕ)^1024*625000000000000^6079 ≤ 625912462658169^6079*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25217065006776176289 25000000000000000000 625912462658169 625000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625912462658169/625000000000000 : ℝ)) (X := (25217065006776176289/25000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(912462658169/500000000000000 : ℝ)*(0 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(912462658169/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(217065006776176289/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(912462658169/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6079/1024 : ℝ) := by
    rw [show (1 : ℝ)+(912462658169/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1250912462658169/1250000000000000 : ℝ) by norm_num, show 1+(217065006776176289/50000000000000000000 : ℝ)+(0 : ℝ)=(50217065006776176289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(217065006776176289/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(912462658169/500000000000000 : ℝ)*(2/5 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(912462658169/500000000000000 : ℝ)*(2/5 : ℝ)=(625912462658169/625000000000000 : ℝ) by norm_num, show 1+2*(217065006776176289/50000000000000000000 : ℝ)=(25217065006776176289/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(912462658169/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (912462658169/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(912462658169/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (912462658169/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(912462658169/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (912462658169/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1087465239/10000000000 : ℝ)*X 0 0+(1393474079/2500000000 : ℝ)*X 0 1+(1251183989/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349689809/10000000000 : ℝ)*X 1 0+(-13901093/100000000 : ℝ)*X 1 1+(1251183833/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((6687109/12500000 : ℝ)*X 2 0+(5004737059/10000000000 : ℝ)*X 2 1+(-173763811/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3948878229/10000000000 : ℝ)*X 0 0+(750365181/2500000000 : ℝ)*X 0 1+(5024722619/10000000000 : ℝ)*X 0 2+(3948878229/10000000000 : ℝ)*X 1 0+(750365181/2500000000 : ℝ)*X 1 1+(5024722619/10000000000 : ℝ)*X 1 2+(3948878229/10000000000 : ℝ)*X 2 0+(750365181/2500000000 : ℝ)*X 2 1+(5024722619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272119073/2500000000 : ℝ)*X 0 0+(501878951/1000000000 : ℝ)*X 0 1+(1111882099/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5199320681/10000000000 : ℝ)*X 1 0+(-417717973/5000000000 : ℝ)*X 1 1+(5559410483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199321057/10000000000 : ℝ)*X 2 0+(2779705159/5000000000 : ℝ)*X 2 1+(-167087129/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1976234757/5000000000 : ℝ)*X 0 0+(4974767163/10000000000 : ℝ)*X 0 1+(3052953321/10000000000 : ℝ)*X 0 2+(1976234757/5000000000 : ℝ)*X 1 0+(4974767163/10000000000 : ℝ)*X 1 1+(3052953321/10000000000 : ℝ)*X 1 2+(1976234757/5000000000 : ℝ)*X 2 0+(4974767163/10000000000 : ℝ)*X 2 1+(3052953321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4600056970066784559/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44044923/12500000000000 : ℝ)*(base1) + (1014317831/100000000000000 : ℝ)*(base19) + (9160119/20000000000000 : ℝ)*(base23) + (809971/10000000000000 : ℝ)*(base37) + (1384359/1000000000000 : ℝ)*(upper3) + (35175492807807/3125000000000 : ℝ)*(major0) + (35175492807807/3125000000000 : ℝ)*(major1) + (35175492807807/3125000000000 : ℝ)*(major2) + (1756978623357537/100000000000000 : ℝ)*(sp0) + (1756978739722933/100000000000000 : ℝ)*(sp1) + (219621966986457/12500000000000 : ℝ)*(sp2) + (9885025437291/2000000000000 : ℝ)*(sp3) + (1483042611/100000000000000 : ℝ)*(sp4) + (124135891/3125000000000 : ℝ)*(sp6) + (123562908080911/25000000000000 : ℝ)*(f.failure) + (439244938510191/25000000000000 : ℝ)*(f.sum) + (147275382843/3125000000000000000000000000 : ℝ)*base66 + (632183795751/195312500000000000000000000 : ℝ)*base67 + (10524061658609/3125000000000000000000000000 : ℝ)*base70 + (7590899341391/3125000000000000000000000000 : ℝ)*base71 + (55844442379/390625000000000000000000000 : ℝ)*base73 + (493199772437/97656250000000000000000000 : ℝ)*base76 + (1448655157127/390625000000000000000000000 : ℝ)*base77 + (12101404400383/1562500000000000000000000000 : ℝ)*base79 + (12086154702359/1562500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16590893/2500000000000000000000 : ℝ)*base90 + (16590893/2500000000000000000000 : ℝ)*base92 + (16590893/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31398484447222159200309/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1445045493/100000000000000 : ℝ)*(base19) + (1618526509/100000000000000 : ℝ)*(base23) + (156162107/100000000000000 : ℝ)*(base32) + (288171819/100000000000000 : ℝ)*(upper3) + (57181377/25000000000000 : ℝ)*(upper5) + (296258235874781/25000000000000 : ℝ)*(major0) + (296258235874781/25000000000000 : ℝ)*(major1) + (296258235874781/25000000000000 : ℝ)*(major2) + (3166663393/50000000000000 : ℝ)*(sp1) + (7706685553/100000000000000 : ℝ)*(sp2) + (924862084419951/50000000000000 : ℝ)*(sp4) + (1849716390467623/100000000000000 : ℝ)*(sp5) + (1849714843627839/100000000000000 : ℝ)*(sp6) + (260170613539533/50000000000000 : ℝ)*(sp7) + (520341383241173/100000000000000 : ℝ)*(f.failure) + (924862084419951/50000000000000 : ℝ)*(f.sum) + (4005849860989/6250000000000000000000000000 : ℝ)*base65 + (75838431489011/12500000000000000000000000000 : ℝ)*base68 + (124079830214011/12500000000000000000000000000 : ℝ)*base70 + (79835822526511/12500000000000000000000000000 : ℝ)*base72 + (18609356764011/6250000000000000000000000000 : ℝ)*base74 + (79341372351511/12500000000000000000000000000 : ℝ)*base76 + (20303226101511/12500000000000000000000000000 : ℝ)*base78 + (11096224101511/12500000000000000000000000000 : ℝ)*base80 + (31956566557761/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (56585601/10000000000000000000000 : ℝ)*base89 + (56585601/10000000000000000000000 : ℝ)*base91 + (56585601/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1770_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9901/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1770_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1770_s1_0 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1118774471/10000000000 : ℝ)*x 0 + (2736377907/5000000000 : ℝ)*x 1 + (5084711503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118774471/10000000000 : ℝ)^6095 ≤ (1797184672887/25000000000000 : ℝ)^5071 := by
    have hnat : (1118774471 : ℕ)^6095*25000000000000^5071 ≤ 1797184672887^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118774471 10000000000 1797184672887 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736377907/5000000000 : ℝ)^6095 ≤ (12113826857789/25000000000000 : ℝ)^5071 := by
    have hnat : (2736377907 : ℕ)^6095*25000000000000^5071 ≤ 12113826857789^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736377907 5000000000 12113826857789 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084711503/10000000000 : ℝ)^6095 ≤ (44355953855691/100000000000000 : ℝ)^5071 := by
    have hnat : (5084711503 : ℕ)^6095*100000000000000^5071 ≤ 44355953855691^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084711503 10000000000 44355953855691 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1118774471/10000000000 : ℝ), (2736377907/5000000000 : ℝ), (5084711503/10000000000 : ℝ)] ![(1797184672887/25000000000000 : ℝ), (12113826857789/25000000000000 : ℝ), (44355953855691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1118774471/10000000000 : ℝ)|^6095 ≤ (1797184672887/25000000000000 : ℝ)^5071
        have hw : |(-1118774471/10000000000 : ℝ)|=(1118774471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736377907/5000000000 : ℝ)|^6095 ≤ (12113826857789/25000000000000 : ℝ)^5071
        have hw : |(2736377907/5000000000 : ℝ)|=(2736377907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084711503/10000000000 : ℝ)|^6095 ≤ (44355953855691/100000000000000 : ℝ)^5071
        have hw : |(5084711503/10000000000 : ℝ)|=(5084711503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s1_1 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5322898561/10000000000 : ℝ)*x 0 + (-330289723/2500000000 : ℝ)*x 1 + (5084711933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5322898561/10000000000 : ℝ)^6095 ≤ (23432498491921/50000000000000 : ℝ)^5071 := by
    have hnat : (5322898561 : ℕ)^6095*50000000000000^5071 ≤ 23432498491921^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322898561 10000000000 23432498491921 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330289723/2500000000 : ℝ)^6095 ≤ (8779044642423/100000000000000 : ℝ)^5071 := by
    have hnat : (330289723 : ℕ)^6095*100000000000000^5071 ≤ 8779044642423^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330289723 2500000000 8779044642423 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084711933/10000000000 : ℝ)^6095 ≤ (44355958364213/100000000000000 : ℝ)^5071 := by
    have hnat : (5084711933 : ℕ)^6095*100000000000000^5071 ≤ 44355958364213^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084711933 10000000000 44355958364213 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5322898561/10000000000 : ℝ), (-330289723/2500000000 : ℝ), (5084711933/10000000000 : ℝ)] ![(23432498491921/50000000000000 : ℝ), (8779044642423/100000000000000 : ℝ), (44355958364213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5322898561/10000000000 : ℝ)|^6095 ≤ (23432498491921/50000000000000 : ℝ)^5071
        have hw : |(5322898561/10000000000 : ℝ)|=(5322898561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-330289723/2500000000 : ℝ)|^6095 ≤ (8779044642423/100000000000000 : ℝ)^5071
        have hw : |(-330289723/2500000000 : ℝ)|=(330289723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084711933/10000000000 : ℝ)|^6095 ≤ (44355958364213/100000000000000 : ℝ)^5071
        have hw : |(5084711933/10000000000 : ℝ)|=(5084711933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s1_2 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5322899227/10000000000 : ℝ)*x 0 + (5084711021/10000000000 : ℝ)*x 1 + (-660579603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5322899227/10000000000 : ℝ)^6095 ≤ (46865004031661/100000000000000 : ℝ)^5071 := by
    have hnat : (5322899227 : ℕ)^6095*100000000000000^5071 ≤ 46865004031661^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322899227 10000000000 46865004031661 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084711021/10000000000 : ℝ)^6095 ≤ (44355948801953/100000000000000 : ℝ)^5071 := by
    have hnat : (5084711021 : ℕ)^6095*100000000000000^5071 ≤ 44355948801953^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084711021 10000000000 44355948801953 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660579603/5000000000 : ℝ)^6095 ≤ (351161886011/4000000000000 : ℝ)^5071 := by
    have hnat : (660579603 : ℕ)^6095*4000000000000^5071 ≤ 351161886011^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660579603 5000000000 351161886011 4000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5322899227/10000000000 : ℝ), (5084711021/10000000000 : ℝ), (-660579603/5000000000 : ℝ)] ![(46865004031661/100000000000000 : ℝ), (44355948801953/100000000000000 : ℝ), (351161886011/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5322899227/10000000000 : ℝ)|^6095 ≤ (46865004031661/100000000000000 : ℝ)^5071
        have hw : |(5322899227/10000000000 : ℝ)|=(5322899227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084711021/10000000000 : ℝ)|^6095 ≤ (44355948801953/100000000000000 : ℝ)^5071
        have hw : |(5084711021/10000000000 : ℝ)|=(5084711021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-660579603/5000000000 : ℝ)|^6095 ≤ (351161886011/4000000000000 : ℝ)^5071
        have hw : |(-660579603/5000000000 : ℝ)|=(660579603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s1_3 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (796236683/2000000000 : ℝ)*x 0 + (1660595493/5000000000 : ℝ)*x 1 + (2350314277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796236683/2000000000 : ℝ)^6095 ≤ (16527669822519/50000000000000 : ℝ)^5071 := by
    have hnat : (796236683 : ℕ)^6095*50000000000000^5071 ≤ 16527669822519^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796236683 2000000000 16527669822519 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1660595493/5000000000 : ℝ)^6095 ≤ (1063377543803/4000000000000 : ℝ)^5071 := by
    have hnat : (1660595493 : ℕ)^6095*4000000000000^5071 ≤ 1063377543803^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660595493 5000000000 1063377543803 4000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2350314277/5000000000 : ℝ)^6095 ≤ (5045027718567/12500000000000 : ℝ)^5071 := by
    have hnat : (2350314277 : ℕ)^6095*12500000000000^5071 ≤ 5045027718567^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350314277 5000000000 5045027718567 12500000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796236683/2000000000 : ℝ), (1660595493/5000000000 : ℝ), (2350314277/5000000000 : ℝ)] ![(16527669822519/50000000000000 : ℝ), (1063377543803/4000000000000 : ℝ), (5045027718567/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796236683/2000000000 : ℝ)|^6095 ≤ (16527669822519/50000000000000 : ℝ)^5071
        have hw : |(796236683/2000000000 : ℝ)|=(796236683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1660595493/5000000000 : ℝ)|^6095 ≤ (1063377543803/4000000000000 : ℝ)^5071
        have hw : |(1660595493/5000000000 : ℝ)|=(1660595493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2350314277/5000000000 : ℝ)|^6095 ≤ (5045027718567/12500000000000 : ℝ)^5071
        have hw : |(2350314277/5000000000 : ℝ)|=(2350314277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s1_4 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1119093389/10000000000 : ℝ)*x 0 + (2545633119/5000000000 : ℝ)*x 1 + (2733032291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119093389/10000000000 : ℝ)^6095 ≤ (3595600895023/50000000000000 : ℝ)^5071 := by
    have hnat : (1119093389 : ℕ)^6095*50000000000000^5071 ≤ 3595600895023^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119093389 10000000000 3595600895023 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545633119/5000000000 : ℝ)^6095 ≤ (5553086095289/12500000000000 : ℝ)^5071 := by
    have hnat : (2545633119 : ℕ)^6095*12500000000000^5071 ≤ 5553086095289^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545633119 5000000000 5553086095289 12500000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733032291/5000000000 : ℝ)^6095 ≤ (1512003419503/3125000000000 : ℝ)^5071 := by
    have hnat : (2733032291 : ℕ)^6095*3125000000000^5071 ≤ 1512003419503^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733032291 5000000000 1512003419503 3125000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1119093389/10000000000 : ℝ), (2545633119/5000000000 : ℝ), (2733032291/5000000000 : ℝ)] ![(3595600895023/50000000000000 : ℝ), (5553086095289/12500000000000 : ℝ), (1512003419503/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1119093389/10000000000 : ℝ)|^6095 ≤ (3595600895023/50000000000000 : ℝ)^5071
        have hw : |(-1119093389/10000000000 : ℝ)|=(1119093389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2545633119/5000000000 : ℝ)|^6095 ≤ (5553086095289/12500000000000 : ℝ)^5071
        have hw : |(2545633119/5000000000 : ℝ)|=(2545633119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733032291/5000000000 : ℝ)|^6095 ≤ (1512003419503/3125000000000 : ℝ)^5071
        have hw : |(2733032291/5000000000 : ℝ)|=(2733032291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s1_5 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5220736449/10000000000 : ℝ)*x 0 + (-469902997/5000000000 : ℝ)*x 1 + (2733032189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5220736449/10000000000 : ℝ)^6095 ≤ (11446497899361/25000000000000 : ℝ)^5071 := by
    have hnat : (5220736449 : ℕ)^6095*25000000000000^5071 ≤ 11446497899361^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220736449 10000000000 11446497899361 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469902997/5000000000 : ℝ)^6095 ≤ (728737641657/12500000000000 : ℝ)^5071 := by
    have hnat : (469902997 : ℕ)^6095*12500000000000^5071 ≤ 728737641657^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469902997 5000000000 728737641657 12500000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733032189/5000000000 : ℝ)^6095 ≤ (48384107253703/100000000000000 : ℝ)^5071 := by
    have hnat : (2733032189 : ℕ)^6095*100000000000000^5071 ≤ 48384107253703^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733032189 5000000000 48384107253703 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5220736449/10000000000 : ℝ), (-469902997/5000000000 : ℝ), (2733032189/5000000000 : ℝ)] ![(11446497899361/25000000000000 : ℝ), (728737641657/12500000000000 : ℝ), (48384107253703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5220736449/10000000000 : ℝ)|^6095 ≤ (11446497899361/25000000000000 : ℝ)^5071
        have hw : |(5220736449/10000000000 : ℝ)|=(5220736449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469902997/5000000000 : ℝ)|^6095 ≤ (728737641657/12500000000000 : ℝ)^5071
        have hw : |(-469902997/5000000000 : ℝ)|=(469902997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733032189/5000000000 : ℝ)|^6095 ≤ (48384107253703/100000000000000 : ℝ)^5071
        have hw : |(2733032189/5000000000 : ℝ)|=(2733032189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s1_6 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2610368363/5000000000 : ℝ)*x 0 + (1366516069/2500000000 : ℝ)*x 1 + (-939805749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2610368363/5000000000 : ℝ)^6095 ≤ (2861624657331/6250000000000 : ℝ)^5071 := by
    have hnat : (2610368363 : ℕ)^6095*6250000000000^5071 ≤ 2861624657331^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610368363 5000000000 2861624657331 6250000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366516069/2500000000 : ℝ)^6095 ≤ (48384106168507/100000000000000 : ℝ)^5071 := by
    have hnat : (1366516069 : ℕ)^6095*100000000000000^5071 ≤ 48384106168507^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366516069 2500000000 48384106168507 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939805749/10000000000 : ℝ)^6095 ≤ (1457474826637/25000000000000 : ℝ)^5071 := by
    have hnat : (939805749 : ℕ)^6095*25000000000000^5071 ≤ 1457474826637^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939805749 10000000000 1457474826637 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2610368363/5000000000 : ℝ), (1366516069/2500000000 : ℝ), (-939805749/10000000000 : ℝ)] ![(2861624657331/6250000000000 : ℝ), (48384106168507/100000000000000 : ℝ), (1457474826637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2610368363/5000000000 : ℝ)|^6095 ≤ (2861624657331/6250000000000 : ℝ)^5071
        have hw : |(2610368363/5000000000 : ℝ)|=(2610368363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366516069/2500000000 : ℝ)|^6095 ≤ (48384106168507/100000000000000 : ℝ)^5071
        have hw : |(1366516069/2500000000 : ℝ)|=(1366516069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-939805749/10000000000 : ℝ)|^6095 ≤ (1457474826637/25000000000000 : ℝ)^5071
        have hw : |(-939805749/10000000000 : ℝ)|=(939805749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s1_7 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (497789743/1250000000 : ℝ)*x 0 + (4677325001/10000000000 : ℝ)*x 1 + (836245331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497789743/1250000000 : ℝ)^6095 ≤ (2066666376413/6250000000000 : ℝ)^5071 := by
    have hnat : (497789743 : ℕ)^6095*6250000000000^5071 ≤ 2066666376413^5071*1250000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497789743 1250000000 2066666376413 6250000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4677325001/10000000000 : ℝ)^6095 ≤ (250749066991/625000000000 : ℝ)^5071 := by
    have hnat : (4677325001 : ℕ)^6095*625000000000^5071 ≤ 250749066991^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4677325001 10000000000 250749066991 625000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (836245331/2500000000 : ℝ)^6095 ≤ (1675842953083/6250000000000 : ℝ)^5071 := by
    have hnat : (836245331 : ℕ)^6095*6250000000000^5071 ≤ 1675842953083^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836245331 2500000000 1675842953083 6250000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(497789743/1250000000 : ℝ), (4677325001/10000000000 : ℝ), (836245331/2500000000 : ℝ)] ![(2066666376413/6250000000000 : ℝ), (250749066991/625000000000 : ℝ), (1675842953083/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(497789743/1250000000 : ℝ)|^6095 ≤ (2066666376413/6250000000000 : ℝ)^5071
        have hw : |(497789743/1250000000 : ℝ)|=(497789743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4677325001/10000000000 : ℝ)|^6095 ≤ (250749066991/625000000000 : ℝ)^5071
        have hw : |(4677325001/10000000000 : ℝ)|=(4677325001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(836245331/2500000000 : ℝ)|^6095 ≤ (1675842953083/6250000000000 : ℝ)^5071
        have hw : |(836245331/2500000000 : ℝ)|=(836245331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1770_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17621/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9901/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9901/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9901/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9901/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9901/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9901/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7433/100000 : ℝ) ^ (6079/1024 : ℝ) ≤ (19890212238769/100000000000000000000 : ℝ) := by
    have hpowers : (7433/100000 : ℝ)^6079 ≤ (19890212238769/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7433 : ℕ)^6079*100000000000000000000^1024 ≤ 19890212238769^1024*100000^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7433 100000 19890212238769 100000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7433/100000 : ℝ)) (X := (19890212238769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9901/50000 : ℝ) ^ (6079/1024 : ℝ) ≤ (6681851640327771/100000000000000000000 : ℝ) := by
    have hpowers : (9901/50000 : ℝ)^6079 ≤ (6681851640327771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9901 : ℕ)^6079*100000000000000000000^1024 ≤ 6681851640327771^1024*50000^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9901 50000 6681851640327771 100000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9901/50000 : ℝ)) (X := (6681851640327771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000019890212238769/50000000000000000000 : ℝ) ≤ (10000000670096199/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (50000019890212238769/50000000000000000000 : ℝ)^1024 ≤ (10000000670096199/10000000000000000 : ℝ)^6079 := by
      have hnat : (50000019890212238769 : ℕ)^1024*10000000000000000^6079 ≤ 10000000670096199^6079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000019890212238769 50000000000000000000 10000000670096199 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000670096199/10000000000000000 : ℝ)) (X := (50000019890212238769/50000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5000335087092628327/5000000000000000000 : ℝ) ≤ (5000056443431851/5000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (5000335087092628327/5000000000000000000 : ℝ)^1024 ≤ (5000056443431851/5000000000000000 : ℝ)^6079 := by
      have hnat : (5000335087092628327 : ℕ)^1024*5000000000000000^6079 ≤ 5000056443431851^6079*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000335087092628327 5000000000000000000 5000056443431851 5000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000056443431851/5000000000000000 : ℝ)) (X := (5000335087092628327/5000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50006681851640327771/50000000000000000000 : ℝ) ≤ (2000045020726241/2000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (50006681851640327771/50000000000000000000 : ℝ)^1024 ≤ (2000045020726241/2000000000000000 : ℝ)^6079 := by
      have hnat : (50006681851640327771 : ℕ)^1024*2000000000000000^6079 ≤ 2000045020726241^6079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006681851640327771 50000000000000000000 2000045020726241 2000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000045020726241/2000000000000000 : ℝ)) (X := (50006681851640327771/50000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19890212238769/100000000000000000000 : ℝ) ≤ ((123688340073954185833/123690000000000000000 : ℝ)+2*(112216767503/1236900000000000 : ℝ)*(7433/100000 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (123688340073954185833/123690000000000000000 : ℝ)+2*(112216767503/1236900000000000 : ℝ)*(7433/100000 : ℝ)=(10000000670096199/10000000000000000 : ℝ) by norm_num, show 1+2*(19890212238769/100000000000000000000 : ℝ)=(50000019890212238769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6681851640327771/100000000000000000000 : ℝ)+(19890212238769/100000000000000000000 : ℝ) ≤ ((123688340073954185833/123690000000000000000 : ℝ)+(112216767503/1236900000000000 : ℝ)*((9901/50000 : ℝ)+(7433/100000 : ℝ)))^(6079/1024 : ℝ) := by
    rw [show (123688340073954185833/123690000000000000000 : ℝ)+(112216767503/1236900000000000 : ℝ)*((9901/50000 : ℝ)+(7433/100000 : ℝ))=(5000056443431851/5000000000000000 : ℝ) by norm_num, show 1+(6681851640327771/100000000000000000000 : ℝ)+(19890212238769/100000000000000000000 : ℝ)=(5000335087092628327/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6681851640327771/100000000000000000000 : ℝ) ≤ ((123688340073954185833/123690000000000000000 : ℝ)+2*(112216767503/1236900000000000 : ℝ)*(9901/50000 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (123688340073954185833/123690000000000000000 : ℝ)+2*(112216767503/1236900000000000 : ℝ)*(9901/50000 : ℝ)=(2000045020726241/2000000000000000 : ℝ) by norm_num, show 1+2*(6681851640327771/100000000000000000000 : ℝ)=(50006681851640327771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (123688340073954185833/123690000000000000000 : ℝ)*(X 1 0+X 2 0)+(112216767503/1236900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (7433/100000 : ℝ)) (hi := (9901/50000 : ℝ)) (c := (123688340073954185833/123690000000000000000 : ℝ)) (alpha := (112216767503/1236900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (123688340073954185833/123690000000000000000 : ℝ)*(X 0 1+X 2 1)+(112216767503/1236900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (7433/100000 : ℝ)) (hi := (9901/50000 : ℝ)) (c := (123688340073954185833/123690000000000000000 : ℝ)) (alpha := (112216767503/1236900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (123688340073954185833/123690000000000000000 : ℝ)*(X 0 2+X 1 2)+(112216767503/1236900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (7433/100000 : ℝ)) (hi := (9901/50000 : ℝ)) (c := (123688340073954185833/123690000000000000000 : ℝ)) (alpha := (112216767503/1236900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1118774471/10000000000 : ℝ)*X 0 0+(2736377907/5000000000 : ℝ)*X 0 1+(5084711503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5322898561/10000000000 : ℝ)*X 1 0+(-330289723/2500000000 : ℝ)*X 1 1+(5084711933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5322899227/10000000000 : ℝ)*X 2 0+(5084711021/10000000000 : ℝ)*X 2 1+(-660579603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((796236683/2000000000 : ℝ)*X 0 0+(1660595493/5000000000 : ℝ)*X 0 1+(2350314277/5000000000 : ℝ)*X 0 2+(796236683/2000000000 : ℝ)*X 1 0+(1660595493/5000000000 : ℝ)*X 1 1+(2350314277/5000000000 : ℝ)*X 1 2+(796236683/2000000000 : ℝ)*X 2 0+(1660595493/5000000000 : ℝ)*X 2 1+(2350314277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1119093389/10000000000 : ℝ)*X 0 0+(2545633119/5000000000 : ℝ)*X 0 1+(2733032291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5220736449/10000000000 : ℝ)*X 1 0+(-469902997/5000000000 : ℝ)*X 1 1+(2733032189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2610368363/5000000000 : ℝ)*X 2 0+(1366516069/2500000000 : ℝ)*X 2 1+(-939805749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((497789743/1250000000 : ℝ)*X 0 0+(4677325001/10000000000 : ℝ)*X 0 1+(836245331/2500000000 : ℝ)*X 0 2+(497789743/1250000000 : ℝ)*X 1 0+(4677325001/10000000000 : ℝ)*X 1 1+(836245331/2500000000 : ℝ)*X 1 2+(497789743/1250000000 : ℝ)*X 2 0+(4677325001/10000000000 : ℝ)*X 2 1+(836245331/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6934280305066704601691217/1085000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133207339/20000000000000 : ℝ)*(base19) + (957485007/100000000000000 : ℝ)*(base23) + (255067841/100000000000000 : ℝ)*(upper3) + (16495591/100000000000000 : ℝ)*(upper4) + (3672979/4000000000000 : ℝ)*(upper5) + (33019765601869/2000000000000 : ℝ)*(major0) + (33019765601869/2000000000000 : ℝ)*(major1) + (33019765601869/2000000000000 : ℝ)*(major2) + (644257940470179/25000000000000 : ℝ)*(sp0) + (515407179543657/20000000000000 : ℝ)*(sp1) + (2577035606269973/100000000000000 : ℝ)*(sp2) + (724935955636419/100000000000000 : ℝ)*(sp3) + (600234283/12500000000000 : ℝ)*(sp4) + (956940193/25000000000000 : ℝ)*(sp7) + (724939783397191/100000000000000 : ℝ)*(f.failure) + (128851828187749/5000000000000 : ℝ)*(f.sum) + (48317015415979/12369000000000000000000000000 : ℝ)*base66 + (43521826867679137/11780000000000000000000000000000 : ℝ)*base67 + (2052195240960863/11780000000000000000000000000000 : ℝ)*base70 + (78399933350399137/11780000000000000000000000000000 : ℝ)*base71 + (2254709780633/1546125000000000000000000000 : ℝ)*base74 + (45244491695019137/11780000000000000000000000000000 : ℝ)*base75 + (40407984575319137/11780000000000000000000000000000 : ℝ)*base77 + (79725409514619137/11780000000000000000000000000000 : ℝ)*base79 + (37858208607017/6184500000000000000000000000 : ℝ)*base82 + (20103467/10000000000000000000000 : ℝ)*base89 + (20103467/10000000000000000000000 : ℝ)*base91 + (20103467/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11017214891605721605621/1085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1131214463/100000000000000 : ℝ)*(base19) + (1433513093/100000000000000 : ℝ)*(base23) + (87554497/50000000000000 : ℝ)*(upper3) + (11627657/20000000000000 : ℝ)*(lower4) + (183661507/100000000000000 : ℝ)*(upper5) + (427332331532713/25000000000000 : ℝ)*(major0) + (427332331532713/25000000000000 : ℝ)*(major1) + (427332331532713/25000000000000 : ℝ)*(major2) + (1857514607/25000000000000 : ℝ)*(sp1) + (4976607899/50000000000000 : ℝ)*(sp2) + (667025325283381/25000000000000 : ℝ)*(sp4) + (333511592482579/12500000000000 : ℝ)*(sp5) + (333511239300579/12500000000000 : ℝ)*(sp6) + (750557012657671/100000000000000 : ℝ)*(sp7) + (750557012657671/100000000000000 : ℝ)*(f.failure) + (667025325283381/25000000000000 : ℝ)*(f.sum) + (1071486997123/406875000000000000000000000 : ℝ)*base65 + (12796775169416529/7750000000000000000000000000000 : ℝ)*base68 + (45297082084166529/7750000000000000000000000000000 : ℝ)*base70 + (9597194776166529/7750000000000000000000000000000 : ℝ)*base72 + (9630138469739/3255000000000000000000000000 : ℝ)*base73 + (24380523212833471/7750000000000000000000000000000 : ℝ)*base75 + (30426865683333471/7750000000000000000000000000000 : ℝ)*base77 + (7392955376083471/7750000000000000000000000000000 : ℝ)*base79 + (2547721110829/813750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17386773/10000000000000000000000 : ℝ)*base90 + (17386773/10000000000000000000000 : ℝ)*base92 + (17386773/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1770_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17621/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1770_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1770_s2_0 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1119193349/10000000000 : ℝ)*x 0 + (2735702617/5000000000 : ℝ)*x 1 + (2542886841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119193349/10000000000 : ℝ)^6095 ≤ (7191973840013/100000000000000 : ℝ)^5071 := by
    have hnat : (1119193349 : ℕ)^6095*100000000000000^5071 ≤ 7191973840013^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119193349 10000000000 7191973840013 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735702617/5000000000 : ℝ)^6095 ≤ (24220467588743/50000000000000 : ℝ)^5071 := by
    have hnat : (2735702617 : ℕ)^6095*50000000000000^5071 ≤ 24220467588743^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735702617 5000000000 24220467588743 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542886841/5000000000 : ℝ)^6095 ≤ (22183545483699/50000000000000 : ℝ)^5071 := by
    have hnat : (2542886841 : ℕ)^6095*50000000000000^5071 ≤ 22183545483699^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542886841 5000000000 22183545483699 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1119193349/10000000000 : ℝ), (2735702617/5000000000 : ℝ), (2542886841/5000000000 : ℝ)] ![(7191973840013/100000000000000 : ℝ), (24220467588743/50000000000000 : ℝ), (22183545483699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1119193349/10000000000 : ℝ)|^6095 ≤ (7191973840013/100000000000000 : ℝ)^5071
        have hw : |(-1119193349/10000000000 : ℝ)|=(1119193349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735702617/5000000000 : ℝ)|^6095 ≤ (24220467588743/50000000000000 : ℝ)^5071
        have hw : |(2735702617/5000000000 : ℝ)|=(2735702617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542886841/5000000000 : ℝ)|^6095 ≤ (22183545483699/50000000000000 : ℝ)^5071
        have hw : |(2542886841/5000000000 : ℝ)|=(2542886841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s2_1 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1330629839/2500000000 : ℝ)*x 0 + (-132026739/1000000000 : ℝ)*x 1 + (63572171/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1330629839/2500000000 : ℝ)^6095 ≤ (11715246036907/25000000000000 : ℝ)^5071 := by
    have hnat : (1330629839 : ℕ)^6095*25000000000000^5071 ≤ 11715246036907^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330629839 2500000000 11715246036907 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132026739/1000000000 : ℝ)^6095 ≤ (1754384977543/20000000000000 : ℝ)^5071 := by
    have hnat : (132026739 : ℕ)^6095*20000000000000^5071 ≤ 1754384977543^5071*1000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132026739 1000000000 1754384977543 20000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63572171/125000000 : ℝ)^6095 ≤ (44367090946427/100000000000000 : ℝ)^5071 := by
    have hnat : (63572171 : ℕ)^6095*100000000000000^5071 ≤ 44367090946427^5071*125000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63572171 125000000 44367090946427 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1330629839/2500000000 : ℝ), (-132026739/1000000000 : ℝ), (63572171/125000000 : ℝ)] ![(11715246036907/25000000000000 : ℝ), (1754384977543/20000000000000 : ℝ), (44367090946427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1330629839/2500000000 : ℝ)|^6095 ≤ (11715246036907/25000000000000 : ℝ)^5071
        have hw : |(1330629839/2500000000 : ℝ)|=(1330629839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132026739/1000000000 : ℝ)|^6095 ≤ (1754384977543/20000000000000 : ℝ)^5071
        have hw : |(-132026739/1000000000 : ℝ)|=(132026739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63572171/125000000 : ℝ)|^6095 ≤ (44367090946427/100000000000000 : ℝ)^5071
        have hw : |(63572171/125000000 : ℝ)|=(63572171/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s2_2 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064503871/2000000000 : ℝ)*x 0 + (63572171/125000000 : ℝ)*x 1 + (-10314589/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064503871/2000000000 : ℝ)^6095 ≤ (23430492068523/50000000000000 : ℝ)^5071 := by
    have hnat : (1064503871 : ℕ)^6095*50000000000000^5071 ≤ 23430492068523^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064503871 2000000000 23430492068523 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63572171/125000000 : ℝ)^6095 ≤ (44367090946427/100000000000000 : ℝ)^5071 := by
    have hnat : (63572171 : ℕ)^6095*100000000000000^5071 ≤ 44367090946427^5071*125000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63572171 125000000 44367090946427 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10314589/78125000 : ℝ)^6095 ≤ (8771924903687/100000000000000 : ℝ)^5071 := by
    have hnat : (10314589 : ℕ)^6095*100000000000000^5071 ≤ 8771924903687^5071*78125000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10314589 78125000 8771924903687 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064503871/2000000000 : ℝ), (63572171/125000000 : ℝ), (-10314589/78125000 : ℝ)] ![(23430492068523/50000000000000 : ℝ), (44367090946427/100000000000000 : ℝ), (8771924903687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064503871/2000000000 : ℝ)|^6095 ≤ (23430492068523/50000000000000 : ℝ)^5071
        have hw : |(1064503871/2000000000 : ℝ)|=(1064503871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63572171/125000000 : ℝ)|^6095 ≤ (44367090946427/100000000000000 : ℝ)^5071
        have hw : |(63572171/125000000 : ℝ)|=(63572171/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10314589/78125000 : ℝ)|^6095 ≤ (8771924903687/100000000000000 : ℝ)^5071
        have hw : |(-10314589/78125000 : ℝ)|=(10314589/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s2_3 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (159261189/400000000 : ℝ)*x 0 + (207841211/625000000 : ℝ)*x 1 + (4696313509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159261189/400000000 : ℝ)^6095 ≤ (33058795682041/100000000000000 : ℝ)^5071 := by
    have hnat : (159261189 : ℕ)^6095*100000000000000^5071 ≤ 33058795682041^5071*400000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159261189 400000000 33058795682041 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207841211/625000000 : ℝ)^6095 ≤ (2662550949017/10000000000000 : ℝ)^5071 := by
    have hnat : (207841211 : ℕ)^6095*10000000000000^5071 ≤ 2662550949017^5071*625000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207841211 625000000 2662550949017 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4696313509/10000000000 : ℝ)^6095 ≤ (40315694816373/100000000000000 : ℝ)^5071 := by
    have hnat : (4696313509 : ℕ)^6095*100000000000000^5071 ≤ 40315694816373^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696313509 10000000000 40315694816373 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(159261189/400000000 : ℝ), (207841211/625000000 : ℝ), (4696313509/10000000000 : ℝ)] ![(33058795682041/100000000000000 : ℝ), (2662550949017/10000000000000 : ℝ), (40315694816373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(159261189/400000000 : ℝ)|^6095 ≤ (33058795682041/100000000000000 : ℝ)^5071
        have hw : |(159261189/400000000 : ℝ)|=(159261189/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207841211/625000000 : ℝ)|^6095 ≤ (2662550949017/10000000000000 : ℝ)^5071
        have hw : |(207841211/625000000 : ℝ)|=(207841211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4696313509/10000000000 : ℝ)|^6095 ≤ (40315694816373/100000000000000 : ℝ)^5071
        have hw : |(4696313509/10000000000 : ℝ)|=(4696313509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s2_4 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1119506707/10000000000 : ℝ)*x 0 + (101844953/200000000 : ℝ)*x 1 + (5464797039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119506707/10000000000 : ℝ)^6095 ≤ (56206204521/781250000000 : ℝ)^5071 := by
    have hnat : (1119506707 : ℕ)^6095*781250000000^5071 ≤ 56206204521^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119506707 10000000000 56206204521 781250000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101844953/200000000 : ℝ)^6095 ≤ (11108745420007/25000000000000 : ℝ)^5071 := by
    have hnat : (101844953 : ℕ)^6095*25000000000000^5071 ≤ 11108745420007^5071*200000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101844953 200000000 11108745420007 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464797039/10000000000 : ℝ)^6095 ≤ (12092656030929/25000000000000 : ℝ)^5071 := by
    have hnat : (5464797039 : ℕ)^6095*25000000000000^5071 ≤ 12092656030929^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464797039 10000000000 12092656030929 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1119506707/10000000000 : ℝ), (101844953/200000000 : ℝ), (5464797039/10000000000 : ℝ)] ![(56206204521/781250000000 : ℝ), (11108745420007/25000000000000 : ℝ), (12092656030929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1119506707/10000000000 : ℝ)|^6095 ≤ (56206204521/781250000000 : ℝ)^5071
        have hw : |(-1119506707/10000000000 : ℝ)|=(1119506707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(101844953/200000000 : ℝ)|^6095 ≤ (11108745420007/25000000000000 : ℝ)^5071
        have hw : |(101844953/200000000 : ℝ)|=(101844953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464797039/10000000000 : ℝ)|^6095 ≤ (12092656030929/25000000000000 : ℝ)^5071
        have hw : |(5464797039/10000000000 : ℝ)|=(5464797039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s2_5 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2610499119/5000000000 : ℝ)*x 0 + (-941244033/10000000000 : ℝ)*x 1 + (5464797039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2610499119/5000000000 : ℝ)^6095 ≤ (22894375561901/50000000000000 : ℝ)^5071 := by
    have hnat : (2610499119 : ℕ)^6095*50000000000000^5071 ≤ 22894375561901^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610499119 5000000000 22894375561901 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941244033/10000000000 : ℝ)^6095 ≤ (5840624738193/100000000000000 : ℝ)^5071 := by
    have hnat : (941244033 : ℕ)^6095*100000000000000^5071 ≤ 5840624738193^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941244033 10000000000 5840624738193 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464797039/10000000000 : ℝ)^6095 ≤ (12092656030929/25000000000000 : ℝ)^5071 := by
    have hnat : (5464797039 : ℕ)^6095*25000000000000^5071 ≤ 12092656030929^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464797039 10000000000 12092656030929 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2610499119/5000000000 : ℝ), (-941244033/10000000000 : ℝ), (5464797039/10000000000 : ℝ)] ![(22894375561901/50000000000000 : ℝ), (5840624738193/100000000000000 : ℝ), (12092656030929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2610499119/5000000000 : ℝ)|^6095 ≤ (22894375561901/50000000000000 : ℝ)^5071
        have hw : |(2610499119/5000000000 : ℝ)|=(2610499119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941244033/10000000000 : ℝ)|^6095 ≤ (5840624738193/100000000000000 : ℝ)^5071
        have hw : |(-941244033/10000000000 : ℝ)|=(941244033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464797039/10000000000 : ℝ)|^6095 ≤ (12092656030929/25000000000000 : ℝ)^5071
        have hw : |(5464797039/10000000000 : ℝ)|=(5464797039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s2_6 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2610499119/5000000000 : ℝ)*x 0 + (5464797039/10000000000 : ℝ)*x 1 + (-941244033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2610499119/5000000000 : ℝ)^6095 ≤ (22894375561901/50000000000000 : ℝ)^5071 := by
    have hnat : (2610499119 : ℕ)^6095*50000000000000^5071 ≤ 22894375561901^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610499119 5000000000 22894375561901 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464797039/10000000000 : ℝ)^6095 ≤ (12092656030929/25000000000000 : ℝ)^5071 := by
    have hnat : (5464797039 : ℕ)^6095*25000000000000^5071 ≤ 12092656030929^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464797039 10000000000 12092656030929 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941244033/10000000000 : ℝ)^6095 ≤ (5840624738193/100000000000000 : ℝ)^5071 := by
    have hnat : (941244033 : ℕ)^6095*100000000000000^5071 ≤ 5840624738193^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941244033 10000000000 5840624738193 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2610499119/5000000000 : ℝ), (5464797039/10000000000 : ℝ), (-941244033/10000000000 : ℝ)] ![(22894375561901/50000000000000 : ℝ), (12092656030929/25000000000000 : ℝ), (5840624738193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2610499119/5000000000 : ℝ)|^6095 ≤ (22894375561901/50000000000000 : ℝ)^5071
        have hw : |(2610499119/5000000000 : ℝ)|=(2610499119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464797039/10000000000 : ℝ)|^6095 ≤ (12092656030929/25000000000000 : ℝ)^5071
        have hw : |(5464797039/10000000000 : ℝ)|=(5464797039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941244033/10000000000 : ℝ)|^6095 ≤ (5840624738193/100000000000000 : ℝ)^5071
        have hw : |(-941244033/10000000000 : ℝ)|=(941244033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s2_7 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1991321829/5000000000 : ℝ)*x 0 + (2336649829/5000000000 : ℝ)*x 1 + (3348950381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991321829/5000000000 : ℝ)^6095 ≤ (3306991270499/10000000000000 : ℝ)^5071 := by
    have hnat : (1991321829 : ℕ)^6095*10000000000000^5071 ≤ 3306991270499^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991321829 5000000000 3306991270499 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2336649829/5000000000 : ℝ)^6095 ≤ (10019588661233/25000000000000 : ℝ)^5071 := by
    have hnat : (2336649829 : ℕ)^6095*25000000000000^5071 ≤ 10019588661233^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336649829 5000000000 10019588661233 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3348950381/10000000000 : ℝ)^6095 ≤ (5370346527069/20000000000000 : ℝ)^5071 := by
    have hnat : (3348950381 : ℕ)^6095*20000000000000^5071 ≤ 5370346527069^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3348950381 10000000000 5370346527069 20000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1991321829/5000000000 : ℝ), (2336649829/5000000000 : ℝ), (3348950381/10000000000 : ℝ)] ![(3306991270499/10000000000000 : ℝ), (10019588661233/25000000000000 : ℝ), (5370346527069/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1991321829/5000000000 : ℝ)|^6095 ≤ (3306991270499/10000000000000 : ℝ)^5071
        have hw : |(1991321829/5000000000 : ℝ)|=(1991321829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2336649829/5000000000 : ℝ)|^6095 ≤ (10019588661233/25000000000000 : ℝ)^5071
        have hw : |(2336649829/5000000000 : ℝ)|=(2336649829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3348950381/10000000000 : ℝ)|^6095 ≤ (5370346527069/20000000000000 : ℝ)^5071
        have hw : |(3348950381/10000000000 : ℝ)|=(3348950381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1770_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2199/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4613/50000 : ℝ) ^ (6079/1024 : ℝ) ≤ (35871380804061/50000000000000000000 : ℝ) := by
    have hpowers : (4613/50000 : ℝ)^6079 ≤ (35871380804061/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4613 : ℕ)^6079*50000000000000000000^1024 ≤ 35871380804061^1024*50000^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4613 50000 35871380804061 50000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4613/50000 : ℝ)) (X := (35871380804061/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17621/100000 : ℝ) ^ (6079/1024 : ℝ) ≤ (1671139483676323/50000000000000000000 : ℝ) := by
    have hpowers : (17621/100000 : ℝ)^6079 ≤ (1671139483676323/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17621 : ℕ)^6079*50000000000000000000^1024 ≤ 1671139483676323^1024*100000^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17621 100000 1671139483676323 50000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17621/100000 : ℝ)) (X := (1671139483676323/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000035871380804061/25000000000000000000 : ℝ) ≤ (10000002416994377/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (25000035871380804061/25000000000000000000 : ℝ)^1024 ≤ (10000002416994377/10000000000000000 : ℝ)^6079 := by
      have hnat : (25000035871380804061 : ℕ)^1024*10000000000000000^6079 ≤ 10000002416994377^6079*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000035871380804061 25000000000000000000 10000002416994377 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002416994377/10000000000000000 : ℝ)) (X := (25000035871380804061/25000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (390638336022378753/390625000000000000 : ℝ) ≤ (10000057507955709/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (390638336022378753/390625000000000000 : ℝ)^1024 ≤ (10000057507955709/10000000000000000 : ℝ)^6079 := by
      have hnat : (390638336022378753 : ℕ)^1024*10000000000000000^6079 ≤ 10000057507955709^6079*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390638336022378753 390625000000000000 10000057507955709 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057507955709/10000000000000000 : ℝ)) (X := (390638336022378753/390625000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25001671139483676323/25000000000000000000 : ℝ) ≤ (10000112598917041/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (25001671139483676323/25000000000000000000 : ℝ)^1024 ≤ (10000112598917041/10000000000000000 : ℝ)^6079 := by
      have hnat : (25001671139483676323 : ℕ)^1024*10000000000000000^6079 ≤ 10000112598917041^6079*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001671139483676323 25000000000000000000 10000112598917041 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000112598917041/10000000000000000 : ℝ)) (X := (25001671139483676323/25000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(35871380804061/50000000000000000000 : ℝ) ≤ ((83949003752249296851/83950000000000000000 : ℝ)+2*(13772740333/209875000000000 : ℝ)*(4613/50000 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (83949003752249296851/83950000000000000000 : ℝ)+2*(13772740333/209875000000000 : ℝ)*(4613/50000 : ℝ)=(10000002416994377/10000000000000000 : ℝ) by norm_num, show 1+2*(35871380804061/50000000000000000000 : ℝ)=(25000035871380804061/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1671139483676323/50000000000000000000 : ℝ)+(35871380804061/50000000000000000000 : ℝ) ≤ ((83949003752249296851/83950000000000000000 : ℝ)+(13772740333/209875000000000 : ℝ)*((17621/100000 : ℝ)+(4613/50000 : ℝ)))^(6079/1024 : ℝ) := by
    rw [show (83949003752249296851/83950000000000000000 : ℝ)+(13772740333/209875000000000 : ℝ)*((17621/100000 : ℝ)+(4613/50000 : ℝ))=(10000057507955709/10000000000000000 : ℝ) by norm_num, show 1+(1671139483676323/50000000000000000000 : ℝ)+(35871380804061/50000000000000000000 : ℝ)=(390638336022378753/390625000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1671139483676323/50000000000000000000 : ℝ) ≤ ((83949003752249296851/83950000000000000000 : ℝ)+2*(13772740333/209875000000000 : ℝ)*(17621/100000 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (83949003752249296851/83950000000000000000 : ℝ)+2*(13772740333/209875000000000 : ℝ)*(17621/100000 : ℝ)=(10000112598917041/10000000000000000 : ℝ) by norm_num, show 1+2*(1671139483676323/50000000000000000000 : ℝ)=(25001671139483676323/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (83949003752249296851/83950000000000000000 : ℝ)*(X 1 0+X 2 0)+(13772740333/209875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (4613/50000 : ℝ)) (hi := (17621/100000 : ℝ)) (c := (83949003752249296851/83950000000000000000 : ℝ)) (alpha := (13772740333/209875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (83949003752249296851/83950000000000000000 : ℝ)*(X 0 1+X 2 1)+(13772740333/209875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (4613/50000 : ℝ)) (hi := (17621/100000 : ℝ)) (c := (83949003752249296851/83950000000000000000 : ℝ)) (alpha := (13772740333/209875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (83949003752249296851/83950000000000000000 : ℝ)*(X 0 2+X 1 2)+(13772740333/209875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (4613/50000 : ℝ)) (hi := (17621/100000 : ℝ)) (c := (83949003752249296851/83950000000000000000 : ℝ)) (alpha := (13772740333/209875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1119193349/10000000000 : ℝ)*X 0 0+(2735702617/5000000000 : ℝ)*X 0 1+(2542886841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1330629839/2500000000 : ℝ)*X 1 0+(-132026739/1000000000 : ℝ)*X 1 1+(63572171/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1064503871/2000000000 : ℝ)*X 2 0+(63572171/125000000 : ℝ)*X 2 1+(-10314589/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((159261189/400000000 : ℝ)*X 0 0+(207841211/625000000 : ℝ)*X 0 1+(4696313509/10000000000 : ℝ)*X 0 2+(159261189/400000000 : ℝ)*X 1 0+(207841211/625000000 : ℝ)*X 1 1+(4696313509/10000000000 : ℝ)*X 1 2+(159261189/400000000 : ℝ)*X 2 0+(207841211/625000000 : ℝ)*X 2 1+(4696313509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1119506707/10000000000 : ℝ)*X 0 0+(101844953/200000000 : ℝ)*X 0 1+(5464797039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2610499119/5000000000 : ℝ)*X 1 0+(-941244033/10000000000 : ℝ)*X 1 1+(5464797039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2610499119/5000000000 : ℝ)*X 2 0+(5464797039/10000000000 : ℝ)*X 2 1+(-941244033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1991321829/5000000000 : ℝ)*X 0 0+(2336649829/5000000000 : ℝ)*X 0 1+(3348950381/10000000000 : ℝ)*X 0 2+(1991321829/5000000000 : ℝ)*X 1 0+(2336649829/5000000000 : ℝ)*X 1 1+(3348950381/10000000000 : ℝ)*X 1 2+(1991321829/5000000000 : ℝ)*X 2 0+(2336649829/5000000000 : ℝ)*X 2 1+(3348950381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31095026820706261393543809441/2098750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48818823/2500000000000 : ℝ)*(base19) + (1847993349/100000000000000 : ℝ)*(base23) + (55499167/100000000000000 : ℝ)*(lower2) + (70056881/20000000000000 : ℝ)*(upper3) + (138293873/50000000000000 : ℝ)*(upper5) + (830665716151303/50000000000000 : ℝ)*(major0) + (830665716151303/50000000000000 : ℝ)*(major1) + (830665716151303/50000000000000 : ℝ)*(major2) + (648291225922957/25000000000000 : ℝ)*(sp0) + (648294753476283/25000000000000 : ℝ)*(sp1) + (2593179118664703/100000000000000 : ℝ)*(sp2) + (182369127439111/25000000000000 : ℝ)*(sp3) + (1003935389/6250000000000 : ℝ)*(sp4) + (489432489/10000000000000 : ℝ)*(sp7) + (364740702040667/50000000000000 : ℝ)*(f.failure) + (648295241664513/25000000000000 : ℝ)*(f.sum) + (29907364750173/10493750000000000000000000000 : ℝ)*base65 + (12865177250172953147/4197500000000000000000000000000000 : ℝ)*base68 + (28801900017932046853/4197500000000000000000000000000000 : ℝ)*base69 + (3843375471882953147/4197500000000000000000000000000000 : ℝ)*base72 + (57193193792427/10493750000000000000000000000 : ℝ)*base74 + (18772207451152046853/4197500000000000000000000000000000 : ℝ)*base75 + (16073377650449546853/4197500000000000000000000000000000 : ℝ)*base77 + (14725763899447046853/4197500000000000000000000000000000 : ℝ)*base79 + (32795603961971/20987500000000000000000000000 : ℝ)*base81 + (35018479/5000000000000000000000 : ℝ)*base89 + (35018479/5000000000000000000000 : ℝ)*base91 + (35018479/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20346935591201857281799782669/2098750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (300645647/25000000000000 : ℝ)*(base19) + (1284300763/100000000000000 : ℝ)*(base23) + (336499573/100000000000000 : ℝ)*(lower1) + (104448019/50000000000000 : ℝ)*(upper3) + (36291237/100000000000000 : ℝ)*(lower4) + (25173021/12500000000000 : ℝ)*(upper5) + (1719641902910827/100000000000000 : ℝ)*(major0) + (1719641902910827/100000000000000 : ℝ)*(major1) + (1719641902910827/100000000000000 : ℝ)*(major2) + (627830691/100000000000000 : ℝ)*(sp2) + (2684198274821367/100000000000000 : ℝ)*(sp4) + (2684197072238779/100000000000000 : ℝ)*(sp5) + (1342098181344957/50000000000000 : ℝ)*(sp6) + (755085207840691/100000000000000 : ℝ)*(sp7) + (755085207840691/100000000000000 : ℝ)*(f.failure) + (2684198274821367/100000000000000 : ℝ)*(f.sum) + (185088726343789/41975000000000000000000000000 : ℝ)*base65 + (69211960626001305777/8395000000000000000000000000000000 : ℝ)*base67 + (53377610857381305777/8395000000000000000000000000000000 : ℝ)*base69 + (2681267858461305777/8395000000000000000000000000000000 : ℝ)*base71 + (219434822058839/41975000000000000000000000000 : ℝ)*base73 + (20262332301521305777/8395000000000000000000000000000000 : ℝ)*base75 + (2109124273363694223/8395000000000000000000000000000000 : ℝ)*base78 + (22108959027481305777/8395000000000000000000000000000000 : ℝ)*base79 + (117770773243489/41975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (64587033/10000000000000000000000 : ℝ)*base90 + (64587033/10000000000000000000000 : ℝ)*base92 + (64587033/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1770_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1770_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1770_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1770_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1770_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1770_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1770_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
