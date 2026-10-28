-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1116_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:07:21.009676+00:00
-- url     : https://prove2.me/submissions/90edab3f-1a28-487c-84de-fbb7b6919acd

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
theorem support_rectangle_w1116_s3_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-5438209/25000000 : ℝ)*x 0 + (5431915503/10000000000 : ℝ)*x 1 + (2614788401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5438209/25000000 : ℝ)^8309 ≤ (13207313461079/100000000000000 : ℝ)^6261 := by
    have hnat : (5438209 : ℕ)^8309*100000000000000^6261 ≤ 13207313461079^6261*25000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438209 25000000 13207313461079 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431915503/10000000000 : ℝ)^8309 ≤ (22244620415257/50000000000000 : ℝ)^6261 := by
    have hnat : (5431915503 : ℕ)^8309*50000000000000^6261 ≤ 22244620415257^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431915503 10000000000 22244620415257 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614788401/5000000000 : ℝ)^8309 ≤ (10575861423261/25000000000000 : ℝ)^6261 := by
    have hnat : (2614788401 : ℕ)^8309*25000000000000^6261 ≤ 10575861423261^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614788401 5000000000 10575861423261 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5438209/25000000 : ℝ), (5431915503/10000000000 : ℝ), (2614788401/5000000000 : ℝ)] ![(13207313461079/100000000000000 : ℝ), (22244620415257/50000000000000 : ℝ), (10575861423261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5438209/25000000 : ℝ)|^8309 ≤ (13207313461079/100000000000000 : ℝ)^6261
        have hw : |(-5438209/25000000 : ℝ)|=(5438209/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431915503/10000000000 : ℝ)|^8309 ≤ (22244620415257/50000000000000 : ℝ)^6261
        have hw : |(5431915503/10000000000 : ℝ)|=(5431915503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614788401/5000000000 : ℝ)|^8309 ≤ (10575861423261/25000000000000 : ℝ)^6261
        have hw : |(2614788401/5000000000 : ℝ)|=(2614788401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s3_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334651667/625000000 : ℝ)*x 0 + (-2278772491/10000000000 : ℝ)*x 1 + (5229576797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334651667/625000000 : ℝ)^8309 ≤ (43648952316787/100000000000000 : ℝ)^6261 := by
    have hnat : (334651667 : ℕ)^8309*100000000000000^6261 ≤ 43648952316787^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334651667 625000000 43648952316787 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278772491/10000000000 : ℝ)^8309 ≤ (2809520406061/20000000000000 : ℝ)^6261 := by
    have hnat : (2278772491 : ℕ)^8309*20000000000000^6261 ≤ 2809520406061^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278772491 10000000000 2809520406061 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229576797/10000000000 : ℝ)^8309 ≤ (5287930704921/12500000000000 : ℝ)^6261 := by
    have hnat : (5229576797 : ℕ)^8309*12500000000000^6261 ≤ 5287930704921^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229576797 10000000000 5287930704921 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334651667/625000000 : ℝ), (-2278772491/10000000000 : ℝ), (5229576797/10000000000 : ℝ)] ![(43648952316787/100000000000000 : ℝ), (2809520406061/20000000000000 : ℝ), (5287930704921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334651667/625000000 : ℝ)|^8309 ≤ (43648952316787/100000000000000 : ℝ)^6261
        have hw : |(334651667/625000000 : ℝ)|=(334651667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2278772491/10000000000 : ℝ)|^8309 ≤ (2809520406061/20000000000000 : ℝ)^6261
        have hw : |(-2278772491/10000000000 : ℝ)|=(2278772491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229576797/10000000000 : ℝ)|^8309 ≤ (5287930704921/12500000000000 : ℝ)^6261
        have hw : |(5229576797/10000000000 : ℝ)|=(5229576797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s3_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677213393/5000000000 : ℝ)*x 0 + (5229576899/10000000000 : ℝ)*x 1 + (-455754441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677213393/5000000000 : ℝ)^8309 ≤ (43648953550093/100000000000000 : ℝ)^6261 := by
    have hnat : (2677213393 : ℕ)^8309*100000000000000^6261 ≤ 43648953550093^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677213393 5000000000 43648953550093 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229576899/10000000000 : ℝ)^8309 ≤ (1321982710449/3125000000000 : ℝ)^6261 := by
    have hnat : (5229576899 : ℕ)^8309*3125000000000^6261 ≤ 1321982710449^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229576899 10000000000 1321982710449 3125000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455754441/2000000000 : ℝ)^8309 ≤ (14047599690539/100000000000000 : ℝ)^6261 := by
    have hnat : (455754441 : ℕ)^8309*100000000000000^6261 ≤ 14047599690539^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455754441 2000000000 14047599690539 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677213393/5000000000 : ℝ), (5229576899/10000000000 : ℝ), (-455754441/2000000000 : ℝ)] ![(43648953550093/100000000000000 : ℝ), (1321982710449/3125000000000 : ℝ), (14047599690539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677213393/5000000000 : ℝ)|^8309 ≤ (43648953550093/100000000000000 : ℝ)^6261
        have hw : |(2677213393/5000000000 : ℝ)|=(2677213393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229576899/10000000000 : ℝ)|^8309 ≤ (1321982710449/3125000000000 : ℝ)^6261
        have hw : |(5229576899/10000000000 : ℝ)|=(5229576899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-455754441/2000000000 : ℝ)|^8309 ≤ (14047599690539/100000000000000 : ℝ)^6261
        have hw : |(-455754441/2000000000 : ℝ)|=(455754441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s3_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873183727/2000000000 : ℝ)*x 0 + (2085131027/5000000000 : ℝ)*x 1 + (2285378547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873183727/2000000000 : ℝ)^8309 ≤ (3329222587427/10000000000000 : ℝ)^6261 := by
    have hnat : (873183727 : ℕ)^8309*10000000000000^6261 ≤ 3329222587427^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873183727 2000000000 3329222587427 10000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085131027/5000000000 : ℝ)^8309 ≤ (1957930006801/6250000000000 : ℝ)^6261 := by
    have hnat : (2085131027 : ℕ)^8309*6250000000000^6261 ≤ 1957930006801^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085131027 5000000000 1957930006801 6250000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285378547/5000000000 : ℝ)^8309 ≤ (141523575989/400000000000 : ℝ)^6261 := by
    have hnat : (2285378547 : ℕ)^8309*400000000000^6261 ≤ 141523575989^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285378547 5000000000 141523575989 400000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873183727/2000000000 : ℝ), (2085131027/5000000000 : ℝ), (2285378547/5000000000 : ℝ)] ![(3329222587427/10000000000000 : ℝ), (1957930006801/6250000000000 : ℝ), (141523575989/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873183727/2000000000 : ℝ)|^8309 ≤ (3329222587427/10000000000000 : ℝ)^6261
        have hw : |(873183727/2000000000 : ℝ)|=(873183727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085131027/5000000000 : ℝ)|^8309 ≤ (1957930006801/6250000000000 : ℝ)^6261
        have hw : |(2085131027/5000000000 : ℝ)|=(2085131027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2285378547/5000000000 : ℝ)|^8309 ≤ (141523575989/400000000000 : ℝ)^6261
        have hw : |(2285378547/5000000000 : ℝ)|=(2285378547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s3_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175302941/10000000000 : ℝ)*x 0 + (1307594143/2500000000 : ℝ)*x 1 + (2715555613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175302941/10000000000 : ℝ)^8309 ≤ (3301867325653/25000000000000 : ℝ)^6261 := by
    have hnat : (2175302941 : ℕ)^8309*25000000000000^6261 ≤ 3301867325653^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175302941 10000000000 3301867325653 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307594143/2500000000 : ℝ)^8309 ≤ (42312031679997/100000000000000 : ℝ)^6261 := by
    have hnat : (1307594143 : ℕ)^8309*100000000000000^6261 ≤ 42312031679997^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307594143 2500000000 42312031679997 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715555613/5000000000 : ℝ)^8309 ≤ (22240249502071/50000000000000 : ℝ)^6261 := by
    have hnat : (2715555613 : ℕ)^8309*50000000000000^6261 ≤ 22240249502071^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715555613 5000000000 22240249502071 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175302941/10000000000 : ℝ), (1307594143/2500000000 : ℝ), (2715555613/5000000000 : ℝ)] ![(3301867325653/25000000000000 : ℝ), (42312031679997/100000000000000 : ℝ), (22240249502071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175302941/10000000000 : ℝ)|^8309 ≤ (3301867325653/25000000000000 : ℝ)^6261
        have hw : |(-2175302941/10000000000 : ℝ)|=(2175302941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307594143/2500000000 : ℝ)|^8309 ≤ (42312031679997/100000000000000 : ℝ)^6261
        have hw : |(1307594143/2500000000 : ℝ)|=(1307594143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715555613/5000000000 : ℝ)|^8309 ≤ (22240249502071/50000000000000 : ℝ)^6261
        have hw : |(2715555613/5000000000 : ℝ)|=(2715555613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s3_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325815859/2500000000 : ℝ)*x 0 + (-2077237939/10000000000 : ℝ)*x 1 + (5431111371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325815859/2500000000 : ℝ)^8309 ≤ (5387038898453/12500000000000 : ℝ)^6261 := by
    have hnat : (1325815859 : ℕ)^8309*12500000000000^6261 ≤ 5387038898453^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325815859 2500000000 5387038898453 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077237939/10000000000 : ℝ)^8309 ≤ (3105797051961/25000000000000 : ℝ)^6261 := by
    have hnat : (2077237939 : ℕ)^8309*25000000000000^6261 ≤ 3105797051961^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077237939 10000000000 3105797051961 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431111371/10000000000 : ℝ)^8309 ≤ (22240250290067/50000000000000 : ℝ)^6261 := by
    have hnat : (5431111371 : ℕ)^8309*50000000000000^6261 ≤ 22240250290067^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431111371 10000000000 22240250290067 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325815859/2500000000 : ℝ), (-2077237939/10000000000 : ℝ), (5431111371/10000000000 : ℝ)] ![(5387038898453/12500000000000 : ℝ), (3105797051961/25000000000000 : ℝ), (22240250290067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325815859/2500000000 : ℝ)|^8309 ≤ (5387038898453/12500000000000 : ℝ)^6261
        have hw : |(1325815859/2500000000 : ℝ)|=(1325815859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077237939/10000000000 : ℝ)|^8309 ≤ (3105797051961/25000000000000 : ℝ)^6261
        have hw : |(-2077237939/10000000000 : ℝ)|=(2077237939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431111371/10000000000 : ℝ)|^8309 ≤ (22240250290067/50000000000000 : ℝ)^6261
        have hw : |(5431111371/10000000000 : ℝ)|=(5431111371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s3_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303263451/10000000000 : ℝ)*x 0 + (2715555621/5000000000 : ℝ)*x 1 + (-129827381/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303263451/10000000000 : ℝ)^8309 ≤ (2693519459337/6250000000000 : ℝ)^6261 := by
    have hnat : (5303263451 : ℕ)^8309*6250000000000^6261 ≤ 2693519459337^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303263451 10000000000 2693519459337 6250000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715555621/5000000000 : ℝ)^8309 ≤ (8896099835609/20000000000000 : ℝ)^6261 := by
    have hnat : (2715555621 : ℕ)^8309*20000000000000^6261 ≤ 8896099835609^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715555621 5000000000 8896099835609 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129827381/625000000 : ℝ)^8309 ≤ (621159472697/5000000000000 : ℝ)^6261 := by
    have hnat : (129827381 : ℕ)^8309*5000000000000^6261 ≤ 621159472697^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129827381 625000000 621159472697 5000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303263451/10000000000 : ℝ), (2715555621/5000000000 : ℝ), (-129827381/625000000 : ℝ)] ![(2693519459337/6250000000000 : ℝ), (8896099835609/20000000000000 : ℝ), (621159472697/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303263451/10000000000 : ℝ)|^8309 ≤ (2693519459337/6250000000000 : ℝ)^6261
        have hw : |(5303263451/10000000000 : ℝ)|=(5303263451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715555621/5000000000 : ℝ)|^8309 ≤ (8896099835609/20000000000000 : ℝ)^6261
        have hw : |(2715555621/5000000000 : ℝ)|=(2715555621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129827381/625000000 : ℝ)|^8309 ≤ (621159472697/5000000000000 : ℝ)^6261
        have hw : |(-129827381/625000000 : ℝ)|=(129827381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s3_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365956911/10000000000 : ℝ)*x 0 + (1142293677/2500000000 : ℝ)*x 1 + (2085926789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365956911/10000000000 : ℝ)^8309 ≤ (1040394163143/3125000000000 : ℝ)^6261 := by
    have hnat : (4365956911 : ℕ)^8309*3125000000000^6261 ≤ 1040394163143^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365956911 10000000000 1040394163143 3125000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142293677/2500000000 : ℝ)^8309 ≤ (8841159874877/25000000000000 : ℝ)^6261 := by
    have hnat : (1142293677 : ℕ)^8309*25000000000000^6261 ≤ 8841159874877^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142293677 2500000000 8841159874877 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085926789/5000000000 : ℝ)^8309 ≤ (15671373633481/50000000000000 : ℝ)^6261 := by
    have hnat : (2085926789 : ℕ)^8309*50000000000000^6261 ≤ 15671373633481^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085926789 5000000000 15671373633481 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365956911/10000000000 : ℝ), (1142293677/2500000000 : ℝ), (2085926789/5000000000 : ℝ)] ![(1040394163143/3125000000000 : ℝ), (8841159874877/25000000000000 : ℝ), (15671373633481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365956911/10000000000 : ℝ)|^8309 ≤ (1040394163143/3125000000000 : ℝ)^6261
        have hw : |(4365956911/10000000000 : ℝ)|=(4365956911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1142293677/2500000000 : ℝ)|^8309 ≤ (8841159874877/25000000000000 : ℝ)^6261
        have hw : |(1142293677/2500000000 : ℝ)|=(1142293677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085926789/5000000000 : ℝ)|^8309 ≤ (15671373633481/50000000000000 : ℝ)^6261
        have hw : |(2085926789/5000000000 : ℝ)|=(2085926789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2639/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7419/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16581/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16581/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16581/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16581/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16581/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16581/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8951/100000 : ℝ) ^ (2077/512 : ℝ) ≤ (1399779365244313/25000000000000000000 : ℝ) := by
    have hpowers : (8951/100000 : ℝ)^2077 ≤ (1399779365244313/25000000000000000000 : ℝ)^512 := by
      have hnat : (8951 : ℕ)^2077*25000000000000000000^512 ≤ 1399779365244313^512*100000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8951 100000 1399779365244313 25000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8951/100000 : ℝ)) (X := (1399779365244313/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16581/100000 : ℝ) ^ (2077/512 : ℝ) ≤ (17067941642300043/25000000000000000000 : ℝ) := by
    have hpowers : (16581/100000 : ℝ)^2077 ≤ (17067941642300043/25000000000000000000 : ℝ)^512 := by
      have hnat : (16581 : ℕ)^2077*25000000000000000000^512 ≤ 17067941642300043^512*100000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16581 100000 17067941642300043 25000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16581/100000 : ℝ)) (X := (17067941642300043/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501399779365244313/12500000000000000000 : ℝ) ≤ (10000276035358999/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (12501399779365244313/12500000000000000000 : ℝ)^512 ≤ (10000276035358999/10000000000000000 : ℝ)^2077 := by
      have hnat : (12501399779365244313 : ℕ)^512*10000000000000000^2077 ≤ 10000276035358999^2077*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501399779365244313 12500000000000000000 10000276035358999 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000276035358999/10000000000000000 : ℝ)) (X := (12501399779365244313/12500000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6254616930251886089/6250000000000000000 : ℝ) ≤ (10001820480074187/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (6254616930251886089/6250000000000000000 : ℝ)^512 ≤ (10001820480074187/10000000000000000 : ℝ)^2077 := by
      have hnat : (6254616930251886089 : ℕ)^512*10000000000000000^2077 ≤ 10001820480074187^2077*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254616930251886089 6250000000000000000 10001820480074187 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001820480074187/10000000000000000 : ℝ)) (X := (6254616930251886089/6250000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12517067941642300043/12500000000000000000 : ℝ) ≤ (16005383879663/16000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (12517067941642300043/12500000000000000000 : ℝ)^512 ≤ (16005383879663/16000000000000 : ℝ)^2077 := by
      have hnat : (12517067941642300043 : ℕ)^512*16000000000000^2077 ≤ 16005383879663^2077*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12517067941642300043 12500000000000000000 16005383879663 16000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16005383879663/16000000000000 : ℝ)) (X := (12517067941642300043/12500000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1399779365244313/25000000000000000000 : ℝ) ≤ ((38137228750248933397/38150000000000000000 : ℝ)+2*(386111178797/190750000000000 : ℝ)*(8951/100000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (38137228750248933397/38150000000000000000 : ℝ)+2*(386111178797/190750000000000 : ℝ)*(8951/100000 : ℝ)=(10000276035358999/10000000000000000 : ℝ) by norm_num, show 1+2*(1399779365244313/25000000000000000000 : ℝ)=(12501399779365244313/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17067941642300043/25000000000000000000 : ℝ)+(1399779365244313/25000000000000000000 : ℝ) ≤ ((38137228750248933397/38150000000000000000 : ℝ)+(386111178797/190750000000000 : ℝ)*((16581/100000 : ℝ)+(8951/100000 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (38137228750248933397/38150000000000000000 : ℝ)+(386111178797/190750000000000 : ℝ)*((16581/100000 : ℝ)+(8951/100000 : ℝ))=(10001820480074187/10000000000000000 : ℝ) by norm_num, show 1+(17067941642300043/25000000000000000000 : ℝ)+(1399779365244313/25000000000000000000 : ℝ)=(6254616930251886089/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17067941642300043/25000000000000000000 : ℝ) ≤ ((38137228750248933397/38150000000000000000 : ℝ)+2*(386111178797/190750000000000 : ℝ)*(16581/100000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (38137228750248933397/38150000000000000000 : ℝ)+2*(386111178797/190750000000000 : ℝ)*(16581/100000 : ℝ)=(16005383879663/16000000000000 : ℝ) by norm_num, show 1+2*(17067941642300043/25000000000000000000 : ℝ)=(12517067941642300043/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38137228750248933397/38150000000000000000 : ℝ)*(X 1 0+X 2 0)+(386111178797/190750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (8951/100000 : ℝ)) (hi := (16581/100000 : ℝ)) (c := (38137228750248933397/38150000000000000000 : ℝ)) (alpha := (386111178797/190750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38137228750248933397/38150000000000000000 : ℝ)*(X 0 1+X 2 1)+(386111178797/190750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (8951/100000 : ℝ)) (hi := (16581/100000 : ℝ)) (c := (38137228750248933397/38150000000000000000 : ℝ)) (alpha := (386111178797/190750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38137228750248933397/38150000000000000000 : ℝ)*(X 0 2+X 1 2)+(386111178797/190750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (8951/100000 : ℝ)) (hi := (16581/100000 : ℝ)) (c := (38137228750248933397/38150000000000000000 : ℝ)) (alpha := (386111178797/190750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-5438209/25000000 : ℝ)*X 0 0+(5431915503/10000000000 : ℝ)*X 0 1+(2614788401/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334651667/625000000 : ℝ)*X 1 0+(-2278772491/10000000000 : ℝ)*X 1 1+(5229576797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677213393/5000000000 : ℝ)*X 2 0+(5229576899/10000000000 : ℝ)*X 2 1+(-455754441/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873183727/2000000000 : ℝ)*X 0 0+(2085131027/5000000000 : ℝ)*X 0 1+(2285378547/5000000000 : ℝ)*X 0 2+(873183727/2000000000 : ℝ)*X 1 0+(2085131027/5000000000 : ℝ)*X 1 1+(2285378547/5000000000 : ℝ)*X 1 2+(873183727/2000000000 : ℝ)*X 2 0+(2085131027/5000000000 : ℝ)*X 2 1+(2285378547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2175302941/10000000000 : ℝ)*X 0 0+(1307594143/2500000000 : ℝ)*X 0 1+(2715555613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325815859/2500000000 : ℝ)*X 1 0+(-2077237939/10000000000 : ℝ)*X 1 1+(5431111371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303263451/10000000000 : ℝ)*X 2 0+(2715555621/5000000000 : ℝ)*X 2 1+(-129827381/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365956911/10000000000 : ℝ)*X 0 0+(1142293677/2500000000 : ℝ)*X 0 1+(2085926789/5000000000 : ℝ)*X 0 2+(4365956911/10000000000 : ℝ)*X 1 0+(1142293677/2500000000 : ℝ)*X 1 1+(2085926789/5000000000 : ℝ)*X 1 2+(4365956911/10000000000 : ℝ)*X 2 0+(1142293677/2500000000 : ℝ)*X 2 1+(2085926789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66297561790694090425605321/8515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2044289567/100000000000000 : ℝ)*(base19) + (1922487401/100000000000000 : ℝ)*(base23) + (121560109/100000000000000 : ℝ)*(lower2) + (117903157/100000000000000 : ℝ)*(upper3) + (51579221/20000000000000 : ℝ)*(upper5) + (29059493192723/781250000000 : ℝ)*(major0) + (29059493192723/781250000000 : ℝ)*(major1) + (29059493192723/781250000000 : ℝ)*(major2) + (2471121522114339/50000000000000 : ℝ)*(sp0) + (2471141708215801/50000000000000 : ℝ)*(sp1) + (617785442279221/12500000000000 : ℝ)*(sp2) + (1248463721301059/50000000000000 : ℝ)*(sp3) + (42416492491/100000000000000 : ℝ)*(sp4) + (8547250203/50000000000000 : ℝ)*(sp7) + (624236134275631/25000000000000 : ℝ)*(f.failure) + (4942285460721169/100000000000000 : ℝ)*(f.sum) + (12302275694177/2725000000000000000000000000 : ℝ)*base66 + (877856957775827/1064453125000000000000000000000 : ℝ)*base67 + (1284506944411673/1064453125000000000000000000000 : ℝ)*base70 + (7775546157412317/4257812500000000000000000000000 : ℝ)*base72 + (2923134556551/1362500000000000000000000000 : ℝ)*base74 + (6063909003474173/1064453125000000000000000000000 : ℝ)*base76 + (6482964139287317/4257812500000000000000000000000 : ℝ)*base78 + (27573137186025183/4257812500000000000000000000000 : ℝ)*base79 + (1263847485819/340625000000000000000000000 : ℝ)*base82 + (1221877/250000000000000000000 : ℝ)*base89 + (1221877/250000000000000000000 : ℝ)*base91 + (1221877/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9113778559243919450751267663/953750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35670363/2000000000000 : ℝ)*(base19) + (2070862337/100000000000000 : ℝ)*(base23) + (112564261/50000000000000 : ℝ)*(upper3) + (333377/250000000000 : ℝ)*(lower4) + (159761759/100000000000000 : ℝ)*(upper5) + (3749276358258993/100000000000000 : ℝ)*(major0) + (3749276358258993/100000000000000 : ℝ)*(major1) + (3749276358258993/100000000000000 : ℝ)*(major2) + (32846753993/100000000000000 : ℝ)*(sp1) + (35106677961/100000000000000 : ℝ)*(sp2) + (2490848270702847/50000000000000 : ℝ)*(sp4) + (4981661911133551/100000000000000 : ℝ)*(sp5) + (1245414840966349/25000000000000 : ℝ)*(sp6) + (629213964146979/25000000000000 : ℝ)*(sp7) + (629213964146979/25000000000000 : ℝ)*(f.failure) + (2490848270702847/50000000000000 : ℝ)*(f.sum) + (6272324705113/1192187500000000000000000000 : ℝ)*base66 + (11809895342822510779/3815000000000000000000000000000000 : ℝ)*base68 + (14631296889562510779/3815000000000000000000000000000000 : ℝ)*base70 + (47402702796102510779/3815000000000000000000000000000000 : ℝ)*base72 + (24853972052821/9537500000000000000000000000 : ℝ)*base73 + (16126349601932510779/3815000000000000000000000000000000 : ℝ)*base76 + (30127857890252510779/3815000000000000000000000000000000 : ℝ)*base78 + (1834819148732489221/3815000000000000000000000000000000 : ℝ)*base79 + (26518290027183/19075000000000000000000000000 : ℝ)*base82 + (2718993/250000000000000000000 : ℝ)*base89 + (2718993/250000000000000000000 : ℝ)*base91 + (2718993/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1116_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2639/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7419/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1116_s4_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089250673/5000000000 : ℝ)*x 0 + (2701586643/5000000000 : ℝ)*x 1 + (657026881/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089250673/5000000000 : ℝ)^8309 ≤ (13233246919441/100000000000000 : ℝ)^6261 := by
    have hnat : (1089250673 : ℕ)^8309*100000000000000^6261 ≤ 13233246919441^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089250673 5000000000 13233246919441 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701586643/5000000000 : ℝ)^8309 ≤ (8835419960819/20000000000000 : ℝ)^6261 := by
    have hnat : (2701586643 : ℕ)^8309*20000000000000^6261 ≤ 8835419960819^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701586643 5000000000 8835419960819 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657026881/1250000000 : ℝ)^8309 ≤ (42589653268271/100000000000000 : ℝ)^6261 := by
    have hnat : (657026881 : ℕ)^8309*100000000000000^6261 ≤ 42589653268271^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657026881 1250000000 42589653268271 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089250673/5000000000 : ℝ), (2701586643/5000000000 : ℝ), (657026881/1250000000 : ℝ)] ![(13233246919441/100000000000000 : ℝ), (8835419960819/20000000000000 : ℝ), (42589653268271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089250673/5000000000 : ℝ)|^8309 ≤ (13233246919441/100000000000000 : ℝ)^6261
        have hw : |(-1089250673/5000000000 : ℝ)|=(1089250673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701586643/5000000000 : ℝ)|^8309 ≤ (8835419960819/20000000000000 : ℝ)^6261
        have hw : |(2701586643/5000000000 : ℝ)|=(2701586643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657026881/1250000000 : ℝ)|^8309 ≤ (42589653268271/100000000000000 : ℝ)^6261
        have hw : |(657026881/1250000000 : ℝ)|=(657026881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s4_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668408673/1250000000 : ℝ)*x 0 + (-140825211/625000000 : ℝ)*x 1 + (5256215269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668408673/1250000000 : ℝ)^8309 ≤ (43571538333901/100000000000000 : ℝ)^6261 := by
    have hnat : (668408673 : ℕ)^8309*100000000000000^6261 ≤ 43571538333901^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668408673 1250000000 43571538333901 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140825211/625000000 : ℝ)^8309 ≤ (864925375133/6250000000000 : ℝ)^6261 := by
    have hnat : (140825211 : ℕ)^8309*6250000000000^6261 ≤ 864925375133^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140825211 625000000 864925375133 6250000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256215269/10000000000 : ℝ)^8309 ≤ (42589655644719/100000000000000 : ℝ)^6261 := by
    have hnat : (5256215269 : ℕ)^8309*100000000000000^6261 ≤ 42589655644719^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256215269 10000000000 42589655644719 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668408673/1250000000 : ℝ), (-140825211/625000000 : ℝ), (5256215269/10000000000 : ℝ)] ![(43571538333901/100000000000000 : ℝ), (864925375133/6250000000000 : ℝ), (42589655644719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668408673/1250000000 : ℝ)|^8309 ≤ (43571538333901/100000000000000 : ℝ)^6261
        have hw : |(668408673/1250000000 : ℝ)|=(668408673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140825211/625000000 : ℝ)|^8309 ≤ (864925375133/6250000000000 : ℝ)^6261
        have hw : |(-140825211/625000000 : ℝ)|=(140825211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256215269/10000000000 : ℝ)|^8309 ≤ (42589655644719/100000000000000 : ℝ)^6261
        have hw : |(5256215269/10000000000 : ℝ)|=(5256215269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s4_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336817197/2500000000 : ℝ)*x 0 + (5256214993/10000000000 : ℝ)*x 1 + (-2253204531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336817197/2500000000 : ℝ)^8309 ≤ (43571531888913/100000000000000 : ℝ)^6261 := by
    have hnat : (1336817197 : ℕ)^8309*100000000000000^6261 ≤ 43571531888913^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336817197 2500000000 43571531888913 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256214993/10000000000 : ℝ)^8309 ≤ (42589652676847/100000000000000 : ℝ)^6261 := by
    have hnat : (5256214993 : ℕ)^8309*100000000000000^6261 ≤ 42589652676847^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256214993 10000000000 42589652676847 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253204531/10000000000 : ℝ)^8309 ≤ (13838815416369/100000000000000 : ℝ)^6261 := by
    have hnat : (2253204531 : ℕ)^8309*100000000000000^6261 ≤ 13838815416369^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253204531 10000000000 13838815416369 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336817197/2500000000 : ℝ), (5256214993/10000000000 : ℝ), (-2253204531/10000000000 : ℝ)] ![(43571531888913/100000000000000 : ℝ), (42589652676847/100000000000000 : ℝ), (13838815416369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336817197/2500000000 : ℝ)|^8309 ≤ (43571531888913/100000000000000 : ℝ)^6261
        have hw : |(1336817197/2500000000 : ℝ)|=(1336817197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256214993/10000000000 : ℝ)|^8309 ≤ (42589652676847/100000000000000 : ℝ)^6261
        have hw : |(5256214993/10000000000 : ℝ)|=(5256214993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253204531/10000000000 : ℝ)|^8309 ≤ (13838815416369/100000000000000 : ℝ)^6261
        have hw : |(-2253204531/10000000000 : ℝ)|=(2253204531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s4_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873567317/2000000000 : ℝ)*x 0 + (4224819713/10000000000 : ℝ)*x 1 + (282231273/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873567317/2000000000 : ℝ)^8309 ≤ (33311636553389/100000000000000 : ℝ)^6261 := by
    have hnat : (873567317 : ℕ)^8309*100000000000000^6261 ≤ 33311636553389^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873567317 2000000000 33311636553389 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224819713/10000000000 : ℝ)^8309 ≤ (31871934863807/100000000000000 : ℝ)^6261 := by
    have hnat : (4224819713 : ℕ)^8309*100000000000000^6261 ≤ 31871934863807^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224819713 10000000000 31871934863807 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282231273/625000000 : ℝ)^8309 ≤ (1088013393037/3125000000000 : ℝ)^6261 := by
    have hnat : (282231273 : ℕ)^8309*3125000000000^6261 ≤ 1088013393037^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282231273 625000000 1088013393037 3125000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873567317/2000000000 : ℝ), (4224819713/10000000000 : ℝ), (282231273/625000000 : ℝ)] ![(33311636553389/100000000000000 : ℝ), (31871934863807/100000000000000 : ℝ), (1088013393037/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873567317/2000000000 : ℝ)|^8309 ≤ (33311636553389/100000000000000 : ℝ)^6261
        have hw : |(873567317/2000000000 : ℝ)|=(873567317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224819713/10000000000 : ℝ)|^8309 ≤ (31871934863807/100000000000000 : ℝ)^6261
        have hw : |(4224819713/10000000000 : ℝ)|=(4224819713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282231273/625000000 : ℝ)|^8309 ≤ (1088013393037/3125000000000 : ℝ)^6261
        have hw : |(282231273/625000000 : ℝ)|=(282231273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s4_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089254141/5000000000 : ℝ)*x 0 + (2628318859/5000000000 : ℝ)*x 1 + (5402749247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089254141/5000000000 : ℝ)^8309 ≤ (3308325708437/25000000000000 : ℝ)^6261 := by
    have hnat : (1089254141 : ℕ)^8309*25000000000000^6261 ≤ 3308325708437^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089254141 5000000000 3308325708437 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628318859/5000000000 : ℝ)^8309 ≤ (42594198365413/100000000000000 : ℝ)^6261 := by
    have hnat : (2628318859 : ℕ)^8309*100000000000000^6261 ≤ 42594198365413^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628318859 5000000000 42594198365413 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402749247/10000000000 : ℝ)^8309 ≤ (11043124697437/25000000000000 : ℝ)^6261 := by
    have hnat : (5402749247 : ℕ)^8309*25000000000000^6261 ≤ 11043124697437^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402749247 10000000000 11043124697437 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089254141/5000000000 : ℝ), (2628318859/5000000000 : ℝ), (5402749247/10000000000 : ℝ)] ![(3308325708437/25000000000000 : ℝ), (42594198365413/100000000000000 : ℝ), (11043124697437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089254141/5000000000 : ℝ)|^8309 ≤ (3308325708437/25000000000000 : ℝ)^6261
        have hw : |(-1089254141/5000000000 : ℝ)|=(1089254141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628318859/5000000000 : ℝ)|^8309 ≤ (42594198365413/100000000000000 : ℝ)^6261
        have hw : |(2628318859/5000000000 : ℝ)|=(2628318859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402749247/10000000000 : ℝ)|^8309 ≤ (11043124697437/25000000000000 : ℝ)^6261
        have hw : |(5402749247/10000000000 : ℝ)|=(5402749247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s4_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165940949/312500000 : ℝ)*x 0 + (-1053335247/5000000000 : ℝ)*x 1 + (5402749407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165940949/312500000 : ℝ)^8309 ≤ (43170167842951/100000000000000 : ℝ)^6261 := by
    have hnat : (165940949 : ℕ)^8309*100000000000000^6261 ≤ 43170167842951^6261*312500000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165940949 312500000 43170167842951 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053335247/5000000000 : ℝ)^8309 ≤ (3164332903033/25000000000000 : ℝ)^6261 := by
    have hnat : (1053335247 : ℕ)^8309*25000000000000^6261 ≤ 3164332903033^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053335247 5000000000 3164332903033 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402749407/10000000000 : ℝ)^8309 ≤ (44172500525797/100000000000000 : ℝ)^6261 := by
    have hnat : (5402749407 : ℕ)^8309*100000000000000^6261 ≤ 44172500525797^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402749407 10000000000 44172500525797 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165940949/312500000 : ℝ), (-1053335247/5000000000 : ℝ), (5402749407/10000000000 : ℝ)] ![(43170167842951/100000000000000 : ℝ), (3164332903033/25000000000000 : ℝ), (44172500525797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165940949/312500000 : ℝ)|^8309 ≤ (43170167842951/100000000000000 : ℝ)^6261
        have hw : |(165940949/312500000 : ℝ)|=(165940949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053335247/5000000000 : ℝ)|^8309 ≤ (3164332903033/25000000000000 : ℝ)^6261
        have hw : |(-1053335247/5000000000 : ℝ)|=(1053335247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402749407/10000000000 : ℝ)|^8309 ≤ (44172500525797/100000000000000 : ℝ)^6261
        have hw : |(5402749407/10000000000 : ℝ)|=(5402749407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s4_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062022111/2000000000 : ℝ)*x 0 + (270137473/500000000 : ℝ)*x 1 + (-210667017/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062022111/2000000000 : ℝ)^8309 ≤ (43170169860513/100000000000000 : ℝ)^6261 := by
    have hnat : (1062022111 : ℕ)^8309*100000000000000^6261 ≤ 43170169860513^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062022111 2000000000 43170169860513 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270137473/500000000 : ℝ)^8309 ≤ (690195329701/1562500000000 : ℝ)^6261 := by
    have hnat : (270137473 : ℕ)^8309*1562500000000^6261 ≤ 690195329701^6261*500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270137473 500000000 690195329701 1562500000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210667017/1000000000 : ℝ)^8309 ≤ (3164332257177/25000000000000 : ℝ)^6261 := by
    have hnat : (210667017 : ℕ)^8309*25000000000000^6261 ≤ 3164332257177^6261*1000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210667017 1000000000 3164332257177 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062022111/2000000000 : ℝ), (270137473/500000000 : ℝ), (-210667017/1000000000 : ℝ)] ![(43170169860513/100000000000000 : ℝ), (690195329701/1562500000000 : ℝ), (3164332257177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062022111/2000000000 : ℝ)|^8309 ≤ (43170169860513/100000000000000 : ℝ)^6261
        have hw : |(1062022111/2000000000 : ℝ)|=(1062022111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270137473/500000000 : ℝ)|^8309 ≤ (690195329701/1562500000000 : ℝ)^6261
        have hw : |(270137473/500000000 : ℝ)|=(270137473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210667017/1000000000 : ℝ)|^8309 ≤ (3164332257177/25000000000000 : ℝ)^6261
        have hw : |(-210667017/1000000000 : ℝ)|=(210667017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s4_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367852091/10000000000 : ℝ)*x 0 + (4514863233/10000000000 : ℝ)*x 1 + (84513191/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367852091/10000000000 : ℝ)^8309 ≤ (26024838667/78125000000 : ℝ)^6261 := by
    have hnat : (4367852091 : ℕ)^8309*78125000000^6261 ≤ 26024838667^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367852091 10000000000 26024838667 78125000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514863233/10000000000 : ℝ)^8309 ≤ (6961572640013/20000000000000 : ℝ)^6261 := by
    have hnat : (4514863233 : ℕ)^8309*20000000000000^6261 ≤ 6961572640013^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514863233 10000000000 6961572640013 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84513191/200000000 : ℝ)^8309 ≤ (15940171642193/50000000000000 : ℝ)^6261 := by
    have hnat : (84513191 : ℕ)^8309*50000000000000^6261 ≤ 15940171642193^6261*200000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84513191 200000000 15940171642193 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367852091/10000000000 : ℝ), (4514863233/10000000000 : ℝ), (84513191/200000000 : ℝ)] ![(26024838667/78125000000 : ℝ), (6961572640013/20000000000000 : ℝ), (15940171642193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367852091/10000000000 : ℝ)|^8309 ≤ (26024838667/78125000000 : ℝ)^6261
        have hw : |(4367852091/10000000000 : ℝ)|=(4367852091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514863233/10000000000 : ℝ)|^8309 ≤ (6961572640013/20000000000000 : ℝ)^6261
        have hw : |(4514863233/10000000000 : ℝ)|=(4514863233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84513191/200000000 : ℝ)|^8309 ≤ (15940171642193/50000000000000 : ℝ)^6261
        have hw : |(84513191/200000000 : ℝ)|=(84513191/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7419/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2639/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (89/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7419/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2639/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7419/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2639/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7419/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2639/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7419/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2639/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7419/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2639/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7419/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2639/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2639/25000 : ℝ) ^ (2077/512 : ℝ) ≤ (10931705438566181/100000000000000000000 : ℝ) := by
    have hpowers : (2639/25000 : ℝ)^2077 ≤ (10931705438566181/100000000000000000000 : ℝ)^512 := by
      have hnat : (2639 : ℕ)^2077*100000000000000000000^512 ≤ 10931705438566181^512*25000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2639 25000 10931705438566181 100000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2639/25000 : ℝ)) (X := (10931705438566181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7419/50000 : ℝ) ^ (2077/512 : ℝ) ≤ (21753926367239081/50000000000000000000 : ℝ) := by
    have hpowers : (7419/50000 : ℝ)^2077 ≤ (21753926367239081/50000000000000000000 : ℝ)^512 := by
      have hnat : (7419 : ℕ)^2077*50000000000000000000^512 ≤ 21753926367239081^512*50000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7419 50000 21753926367239081 50000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7419/50000 : ℝ)) (X := (21753926367239081/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010931705438566181/50000000000000000000 : ℝ) ≤ (2500134727304269/2500000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50010931705438566181/50000000000000000000 : ℝ)^512 ≤ (2500134727304269/2500000000000000 : ℝ)^2077 := by
      have hnat : (50010931705438566181 : ℕ)^512*2500000000000000^2077 ≤ 2500134727304269^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010931705438566181 50000000000000000000 2500134727304269 2500000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134727304269/2500000000000000 : ℝ)) (X := (50010931705438566181/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054439558173044343/100000000000000000000 : ℝ) ≤ (10001341711067983/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (100054439558173044343/100000000000000000000 : ℝ)^512 ≤ (10001341711067983/10000000000000000 : ℝ)^2077 := by
      have hnat : (100054439558173044343 : ℕ)^512*10000000000000000^2077 ≤ 10001341711067983^2077*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054439558173044343 100000000000000000000 10001341711067983 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001341711067983/10000000000000000 : ℝ)) (X := (100054439558173044343/100000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021753926367239081/25000000000000000000 : ℝ) ≤ (1000214451291889/1000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (25021753926367239081/25000000000000000000 : ℝ)^512 ≤ (1000214451291889/1000000000000000 : ℝ)^2077 := by
      have hnat : (25021753926367239081 : ℕ)^512*1000000000000000^2077 ≤ 1000214451291889^2077*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021753926367239081 25000000000000000000 1000214451291889 1000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000214451291889/1000000000000000 : ℝ)) (X := (25021753926367239081/25000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10931705438566181/100000000000000000000 : ℝ) ≤ ((1337667464268474089/1338125000000000000 : ℝ)+2*(802801850907/428200000000000 : ℝ)*(2639/25000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (1337667464268474089/1338125000000000000 : ℝ)+2*(802801850907/428200000000000 : ℝ)*(2639/25000 : ℝ)=(2500134727304269/2500000000000000 : ℝ) by norm_num, show 1+2*(10931705438566181/100000000000000000000 : ℝ)=(50010931705438566181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21753926367239081/50000000000000000000 : ℝ)+(10931705438566181/100000000000000000000 : ℝ) ≤ ((1337667464268474089/1338125000000000000 : ℝ)+(802801850907/428200000000000 : ℝ)*((7419/50000 : ℝ)+(2639/25000 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (1337667464268474089/1338125000000000000 : ℝ)+(802801850907/428200000000000 : ℝ)*((7419/50000 : ℝ)+(2639/25000 : ℝ))=(10001341711067983/10000000000000000 : ℝ) by norm_num, show 1+(21753926367239081/50000000000000000000 : ℝ)+(10931705438566181/100000000000000000000 : ℝ)=(100054439558173044343/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21753926367239081/50000000000000000000 : ℝ) ≤ ((1337667464268474089/1338125000000000000 : ℝ)+2*(802801850907/428200000000000 : ℝ)*(7419/50000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (1337667464268474089/1338125000000000000 : ℝ)+2*(802801850907/428200000000000 : ℝ)*(7419/50000 : ℝ)=(1000214451291889/1000000000000000 : ℝ) by norm_num, show 1+2*(21753926367239081/50000000000000000000 : ℝ)=(25021753926367239081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1337667464268474089/1338125000000000000 : ℝ)*(X 1 0+X 2 0)+(802801850907/428200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (2639/25000 : ℝ)) (hi := (7419/50000 : ℝ)) (c := (1337667464268474089/1338125000000000000 : ℝ)) (alpha := (802801850907/428200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1337667464268474089/1338125000000000000 : ℝ)*(X 0 1+X 2 1)+(802801850907/428200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (2639/25000 : ℝ)) (hi := (7419/50000 : ℝ)) (c := (1337667464268474089/1338125000000000000 : ℝ)) (alpha := (802801850907/428200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1337667464268474089/1338125000000000000 : ℝ)*(X 0 2+X 1 2)+(802801850907/428200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (2639/25000 : ℝ)) (hi := (7419/50000 : ℝ)) (c := (1337667464268474089/1338125000000000000 : ℝ)) (alpha := (802801850907/428200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1089250673/5000000000 : ℝ)*X 0 0+(2701586643/5000000000 : ℝ)*X 0 1+(657026881/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668408673/1250000000 : ℝ)*X 1 0+(-140825211/625000000 : ℝ)*X 1 1+(5256215269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336817197/2500000000 : ℝ)*X 2 0+(5256214993/10000000000 : ℝ)*X 2 1+(-2253204531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873567317/2000000000 : ℝ)*X 0 0+(4224819713/10000000000 : ℝ)*X 0 1+(282231273/625000000 : ℝ)*X 0 2+(873567317/2000000000 : ℝ)*X 1 0+(4224819713/10000000000 : ℝ)*X 1 1+(282231273/625000000 : ℝ)*X 1 2+(873567317/2000000000 : ℝ)*X 2 0+(4224819713/10000000000 : ℝ)*X 2 1+(282231273/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089254141/5000000000 : ℝ)*X 0 0+(2628318859/5000000000 : ℝ)*X 0 1+(5402749247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165940949/312500000 : ℝ)*X 1 0+(-1053335247/5000000000 : ℝ)*X 1 1+(5402749407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062022111/2000000000 : ℝ)*X 2 0+(270137473/500000000 : ℝ)*X 2 1+(-210667017/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367852091/10000000000 : ℝ)*X 0 0+(4514863233/10000000000 : ℝ)*X 0 1+(84513191/200000000 : ℝ)*X 0 2+(4367852091/10000000000 : ℝ)*X 1 0+(4514863233/10000000000 : ℝ)*X 1 1+(84513191/200000000 : ℝ)*X 1 2+(4367852091/10000000000 : ℝ)*X 2 0+(4514863233/10000000000 : ℝ)*X 2 1+(84513191/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3256837596351391463088063/16726562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (234704053/10000000000000 : ℝ)*(base19) + (2256765703/100000000000000 : ℝ)*(base23) + (446432061/100000000000000 : ℝ)*(upper2) + (469851711/100000000000000 : ℝ)*(upper3) + (2560682222314951/50000000000000 : ℝ)*(major0) + (2560682222314951/50000000000000 : ℝ)*(major1) + (2560682222314951/50000000000000 : ℝ)*(major2) + (6804748323405691/100000000000000 : ℝ)*(sp0) + (6804800156203949/100000000000000 : ℝ)*(sp1) + (1360955251524637/20000000000000 : ℝ)*(sp2) + (1718940410424053/50000000000000 : ℝ)*(sp3) + (54179838787/100000000000000 : ℝ)*(sp4) + (23988855591/100000000000000 : ℝ)*(sp6) + (2277933843/5000000000000 : ℝ)*(sp7) + (687585275904993/20000000000000 : ℝ)*(f.failure) + (3402401251622239/50000000000000 : ℝ)*(f.sum) + (27263255844307/10705000000000000000000000000 : ℝ)*base65 + (286832293128816809/16726562500000000000000000000000 : ℝ)*base68 + (464508943367242993/33453125000000000000000000000000 : ℝ)*base70 + (107786635832535559/16726562500000000000000000000000 : ℝ)*base72 + (31730841773913/10705000000000000000000000000 : ℝ)*base74 + (435177769384180493/33453125000000000000000000000000 : ℝ)*base76 + (88716190493649243/33453125000000000000000000000000 : ℝ)*base78 + (399022710212211743/33453125000000000000000000000000 : ℝ)*base80 + (14319480626529/5352500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (358331/200000000000000000000 : ℝ)*base89 + (358331/200000000000000000000 : ℝ)*base91 + (358331/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (270047528528221193776692501/33453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1141688753/100000000000000 : ℝ)*(base19) + (2009014831/100000000000000 : ℝ)*(base23) + (189443657/50000000000000 : ℝ)*(upper3) + (111359907/50000000000000 : ℝ)*(lower4) + (159799937/50000000000000 : ℝ)*(upper5) + (643865916268693/12500000000000 : ℝ)*(major0) + (643865916268693/12500000000000 : ℝ)*(major1) + (643865916268693/12500000000000 : ℝ)*(major2) + (4358727307/25000000000000 : ℝ)*(sp1) + (9399908997/20000000000000 : ℝ)*(sp2) + (684408270970783/10000000000000 : ℝ)*(sp4) + (6844064133109849/100000000000000 : ℝ)*(sp5) + (3422016850574007/50000000000000 : ℝ)*(sp6) + (3457771681510733/100000000000000 : ℝ)*(sp7) + (3457771681510733/100000000000000 : ℝ)*(f.failure) + (684408270970783/10000000000000 : ℝ)*(f.sum) + (33555694614889/10705000000000000000000000000 : ℝ)*base65 + (262070671296531979/33453125000000000000000000000000 : ℝ)*base67 + (3150080877155319/2090820312500000000000000000000 : ℝ)*base69 + (18700435282811771/33453125000000000000000000000000 : ℝ)*base72 + (7150891356429/10705000000000000000000000000 : ℝ)*base73 + (201920269988156979/33453125000000000000000000000000 : ℝ)*base75 + (162208519551655521/33453125000000000000000000000000 : ℝ)*base78 + (224443141153695677/16726562500000000000000000000000 : ℝ)*base79 + (15926413249971/10705000000000000000000000000 : ℝ)*base82 + (6426911/1000000000000000000000 : ℝ)*base89 + (6426911/1000000000000000000000 : ℝ)*base91 + (6426911/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1116_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7419/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2639/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1116_s5_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-136199859/625000000 : ℝ)*x 0 + (2697803313/5000000000 : ℝ)*x 1 + (131583121/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136199859/625000000 : ℝ)^8309 ≤ (13238861196717/100000000000000 : ℝ)^6261 := by
    have hnat : (136199859 : ℕ)^8309*100000000000000^6261 ≤ 13238861196717^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136199859 625000000 13238861196717 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697803313/5000000000 : ℝ)^8309 ≤ (22047507944097/50000000000000 : ℝ)^6261 := by
    have hnat : (2697803313 : ℕ)^8309*50000000000000^6261 ≤ 22047507944097^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697803313 5000000000 22047507944097 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131583121/250000000 : ℝ)^8309 ≤ (2133306144731/5000000000000 : ℝ)^6261 := by
    have hnat : (131583121 : ℕ)^8309*5000000000000^6261 ≤ 2133306144731^6261*250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131583121 250000000 2133306144731 5000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136199859/625000000 : ℝ), (2697803313/5000000000 : ℝ), (131583121/250000000 : ℝ)] ![(13238861196717/100000000000000 : ℝ), (22047507944097/50000000000000 : ℝ), (2133306144731/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136199859/625000000 : ℝ)|^8309 ≤ (13238861196717/100000000000000 : ℝ)^6261
        have hw : |(-136199859/625000000 : ℝ)|=(136199859/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697803313/5000000000 : ℝ)|^8309 ≤ (22047507944097/50000000000000 : ℝ)^6261
        have hw : |(2697803313/5000000000 : ℝ)|=(2697803313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131583121/250000000 : ℝ)|^8309 ≤ (2133306144731/5000000000000 : ℝ)^6261
        have hw : |(131583121/250000000 : ℝ)|=(131583121/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s5_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83521493/156250000 : ℝ)*x 0 + (-1123165517/5000000000 : ℝ)*x 1 + (5263324699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83521493/156250000 : ℝ)^8309 ≤ (2177553005761/5000000000000 : ℝ)^6261 := by
    have hnat : (83521493 : ℕ)^8309*5000000000000^6261 ≤ 2177553005761^6261*156250000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83521493 156250000 2177553005761 5000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123165517/5000000000 : ℝ)^8309 ≤ (13782818485891/100000000000000 : ℝ)^6261 := by
    have hnat : (1123165517 : ℕ)^8309*100000000000000^6261 ≤ 13782818485891^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123165517 5000000000 13782818485891 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263324699/10000000000 : ℝ)^8309 ≤ (21333060688877/50000000000000 : ℝ)^6261 := by
    have hnat : (5263324699 : ℕ)^8309*50000000000000^6261 ≤ 21333060688877^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263324699 10000000000 21333060688877 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83521493/156250000 : ℝ), (-1123165517/5000000000 : ℝ), (5263324699/10000000000 : ℝ)] ![(2177553005761/5000000000000 : ℝ), (13782818485891/100000000000000 : ℝ), (21333060688877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83521493/156250000 : ℝ)|^8309 ≤ (2177553005761/5000000000000 : ℝ)^6261
        have hw : |(83521493/156250000 : ℝ)|=(83521493/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123165517/5000000000 : ℝ)|^8309 ≤ (13782818485891/100000000000000 : ℝ)^6261
        have hw : |(-1123165517/5000000000 : ℝ)|=(1123165517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263324699/10000000000 : ℝ)|^8309 ≤ (21333060688877/50000000000000 : ℝ)^6261
        have hw : |(5263324699/10000000000 : ℝ)|=(5263324699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s5_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345375633/10000000000 : ℝ)*x 0 + (5263324897/10000000000 : ℝ)*x 1 + (-2246330667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345375633/10000000000 : ℝ)^8309 ≤ (43551060991031/100000000000000 : ℝ)^6261 := by
    have hnat : (5345375633 : ℕ)^8309*100000000000000^6261 ≤ 43551060991031^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345375633 10000000000 43551060991031 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263324897/10000000000 : ℝ)^8309 ≤ (42666123507821/100000000000000 : ℝ)^6261 := by
    have hnat : (5263324897 : ℕ)^8309*100000000000000^6261 ≤ 42666123507821^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263324897 10000000000 42666123507821 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246330667/10000000000 : ℝ)^8309 ≤ (6891407748757/50000000000000 : ℝ)^6261 := by
    have hnat : (2246330667 : ℕ)^8309*50000000000000^6261 ≤ 6891407748757^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246330667 10000000000 6891407748757 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345375633/10000000000 : ℝ), (5263324897/10000000000 : ℝ), (-2246330667/10000000000 : ℝ)] ![(43551060991031/100000000000000 : ℝ), (42666123507821/100000000000000 : ℝ), (6891407748757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345375633/10000000000 : ℝ)|^8309 ≤ (43551060991031/100000000000000 : ℝ)^6261
        have hw : |(5345375633/10000000000 : ℝ)|=(5345375633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263324897/10000000000 : ℝ)|^8309 ≤ (42666123507821/100000000000000 : ℝ)^6261
        have hw : |(5263324897/10000000000 : ℝ)|=(5263324897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2246330667/10000000000 : ℝ)|^8309 ≤ (6891407748757/50000000000000 : ℝ)^6261
        have hw : |(-2246330667/10000000000 : ℝ)|=(2246330667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s5_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368243007/10000000000 : ℝ)*x 0 + (847858493/2000000000 : ℝ)*x 1 + (1125280441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368243007/10000000000 : ℝ)^8309 ≤ (6663150023861/20000000000000 : ℝ)^6261 := by
    have hnat : (4368243007 : ℕ)^8309*20000000000000^6261 ≤ 6663150023861^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368243007 10000000000 6663150023861 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847858493/2000000000 : ℝ)^8309 ≤ (8004227997957/25000000000000 : ℝ)^6261 := by
    have hnat : (847858493 : ℕ)^8309*25000000000000^6261 ≤ 8004227997957^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847858493 2000000000 8004227997957 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125280441/2500000000 : ℝ)^8309 ≤ (34667337876579/100000000000000 : ℝ)^6261 := by
    have hnat : (1125280441 : ℕ)^8309*100000000000000^6261 ≤ 34667337876579^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125280441 2500000000 34667337876579 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368243007/10000000000 : ℝ), (847858493/2000000000 : ℝ), (1125280441/2500000000 : ℝ)] ![(6663150023861/20000000000000 : ℝ), (8004227997957/25000000000000 : ℝ), (34667337876579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368243007/10000000000 : ℝ)|^8309 ≤ (6663150023861/20000000000000 : ℝ)^6261
        have hw : |(4368243007/10000000000 : ℝ)|=(4368243007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847858493/2000000000 : ℝ)|^8309 ≤ (8004227997957/25000000000000 : ℝ)^6261
        have hw : |(847858493/2000000000 : ℝ)|=(847858493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125280441/2500000000 : ℝ)|^8309 ≤ (34667337876579/100000000000000 : ℝ)^6261
        have hw : |(1125280441/2500000000 : ℝ)|=(1125280441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s5_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179202833/10000000000 : ℝ)*x 0 + (5263667501/10000000000 : ℝ)*x 1 + (2697631473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179202833/10000000000 : ℝ)^8309 ≤ (6619451112893/50000000000000 : ℝ)^6261 := by
    have hnat : (2179202833 : ℕ)^8309*50000000000000^6261 ≤ 6619451112893^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179202833 10000000000 6619451112893 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263667501/10000000000 : ℝ)^8309 ≤ (2666863078211/6250000000000 : ℝ)^6261 := by
    have hnat : (5263667501 : ℕ)^8309*6250000000000^6261 ≤ 2666863078211^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263667501 10000000000 2666863078211 6250000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697631473/5000000000 : ℝ)^8309 ≤ (22045644252621/50000000000000 : ℝ)^6261 := by
    have hnat : (2697631473 : ℕ)^8309*50000000000000^6261 ≤ 22045644252621^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697631473 5000000000 22045644252621 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179202833/10000000000 : ℝ), (5263667501/10000000000 : ℝ), (2697631473/5000000000 : ℝ)] ![(6619451112893/50000000000000 : ℝ), (2666863078211/6250000000000 : ℝ), (22045644252621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179202833/10000000000 : ℝ)|^8309 ≤ (6619451112893/50000000000000 : ℝ)^6261
        have hw : |(-2179202833/10000000000 : ℝ)|=(2179202833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263667501/10000000000 : ℝ)|^8309 ≤ (2666863078211/6250000000000 : ℝ)^6261
        have hw : |(5263667501/10000000000 : ℝ)|=(5263667501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697631473/5000000000 : ℝ)|^8309 ≤ (22045644252621/50000000000000 : ℝ)^6261
        have hw : |(2697631473/5000000000 : ℝ)|=(2697631473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s5_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311927229/10000000000 : ℝ)*x 0 + (-1057196269/5000000000 : ℝ)*x 1 + (337203933/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311927229/10000000000 : ℝ)^8309 ≤ (43189771235999/100000000000000 : ℝ)^6261 := by
    have hnat : (5311927229 : ℕ)^8309*100000000000000^6261 ≤ 43189771235999^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311927229 10000000000 43189771235999 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057196269/5000000000 : ℝ)^8309 ≤ (2543788087893/20000000000000 : ℝ)^6261 := by
    have hnat : (1057196269 : ℕ)^8309*20000000000000^6261 ≤ 2543788087893^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057196269 5000000000 2543788087893 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337203933/625000000 : ℝ)^8309 ≤ (1763651532401/4000000000000 : ℝ)^6261 := by
    have hnat : (337203933 : ℕ)^8309*4000000000000^6261 ≤ 1763651532401^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337203933 625000000 1763651532401 4000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311927229/10000000000 : ℝ), (-1057196269/5000000000 : ℝ), (337203933/625000000 : ℝ)] ![(43189771235999/100000000000000 : ℝ), (2543788087893/20000000000000 : ℝ), (1763651532401/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311927229/10000000000 : ℝ)|^8309 ≤ (43189771235999/100000000000000 : ℝ)^6261
        have hw : |(5311927229/10000000000 : ℝ)|=(5311927229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057196269/5000000000 : ℝ)|^8309 ≤ (2543788087893/20000000000000 : ℝ)^6261
        have hw : |(-1057196269/5000000000 : ℝ)|=(1057196269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337203933/625000000 : ℝ)|^8309 ≤ (1763651532401/4000000000000 : ℝ)^6261
        have hw : |(337203933/625000000 : ℝ)|=(337203933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s5_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655963607/5000000000 : ℝ)*x 0 + (5395262941/10000000000 : ℝ)*x 1 + (-2114392541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655963607/5000000000 : ℝ)^8309 ≤ (8637954214829/20000000000000 : ℝ)^6261 := by
    have hnat : (2655963607 : ℕ)^8309*20000000000000^6261 ≤ 8637954214829^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655963607 5000000000 8637954214829 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395262941/10000000000 : ℝ)^8309 ≤ (8818257690203/20000000000000 : ℝ)^6261 := by
    have hnat : (5395262941 : ℕ)^8309*20000000000000^6261 ≤ 8818257690203^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395262941 10000000000 8818257690203 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114392541/10000000000 : ℝ)^8309 ≤ (6359470231707/50000000000000 : ℝ)^6261 := by
    have hnat : (2114392541 : ℕ)^8309*50000000000000^6261 ≤ 6359470231707^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114392541 10000000000 6359470231707 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655963607/5000000000 : ℝ), (5395262941/10000000000 : ℝ), (-2114392541/10000000000 : ℝ)] ![(8637954214829/20000000000000 : ℝ), (8818257690203/20000000000000 : ℝ), (6359470231707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655963607/5000000000 : ℝ)|^8309 ≤ (8637954214829/20000000000000 : ℝ)^6261
        have hw : |(2655963607/5000000000 : ℝ)|=(2655963607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395262941/10000000000 : ℝ)|^8309 ≤ (8818257690203/20000000000000 : ℝ)^6261
        have hw : |(5395262941/10000000000 : ℝ)|=(5395262941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2114392541/10000000000 : ℝ)|^8309 ≤ (6359470231707/50000000000000 : ℝ)^6261
        have hw : |(-2114392541/10000000000 : ℝ)|=(2114392541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s5_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184126931/5000000000 : ℝ)*x 0 + (4500443961/10000000000 : ℝ)*x 1 + (423997269/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184126931/5000000000 : ℝ)^8309 ≤ (16657929994493/50000000000000 : ℝ)^6261 := by
    have hnat : (2184126931 : ℕ)^8309*50000000000000^6261 ≤ 16657929994493^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184126931 5000000000 16657929994493 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500443961/10000000000 : ℝ)^8309 ≤ (17330205020459/50000000000000 : ℝ)^6261 := by
    have hnat : (4500443961 : ℕ)^8309*50000000000000^6261 ≤ 17330205020459^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500443961 10000000000 17330205020459 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423997269/1000000000 : ℝ)^8309 ≤ (16011864981057/50000000000000 : ℝ)^6261 := by
    have hnat : (423997269 : ℕ)^8309*50000000000000^6261 ≤ 16011864981057^6261*1000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423997269 1000000000 16011864981057 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184126931/5000000000 : ℝ), (4500443961/10000000000 : ℝ), (423997269/1000000000 : ℝ)] ![(16657929994493/50000000000000 : ℝ), (17330205020459/50000000000000 : ℝ), (16011864981057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184126931/5000000000 : ℝ)|^8309 ≤ (16657929994493/50000000000000 : ℝ)^6261
        have hw : |(2184126931/5000000000 : ℝ)|=(2184126931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500443961/10000000000 : ℝ)|^8309 ≤ (17330205020459/50000000000000 : ℝ)^6261
        have hw : |(4500443961/10000000000 : ℝ)|=(4500443961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423997269/1000000000 : ℝ)|^8309 ≤ (16011864981057/50000000000000 : ℝ)^6261
        have hw : |(423997269/1000000000 : ℝ)|=(423997269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    (2819/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7039/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (89/800 : ℝ) ^ (2077/512 : ℝ) ≤ (13526390329691487/100000000000000000000 : ℝ) := by
    have hpowers : (89/800 : ℝ)^2077 ≤ (13526390329691487/100000000000000000000 : ℝ)^512 := by
      have hnat : (89 : ℕ)^2077*100000000000000000000^512 ≤ 13526390329691487^512*800^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 800 13526390329691487 100000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/800 : ℝ)) (X := (13526390329691487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (2077/512 : ℝ) ≤ (36789427875728827/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^2077 ≤ (36789427875728827/100000000000000000000 : ℝ)^512 := by
      have hnat : (14237 : ℕ)^2077*100000000000000000000^512 ≤ 36789427875728827^512*100000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 36789427875728827 100000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (36789427875728827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013526390329691487/50000000000000000000 : ℝ) ≤ (10000666808484513/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50013526390329691487/50000000000000000000 : ℝ)^512 ≤ (10000666808484513/10000000000000000 : ℝ)^2077 := by
      have hnat : (50013526390329691487 : ℕ)^512*10000000000000000^2077 ≤ 10000666808484513^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013526390329691487 50000000000000000000 10000666808484513 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000666808484513/10000000000000000 : ℝ)) (X := (50013526390329691487/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025157909102710157/50000000000000000000 : ℝ) ≤ (10001240097106657/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50025157909102710157/50000000000000000000 : ℝ)^512 ≤ (10001240097106657/10000000000000000 : ℝ)^2077 := by
      have hnat : (50025157909102710157 : ℕ)^512*10000000000000000^2077 ≤ 10001240097106657^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025157909102710157 50000000000000000000 10001240097106657 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001240097106657/10000000000000000 : ℝ)) (X := (50025157909102710157/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036789427875728827/50000000000000000000 : ℝ) ≤ (10001813385728801/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50036789427875728827/50000000000000000000 : ℝ)^512 ≤ (10001813385728801/10000000000000000 : ℝ)^2077 := by
      have hnat : (50036789427875728827 : ℕ)^512*10000000000000000^2077 ≤ 10001813385728801^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036789427875728827 50000000000000000000 10001813385728801 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001813385728801/10000000000000000 : ℝ)) (X := (50036789427875728827/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13526390329691487/100000000000000000000 : ℝ) ≤ ((3888664929520137557/3890000000000000000 : ℝ)+2*(8957634721/4862500000000 : ℝ)*(89/800 : ℝ))^(2077/512 : ℝ) := by
    rw [show (3888664929520137557/3890000000000000000 : ℝ)+2*(8957634721/4862500000000 : ℝ)*(89/800 : ℝ)=(10000666808484513/10000000000000000 : ℝ) by norm_num, show 1+2*(13526390329691487/100000000000000000000 : ℝ)=(50013526390329691487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36789427875728827/100000000000000000000 : ℝ)+(13526390329691487/100000000000000000000 : ℝ) ≤ ((3888664929520137557/3890000000000000000 : ℝ)+(8957634721/4862500000000 : ℝ)*((14237/100000 : ℝ)+(89/800 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (3888664929520137557/3890000000000000000 : ℝ)+(8957634721/4862500000000 : ℝ)*((14237/100000 : ℝ)+(89/800 : ℝ))=(10001240097106657/10000000000000000 : ℝ) by norm_num, show 1+(36789427875728827/100000000000000000000 : ℝ)+(13526390329691487/100000000000000000000 : ℝ)=(50025157909102710157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36789427875728827/100000000000000000000 : ℝ) ≤ ((3888664929520137557/3890000000000000000 : ℝ)+2*(8957634721/4862500000000 : ℝ)*(14237/100000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (3888664929520137557/3890000000000000000 : ℝ)+2*(8957634721/4862500000000 : ℝ)*(14237/100000 : ℝ)=(10001813385728801/10000000000000000 : ℝ) by norm_num, show 1+2*(36789427875728827/100000000000000000000 : ℝ)=(50036789427875728827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3888664929520137557/3890000000000000000 : ℝ)*(X 1 0+X 2 0)+(8957634721/4862500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3888664929520137557/3890000000000000000 : ℝ)) (alpha := (8957634721/4862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3888664929520137557/3890000000000000000 : ℝ)*(X 0 1+X 2 1)+(8957634721/4862500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3888664929520137557/3890000000000000000 : ℝ)) (alpha := (8957634721/4862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3888664929520137557/3890000000000000000 : ℝ)*(X 0 2+X 1 2)+(8957634721/4862500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3888664929520137557/3890000000000000000 : ℝ)) (alpha := (8957634721/4862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-136199859/625000000 : ℝ)*X 0 0+(2697803313/5000000000 : ℝ)*X 0 1+(131583121/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83521493/156250000 : ℝ)*X 1 0+(-1123165517/5000000000 : ℝ)*X 1 1+(5263324699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345375633/10000000000 : ℝ)*X 2 0+(5263324897/10000000000 : ℝ)*X 2 1+(-2246330667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368243007/10000000000 : ℝ)*X 0 0+(847858493/2000000000 : ℝ)*X 0 1+(1125280441/2500000000 : ℝ)*X 0 2+(4368243007/10000000000 : ℝ)*X 1 0+(847858493/2000000000 : ℝ)*X 1 1+(1125280441/2500000000 : ℝ)*X 1 2+(4368243007/10000000000 : ℝ)*X 2 0+(847858493/2000000000 : ℝ)*X 2 1+(1125280441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2179202833/10000000000 : ℝ)*X 0 0+(5263667501/10000000000 : ℝ)*X 0 1+(2697631473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311927229/10000000000 : ℝ)*X 1 0+(-1057196269/5000000000 : ℝ)*X 1 1+(337203933/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655963607/5000000000 : ℝ)*X 2 0+(5395262941/10000000000 : ℝ)*X 2 1+(-2114392541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184126931/5000000000 : ℝ)*X 0 0+(4500443961/10000000000 : ℝ)*X 0 1+(423997269/1000000000 : ℝ)*X 0 2+(2184126931/5000000000 : ℝ)*X 1 0+(4500443961/10000000000 : ℝ)*X 1 1+(423997269/1000000000 : ℝ)*X 1 2+(2184126931/5000000000 : ℝ)*X 2 0+(4500443961/10000000000 : ℝ)*X 2 1+(423997269/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1008322448501299652932053069/97250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (550832113/25000000000000 : ℝ)*(base19) + (477480087/25000000000000 : ℝ)*(base23) + (41501337/25000000000000 : ℝ)*(upper3) + (109035663/50000000000000 : ℝ)*(upper4) + (57666869/12500000000000 : ℝ)*(upper5) + (2844759732444061/50000000000000 : ℝ)*(major0) + (2844759732444061/50000000000000 : ℝ)*(major1) + (2844759732444061/50000000000000 : ℝ)*(major2) + (302386254204713/4000000000000 : ℝ)*(sp0) + (7559712591905121/100000000000000 : ℝ)*(sp1) + (302388515412529/4000000000000 : ℝ)*(sp2) + (76386091619103/2000000000000 : ℝ)*(sp3) + (14610028937/25000000000000 : ℝ)*(sp4) + (19207975703/100000000000000 : ℝ)*(sp7) + (1909661894465427/50000000000000 : ℝ)*(f.failure) + (7559714795233573/100000000000000 : ℝ)*(f.sum) + (297532553257/243125000000000000000000000 : ℝ)*base65 + (1113786675832998977/194500000000000000000000000000000 : ℝ)*base67 + (3347707917041498977/194500000000000000000000000000000 : ℝ)*base69 + (2297551604933501023/194500000000000000000000000000000 : ℝ)*base72 + (10555388990741/1945000000000000000000000000 : ℝ)*base73 + (2134195776181998977/194500000000000000000000000000000 : ℝ)*base75 + (272931986052001023/194500000000000000000000000000000 : ℝ)*base78 + (1156722817881498977/194500000000000000000000000000000 : ℝ)*base79 + (29528736834421/1945000000000000000000000000 : ℝ)*base81 + (968191/500000000000000000000 : ℝ)*base90 + (968191/500000000000000000000 : ℝ)*base92 + (968191/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (807164692730290949935243941/194500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (382495387/50000000000000 : ℝ)*(base19) + (82061657/10000000000000 : ℝ)*(base23) + (18800169/25000000000000 : ℝ)*(upper3) + (35531989/100000000000000 : ℝ)*(lower4) + (36614141/50000000000000 : ℝ)*(upper5) + (5719120372733371/100000000000000 : ℝ)*(major0) + (5719120372733371/100000000000000 : ℝ)*(major1) + (5719120372733371/100000000000000 : ℝ)*(major2) + (9981154921/50000000000000 : ℝ)*(sp1) + (21581042421/100000000000000 : ℝ)*(sp2) + (7599045992169707/100000000000000 : ℝ)*(sp4) + (7599025264869091/100000000000000 : ℝ)*(sp5) + (1899755897627679/25000000000000 : ℝ)*(sp6) + (3839194614965463/100000000000000 : ℝ)*(sp7) + (3839194614965463/100000000000000 : ℝ)*(f.failure) + (7599045992169707/100000000000000 : ℝ)*(f.sum) + (2475481204447/1945000000000000000000000000 : ℝ)*base66 + (1217513933752885353/389000000000000000000000000000000 : ℝ)*base68 + (2944584907990885353/389000000000000000000000000000000 : ℝ)*base70 + (3649626960983885353/389000000000000000000000000000000 : ℝ)*base72 + (7674985246563/1945000000000000000000000000 : ℝ)*base73 + (4207581079433114647/389000000000000000000000000000000 : ℝ)*base75 + (1297184896549885353/389000000000000000000000000000000 : ℝ)*base78 + (436498822893114647/389000000000000000000000000000000 : ℝ)*base79 + (3577952196187/1945000000000000000000000000 : ℝ)*base82 + (8811821/1000000000000000000000 : ℝ)*base89 + (8811821/1000000000000000000000 : ℝ)*base91 + (8811821/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1116_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1116_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1116_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1116_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1116_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1116_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
