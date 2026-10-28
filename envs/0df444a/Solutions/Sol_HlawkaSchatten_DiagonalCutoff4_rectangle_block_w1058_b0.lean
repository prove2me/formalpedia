-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1058_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:01:17.857761+00:00
-- url     : https://prove2.me/submissions/f0b33c8c-63b1-4671-b198-00c557ee23c3

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
theorem support_rectangle_w1058_s0_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-959341921/5000000000 : ℝ)*x 0 + (6073949123/10000000000 : ℝ)*x 1 + (4769757633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959341921/5000000000 : ℝ)^8251 ≤ (11124430872247/100000000000000 : ℝ)^6203 := by
    have hnat : (959341921 : ℕ)^8251*100000000000000^6203 ≤ 11124430872247^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959341921 5000000000 11124430872247 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6073949123/10000000000 : ℝ)^8251 ≤ (12880163671843/25000000000000 : ℝ)^6203 := by
    have hnat : (6073949123 : ℕ)^8251*25000000000000^6203 ≤ 12880163671843^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6073949123 10000000000 12880163671843 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769757633/10000000000 : ℝ)^8251 ≤ (37354914427979/100000000000000 : ℝ)^6203 := by
    have hnat : (4769757633 : ℕ)^8251*100000000000000^6203 ≤ 37354914427979^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769757633 10000000000 37354914427979 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959341921/5000000000 : ℝ), (6073949123/10000000000 : ℝ), (4769757633/10000000000 : ℝ)] ![(11124430872247/100000000000000 : ℝ), (12880163671843/25000000000000 : ℝ), (37354914427979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959341921/5000000000 : ℝ)|^8251 ≤ (11124430872247/100000000000000 : ℝ)^6203
        have hw : |(-959341921/5000000000 : ℝ)|=(959341921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6073949123/10000000000 : ℝ)|^8251 ≤ (12880163671843/25000000000000 : ℝ)^6203
        have hw : |(6073949123/10000000000 : ℝ)|=(6073949123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769757633/10000000000 : ℝ)|^8251 ≤ (37354914427979/100000000000000 : ℝ)^6203
        have hw : |(4769757633/10000000000 : ℝ)|=(4769757633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s0_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521523233/10000000000 : ℝ)*x 0 + (-2669622901/10000000000 : ℝ)*x 1 + (74527463/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521523233/10000000000 : ℝ)^8251 ≤ (45383328328679/100000000000000 : ℝ)^6203 := by
    have hnat : (5521523233 : ℕ)^8251*100000000000000^6203 ≤ 45383328328679^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521523233 10000000000 45383328328679 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2669622901/10000000000 : ℝ)^8251 ≤ (8630878618607/50000000000000 : ℝ)^6203 := by
    have hnat : (2669622901 : ℕ)^8251*50000000000000^6203 ≤ 8630878618607^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669622901 10000000000 8630878618607 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74527463/156250000 : ℝ)^8251 ≤ (18677457208781/50000000000000 : ℝ)^6203 := by
    have hnat : (74527463 : ℕ)^8251*50000000000000^6203 ≤ 18677457208781^6203*156250000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74527463 156250000 18677457208781 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521523233/10000000000 : ℝ), (-2669622901/10000000000 : ℝ), (74527463/156250000 : ℝ)] ![(45383328328679/100000000000000 : ℝ), (8630878618607/50000000000000 : ℝ), (18677457208781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521523233/10000000000 : ℝ)|^8251 ≤ (45383328328679/100000000000000 : ℝ)^6203
        have hw : |(5521523233/10000000000 : ℝ)|=(5521523233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2669622901/10000000000 : ℝ)|^8251 ≤ (8630878618607/50000000000000 : ℝ)^6203
        have hw : |(-2669622901/10000000000 : ℝ)|=(2669622901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74527463/156250000 : ℝ)|^8251 ≤ (18677457208781/50000000000000 : ℝ)^6203
        have hw : |(74527463/156250000 : ℝ)|=(74527463/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s0_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521523233/10000000000 : ℝ)*x 0 + (4769757631/10000000000 : ℝ)*x 1 + (-1334811451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521523233/10000000000 : ℝ)^8251 ≤ (45383328328679/100000000000000 : ℝ)^6203 := by
    have hnat : (5521523233 : ℕ)^8251*100000000000000^6203 ≤ 45383328328679^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521523233 10000000000 45383328328679 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4769757631/10000000000 : ℝ)^8251 ≤ (7470982881429/20000000000000 : ℝ)^6203 := by
    have hnat : (4769757631 : ℕ)^8251*20000000000000^6203 ≤ 7470982881429^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769757631 10000000000 7470982881429 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1334811451/5000000000 : ℝ)^8251 ≤ (3452351449163/20000000000000 : ℝ)^6203 := by
    have hnat : (1334811451 : ℕ)^8251*20000000000000^6203 ≤ 3452351449163^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334811451 5000000000 3452351449163 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521523233/10000000000 : ℝ), (4769757631/10000000000 : ℝ), (-1334811451/5000000000 : ℝ)] ![(45383328328679/100000000000000 : ℝ), (7470982881429/20000000000000 : ℝ), (3452351449163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521523233/10000000000 : ℝ)|^8251 ≤ (45383328328679/100000000000000 : ℝ)^6203
        have hw : |(5521523233/10000000000 : ℝ)|=(5521523233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4769757631/10000000000 : ℝ)|^8251 ≤ (7470982881429/20000000000000 : ℝ)^6203
        have hw : |(4769757631/10000000000 : ℝ)|=(4769757631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1334811451/5000000000 : ℝ)|^8251 ≤ (3452351449163/20000000000000 : ℝ)^6203
        have hw : |(-1334811451/5000000000 : ℝ)|=(1334811451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s0_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4207872731/10000000000 : ℝ)*x 0 + (78132419/250000000 : ℝ)*x 1 + (2838635881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207872731/10000000000 : ℝ)^8251 ≤ (15809278315951/50000000000000 : ℝ)^6203 := by
    have hnat : (4207872731 : ℕ)^8251*50000000000000^6203 ≤ 15809278315951^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207872731 10000000000 15809278315951 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78132419/250000000 : ℝ)^8251 ≤ (4257485031081/20000000000000 : ℝ)^6203 := by
    have hnat : (78132419 : ℕ)^8251*20000000000000^6203 ≤ 4257485031081^6203*250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78132419 250000000 4257485031081 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2838635881/5000000000 : ℝ)^8251 ≤ (23547009097999/50000000000000 : ℝ)^6203 := by
    have hnat : (2838635881 : ℕ)^8251*50000000000000^6203 ≤ 23547009097999^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838635881 5000000000 23547009097999 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207872731/10000000000 : ℝ), (78132419/250000000 : ℝ), (2838635881/5000000000 : ℝ)] ![(15809278315951/50000000000000 : ℝ), (4257485031081/20000000000000 : ℝ), (23547009097999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207872731/10000000000 : ℝ)|^8251 ≤ (15809278315951/50000000000000 : ℝ)^6203
        have hw : |(4207872731/10000000000 : ℝ)|=(4207872731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78132419/250000000 : ℝ)|^8251 ≤ (4257485031081/20000000000000 : ℝ)^6203
        have hw : |(78132419/250000000 : ℝ)|=(78132419/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2838635881/5000000000 : ℝ)|^8251 ≤ (23547009097999/50000000000000 : ℝ)^6203
        have hw : |(2838635881/5000000000 : ℝ)|=(2838635881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s0_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1924081161/10000000000 : ℝ)*x 0 + (600429421/1250000000 : ℝ)*x 1 + (3019547171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1924081161/10000000000 : ℝ)^8251 ≤ (5583037740227/50000000000000 : ℝ)^6203 := by
    have hnat : (1924081161 : ℕ)^8251*50000000000000^6203 ≤ 5583037740227^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924081161 10000000000 5583037740227 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600429421/1250000000 : ℝ)^8251 ≤ (18853077321331/50000000000000 : ℝ)^6203 := by
    have hnat : (600429421 : ℕ)^8251*50000000000000^6203 ≤ 18853077321331^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600429421 1250000000 18853077321331 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3019547171/5000000000 : ℝ)^8251 ≤ (1022555397247/2000000000000 : ℝ)^6203 := by
    have hnat : (3019547171 : ℕ)^8251*2000000000000^6203 ≤ 1022555397247^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019547171 5000000000 1022555397247 2000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1924081161/10000000000 : ℝ), (600429421/1250000000 : ℝ), (3019547171/5000000000 : ℝ)] ![(5583037740227/50000000000000 : ℝ), (18853077321331/50000000000000 : ℝ), (1022555397247/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1924081161/10000000000 : ℝ)|^8251 ≤ (5583037740227/50000000000000 : ℝ)^6203
        have hw : |(-1924081161/10000000000 : ℝ)|=(1924081161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600429421/1250000000 : ℝ)|^8251 ≤ (18853077321331/50000000000000 : ℝ)^6203
        have hw : |(600429421/1250000000 : ℝ)|=(600429421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3019547171/5000000000 : ℝ)|^8251 ≤ (1022555397247/2000000000000 : ℝ)^6203
        have hw : |(3019547171/5000000000 : ℝ)|=(3019547171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s0_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5167588779/10000000000 : ℝ)*x 0 + (-1400289671/10000000000 : ℝ)*x 1 + (6039092717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167588779/10000000000 : ℝ)^8251 ≤ (41555286909831/100000000000000 : ℝ)^6203 := by
    have hnat : (5167588779 : ℕ)^8251*100000000000000^6203 ≤ 41555286909831^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167588779 10000000000 41555286909831 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400289671/10000000000 : ℝ)^8251 ≤ (1829240379189/25000000000000 : ℝ)^6203 := by
    have hnat : (1400289671 : ℕ)^8251*25000000000000^6203 ≤ 1829240379189^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400289671 10000000000 1829240379189 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6039092717/10000000000 : ℝ)^8251 ≤ (51127751562683/100000000000000 : ℝ)^6203 := by
    have hnat : (6039092717 : ℕ)^8251*100000000000000^6203 ≤ 51127751562683^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6039092717 10000000000 51127751562683 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167588779/10000000000 : ℝ), (-1400289671/10000000000 : ℝ), (6039092717/10000000000 : ℝ)] ![(41555286909831/100000000000000 : ℝ), (1829240379189/25000000000000 : ℝ), (51127751562683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167588779/10000000000 : ℝ)|^8251 ≤ (41555286909831/100000000000000 : ℝ)^6203
        have hw : |(5167588779/10000000000 : ℝ)|=(5167588779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1400289671/10000000000 : ℝ)|^8251 ≤ (1829240379189/25000000000000 : ℝ)^6203
        have hw : |(-1400289671/10000000000 : ℝ)|=(1400289671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6039092717/10000000000 : ℝ)|^8251 ≤ (51127751562683/100000000000000 : ℝ)^6203
        have hw : |(6039092717/10000000000 : ℝ)|=(6039092717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s0_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5167589869/10000000000 : ℝ)*x 0 + (6039092687/10000000000 : ℝ)*x 1 + (-1400288041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167589869/10000000000 : ℝ)^8251 ≤ (1298603080283/3125000000000 : ℝ)^6203 := by
    have hnat : (5167589869 : ℕ)^8251*3125000000000^6203 ≤ 1298603080283^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167589869 10000000000 1298603080283 3125000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6039092687/10000000000 : ℝ)^8251 ≤ (51127751224843/100000000000000 : ℝ)^6203 := by
    have hnat : (6039092687 : ℕ)^8251*100000000000000^6203 ≤ 51127751224843^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6039092687 10000000000 51127751224843 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1400288041/10000000000 : ℝ)^8251 ≤ (36584750937/500000000000 : ℝ)^6203 := by
    have hnat : (1400288041 : ℕ)^8251*500000000000^6203 ≤ 36584750937^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400288041 10000000000 36584750937 500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167589869/10000000000 : ℝ), (6039092687/10000000000 : ℝ), (-1400288041/10000000000 : ℝ)] ![(1298603080283/3125000000000 : ℝ), (51127751224843/100000000000000 : ℝ), (36584750937/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167589869/10000000000 : ℝ)|^8251 ≤ (1298603080283/3125000000000 : ℝ)^6203
        have hw : |(5167589869/10000000000 : ℝ)|=(5167589869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6039092687/10000000000 : ℝ)|^8251 ≤ (51127751224843/100000000000000 : ℝ)^6203
        have hw : |(6039092687/10000000000 : ℝ)|=(6039092687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1400288041/10000000000 : ℝ)|^8251 ≤ (36584750937/500000000000 : ℝ)^6203
        have hw : |(-1400288041/10000000000 : ℝ)|=(1400288041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s0_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4218434181/10000000000 : ℝ)*x 0 + (280568511/500000000 : ℝ)*x 1 + (319350027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4218434181/10000000000 : ℝ)^8251 ≤ (31724162391987/100000000000000 : ℝ)^6203 := by
    have hnat : (4218434181 : ℕ)^8251*100000000000000^6203 ≤ 31724162391987^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218434181 10000000000 31724162391987 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280568511/500000000 : ℝ)^8251 ≤ (23184130579403/50000000000000 : ℝ)^6203 := by
    have hnat : (280568511 : ℕ)^8251*50000000000000^6203 ≤ 23184130579403^6203*500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280568511 500000000 23184130579403 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319350027/1000000000 : ℝ)^8251 ≤ (1369223527271/6250000000000 : ℝ)^6203 := by
    have hnat : (319350027 : ℕ)^8251*6250000000000^6203 ≤ 1369223527271^6203*1000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319350027 1000000000 1369223527271 6250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4218434181/10000000000 : ℝ), (280568511/500000000 : ℝ), (319350027/1000000000 : ℝ)] ![(31724162391987/100000000000000 : ℝ), (23184130579403/50000000000000 : ℝ), (1369223527271/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4218434181/10000000000 : ℝ)|^8251 ≤ (31724162391987/100000000000000 : ℝ)^6203
        have hw : |(4218434181/10000000000 : ℝ)|=(4218434181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280568511/500000000 : ℝ)|^8251 ≤ (23184130579403/50000000000000 : ℝ)^6203
        have hw : |(280568511/500000000 : ℝ)|=(280568511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319350027/1000000000 : ℝ)|^8251 ≤ (1369223527271/6250000000000 : ℝ)^6203
        have hw : |(319350027/1000000000 : ℝ)|=(319350027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (63/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/5000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
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
  have hpowlo : (0 : ℝ) ^ (4125/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4125 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4125*1^1024 ≤ 0^1024*1^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4125/1024 : ℝ) ≤ (99776937829220319/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4125 ≤ (99776937829220319/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4125*4000000000000000000^1024 ≤ 99776937829220319^1024*5^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 99776937829220319 4000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (99776937829220319/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4125 := by
      have hnat : (1 : ℕ)^1024*1^4125 ≤ 1^4125*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4099776937829220319/4000000000000000000 : ℝ) ≤ (10061349903485647/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (4099776937829220319/4000000000000000000 : ℝ)^1024 ≤ (10061349903485647/10000000000000000 : ℝ)^4125 := by
      have hnat : (4099776937829220319 : ℕ)^1024*10000000000000000^4125 ≤ 10061349903485647^4125*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4099776937829220319 4000000000000000000 10061349903485647 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061349903485647/10000000000000000 : ℝ)) (X := (4099776937829220319/4000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2099776937829220319/2000000000000000000 : ℝ) ≤ (5061349903485647/5000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (2099776937829220319/2000000000000000000 : ℝ)^1024 ≤ (5061349903485647/5000000000000000 : ℝ)^4125 := by
      have hnat : (2099776937829220319 : ℕ)^1024*5000000000000000^4125 ≤ 5061349903485647^4125*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2099776937829220319 2000000000000000000 5061349903485647 5000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061349903485647/5000000000000000 : ℝ)) (X := (2099776937829220319/2000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61349903485647/4000000000000000 : ℝ)*(0 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(61349903485647/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(99776937829220319/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61349903485647/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (1 : ℝ)+(61349903485647/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061349903485647/10000000000000000 : ℝ) by norm_num, show 1+(99776937829220319/4000000000000000000 : ℝ)+(0 : ℝ)=(4099776937829220319/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(99776937829220319/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61349903485647/4000000000000000 : ℝ)*(2/5 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(61349903485647/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061349903485647/5000000000000000 : ℝ) by norm_num, show 1+2*(99776937829220319/4000000000000000000 : ℝ)=(2099776937829220319/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61349903485647/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61349903485647/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61349903485647/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61349903485647/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61349903485647/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61349903485647/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-959341921/5000000000 : ℝ)*X 0 0+(6073949123/10000000000 : ℝ)*X 0 1+(4769757633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5521523233/10000000000 : ℝ)*X 1 0+(-2669622901/10000000000 : ℝ)*X 1 1+(74527463/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5521523233/10000000000 : ℝ)*X 2 0+(4769757631/10000000000 : ℝ)*X 2 1+(-1334811451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4207872731/10000000000 : ℝ)*X 0 0+(78132419/250000000 : ℝ)*X 0 1+(2838635881/5000000000 : ℝ)*X 0 2+(4207872731/10000000000 : ℝ)*X 1 0+(78132419/250000000 : ℝ)*X 1 1+(2838635881/5000000000 : ℝ)*X 1 2+(4207872731/10000000000 : ℝ)*X 2 0+(78132419/250000000 : ℝ)*X 2 1+(2838635881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1924081161/10000000000 : ℝ)*X 0 0+(600429421/1250000000 : ℝ)*X 0 1+(3019547171/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167588779/10000000000 : ℝ)*X 1 0+(-1400289671/10000000000 : ℝ)*X 1 1+(6039092717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5167589869/10000000000 : ℝ)*X 2 0+(6039092687/10000000000 : ℝ)*X 2 1+(-1400288041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4218434181/10000000000 : ℝ)*X 0 0+(280568511/500000000 : ℝ)*X 0 1+(319350027/1000000000 : ℝ)*X 0 2+(4218434181/10000000000 : ℝ)*X 1 0+(280568511/500000000 : ℝ)*X 1 1+(319350027/1000000000 : ℝ)*X 1 2+(4218434181/10000000000 : ℝ)*X 2 0+(280568511/500000000 : ℝ)*X 2 1+(319350027/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (232977750401858843289849/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12449471/50000000000000 : ℝ)*(base1) + (586102429/100000000000000 : ℝ)*(base19) + (546687503/100000000000000 : ℝ)*(base23) + (19707463/50000000000000 : ℝ)*(base24) + (65819337/50000000000000 : ℝ)*(upper3) + (289654215436063/50000000000000 : ℝ)*(major0) + (289654215436063/50000000000000 : ℝ)*(major1) + (289654215436063/50000000000000 : ℝ)*(major2) + (23961265356881/3125000000000 : ℝ)*(sp0) + (766761164193511/100000000000000 : ℝ)*(sp1) + (766761164193511/100000000000000 : ℝ)*(sp2) + (391853980977409/100000000000000 : ℝ)*(sp3) + (1283774689/100000000000000 : ℝ)*(sp4) + (1027912707/100000000000000 : ℝ)*(sp7) + (195927516894529/50000000000000 : ℝ)*(f.failure) + (38338087514797/5000000000000 : ℝ)*(f.sum) + (156954268612239/100000000000000000000000000000 : ℝ)*base66 + (326721257087761/200000000000000000000000000000 : ℝ)*base67 + (563802377712239/200000000000000000000000000000 : ℝ)*base70 + (540586835112239/200000000000000000000000000000 : ℝ)*base72 + (4607269787761/100000000000000000000000000000 : ℝ)*base73 + (898220533312239/200000000000000000000000000000 : ℝ)*base76 + (540586835112239/200000000000000000000000000000 : ℝ)*base78 + (302126797512239/200000000000000000000000000000 : ℝ)*base80 + (460600895912239/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6578623/1000000000000000000000 : ℝ)*base89 + (6578623/1000000000000000000000 : ℝ)*base91 + (6578623/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (242558765735108951862171/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115245257/25000000000000 : ℝ)*(base19) + (618540767/100000000000000 : ℝ)*(base23) + (1297271/5000000000000 : ℝ)*(base51) + (10216271/20000000000000 : ℝ)*(upper3) + (178701319/100000000000000 : ℝ)*(upper5) + (611436517182969/100000000000000 : ℝ)*(major0) + (611436517182969/100000000000000 : ℝ)*(major1) + (611436517182969/100000000000000 : ℝ)*(major2) + (108233483/20000000000000 : ℝ)*(sp2) + (3499399/10000000000000 : ℝ)*(sp3) + (809285882563781/100000000000000 : ℝ)*(sp4) + (25290169424461/3125000000000 : ℝ)*(sp5) + (404642361427799/50000000000000 : ℝ)*(sp6) + (206793517977619/50000000000000 : ℝ)*(sp7) + (103396767737307/25000000000000 : ℝ)*(f.failure) + (809285882563781/100000000000000 : ℝ)*(f.sum) + (474747041054057/200000000000000000000000000000 : ℝ)*base66 + (1090105897145943/400000000000000000000000000000 : ℝ)*base67 + (1764121667545943/400000000000000000000000000000 : ℝ)*base69 + (2535575733945943/400000000000000000000000000000 : ℝ)*base71 + (155403669254057/200000000000000000000000000000 : ℝ)*base74 + (3394205634745943/400000000000000000000000000000 : ℝ)*base75 + (1661715914345943/400000000000000000000000000000 : ℝ)*base77 + (4765146183945943/400000000000000000000000000000 : ℝ)*base79 + (216025805945943/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (862491/500000000000000000000 : ℝ)*base90 + (862491/500000000000000000000 : ℝ)*base92 + (862491/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1058_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1058_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1058_s1_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129392337/10000000000 : ℝ)*x 0 + (2862278067/5000000000 : ℝ)*x 1 + (4867388/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129392337/10000000000 : ℝ)^8251 ≤ (6389114797353/50000000000000 : ℝ)^6203 := by
    have hnat : (2129392337 : ℕ)^8251*50000000000000^6203 ≤ 6389114797353^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129392337 10000000000 6389114797353 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2862278067/5000000000 : ℝ)^8251 ≤ (23808233715799/50000000000000 : ℝ)^6203 := by
    have hnat : (2862278067 : ℕ)^8251*50000000000000^6203 ≤ 23808233715799^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2862278067 5000000000 23808233715799 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4867388/9765625 : ℝ)^8251 ≤ (39605302958951/100000000000000 : ℝ)^6203 := by
    have hnat : (4867388 : ℕ)^8251*100000000000000^6203 ≤ 39605302958951^6203*9765625^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867388 9765625 39605302958951 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129392337/10000000000 : ℝ), (2862278067/5000000000 : ℝ), (4867388/9765625 : ℝ)] ![(6389114797353/50000000000000 : ℝ), (23808233715799/50000000000000 : ℝ), (39605302958951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129392337/10000000000 : ℝ)|^8251 ≤ (6389114797353/50000000000000 : ℝ)^6203
        have hw : |(-2129392337/10000000000 : ℝ)|=(2129392337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2862278067/5000000000 : ℝ)|^8251 ≤ (23808233715799/50000000000000 : ℝ)^6203
        have hw : |(2862278067/5000000000 : ℝ)|=(2862278067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4867388/9765625 : ℝ)|^8251 ≤ (39605302958951/100000000000000 : ℝ)^6203
        have hw : |(4867388/9765625 : ℝ)|=(4867388/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s1_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5423751711/10000000000 : ℝ)*x 0 + (-2530685639/10000000000 : ℝ)*x 1 + (4984205637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423751711/10000000000 : ℝ)^8251 ≤ (44317522279541/100000000000000 : ℝ)^6203 := by
    have hnat : (5423751711 : ℕ)^8251*100000000000000^6203 ≤ 44317522279541^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423751711 10000000000 44317522279541 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530685639/10000000000 : ℝ)^8251 ≤ (16077171308571/100000000000000 : ℝ)^6203 := by
    have hnat : (2530685639 : ℕ)^8251*100000000000000^6203 ≤ 16077171308571^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530685639 10000000000 16077171308571 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4984205637/10000000000 : ℝ)^8251 ≤ (396053063941/1000000000000 : ℝ)^6203 := by
    have hnat : (4984205637 : ℕ)^8251*1000000000000^6203 ≤ 396053063941^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984205637 10000000000 396053063941 1000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423751711/10000000000 : ℝ), (-2530685639/10000000000 : ℝ), (4984205637/10000000000 : ℝ)] ![(44317522279541/100000000000000 : ℝ), (16077171308571/100000000000000 : ℝ), (396053063941/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423751711/10000000000 : ℝ)|^8251 ≤ (44317522279541/100000000000000 : ℝ)^6203
        have hw : |(5423751711/10000000000 : ℝ)|=(5423751711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2530685639/10000000000 : ℝ)|^8251 ≤ (16077171308571/100000000000000 : ℝ)^6203
        have hw : |(-2530685639/10000000000 : ℝ)|=(2530685639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4984205637/10000000000 : ℝ)|^8251 ≤ (396053063941/1000000000000 : ℝ)^6203
        have hw : |(4984205637/10000000000 : ℝ)|=(4984205637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s1_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355938053/2500000000 : ℝ)*x 0 + (4984205049/10000000000 : ℝ)*x 1 + (-253068573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355938053/2500000000 : ℝ)^8251 ≤ (11079381931199/25000000000000 : ℝ)^6203 := by
    have hnat : (1355938053 : ℕ)^8251*25000000000000^6203 ≤ 11079381931199^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355938053 2500000000 11079381931199 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4984205049/10000000000 : ℝ)^8251 ≤ (39605300179123/100000000000000 : ℝ)^6203 := by
    have hnat : (4984205049 : ℕ)^8251*100000000000000^6203 ≤ 39605300179123^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984205049 10000000000 39605300179123 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253068573/1000000000 : ℝ)^8251 ≤ (4019293019389/25000000000000 : ℝ)^6203 := by
    have hnat : (253068573 : ℕ)^8251*25000000000000^6203 ≤ 4019293019389^6203*1000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253068573 1000000000 4019293019389 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355938053/2500000000 : ℝ), (4984205049/10000000000 : ℝ), (-253068573/1000000000 : ℝ)] ![(11079381931199/25000000000000 : ℝ), (39605300179123/100000000000000 : ℝ), (4019293019389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355938053/2500000000 : ℝ)|^8251 ≤ (11079381931199/25000000000000 : ℝ)^6203
        have hw : |(1355938053/2500000000 : ℝ)|=(1355938053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4984205049/10000000000 : ℝ)|^8251 ≤ (39605300179123/100000000000000 : ℝ)^6203
        have hw : |(4984205049/10000000000 : ℝ)|=(4984205049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253068573/1000000000 : ℝ)|^8251 ≤ (4019293019389/25000000000000 : ℝ)^6203
        have hw : |(-253068573/1000000000 : ℝ)|=(253068573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s1_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1081116859/2500000000 : ℝ)*x 0 + (915254401/2500000000 : ℝ)*x 1 + (5109696751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081116859/2500000000 : ℝ)^8251 ≤ (1024663206851/3125000000000 : ℝ)^6203 := by
    have hnat : (1081116859 : ℕ)^8251*3125000000000^6203 ≤ 1024663206851^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081116859 2500000000 1024663206851 3125000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915254401/2500000000 : ℝ)^8251 ≤ (26273586498531/100000000000000 : ℝ)^6203 := by
    have hnat : (915254401 : ℕ)^8251*100000000000000^6203 ≤ 26273586498531^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915254401 2500000000 26273586498531 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5109696751/10000000000 : ℝ)^8251 ≤ (10234297717371/25000000000000 : ℝ)^6203 := by
    have hnat : (5109696751 : ℕ)^8251*25000000000000^6203 ≤ 10234297717371^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109696751 10000000000 10234297717371 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081116859/2500000000 : ℝ), (915254401/2500000000 : ℝ), (5109696751/10000000000 : ℝ)] ![(1024663206851/3125000000000 : ℝ), (26273586498531/100000000000000 : ℝ), (10234297717371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081116859/2500000000 : ℝ)|^8251 ≤ (1024663206851/3125000000000 : ℝ)^6203
        have hw : |(1081116859/2500000000 : ℝ)|=(1081116859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915254401/2500000000 : ℝ)|^8251 ≤ (26273586498531/100000000000000 : ℝ)^6203
        have hw : |(915254401/2500000000 : ℝ)|=(915254401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5109696751/10000000000 : ℝ)|^8251 ≤ (10234297717371/25000000000000 : ℝ)^6203
        have hw : |(5109696751/10000000000 : ℝ)|=(5109696751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s1_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065163479/5000000000 : ℝ)*x 0 + (4994640769/10000000000 : ℝ)*x 1 + (1428476513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065163479/5000000000 : ℝ)^8251 ≤ (6392845209433/50000000000000 : ℝ)^6203 := by
    have hnat : (1065163479 : ℕ)^8251*50000000000000^6203 ≤ 6392845209433^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065163479 5000000000 6392845209433 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4994640769/10000000000 : ℝ)^8251 ≤ (39715640602561/100000000000000 : ℝ)^6203 := by
    have hnat : (4994640769 : ℕ)^8251*100000000000000^6203 ≤ 39715640602561^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994640769 10000000000 39715640602561 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1428476513/2500000000 : ℝ)^8251 ≤ (4749866896011/10000000000000 : ℝ)^6203 := by
    have hnat : (1428476513 : ℕ)^8251*10000000000000^6203 ≤ 4749866896011^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428476513 2500000000 4749866896011 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065163479/5000000000 : ℝ), (4994640769/10000000000 : ℝ), (1428476513/2500000000 : ℝ)] ![(6392845209433/50000000000000 : ℝ), (39715640602561/100000000000000 : ℝ), (4749866896011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065163479/5000000000 : ℝ)|^8251 ≤ (6392845209433/50000000000000 : ℝ)^6203
        have hw : |(-1065163479/5000000000 : ℝ)|=(1065163479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4994640769/10000000000 : ℝ)|^8251 ≤ (39715640602561/100000000000000 : ℝ)^6203
        have hw : |(4994640769/10000000000 : ℝ)|=(4994640769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1428476513/2500000000 : ℝ)|^8251 ≤ (4749866896011/10000000000000 : ℝ)^6203
        have hw : |(1428476513/2500000000 : ℝ)|=(1428476513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s1_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617378627/5000000000 : ℝ)*x 0 + (-7203933/40000000 : ℝ)*x 1 + (357119223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617378627/5000000000 : ℝ)^8251 ≤ (42275294094783/100000000000000 : ℝ)^6203 := by
    have hnat : (2617378627 : ℕ)^8251*100000000000000^6203 ≤ 42275294094783^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617378627 5000000000 42275294094783 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7203933/40000000 : ℝ)^8251 ≤ (2045204033009/20000000000000 : ℝ)^6203 := by
    have hnat : (7203933 : ℕ)^8251*20000000000000^6203 ≤ 2045204033009^6203*40000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7203933 40000000 2045204033009 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357119223/625000000 : ℝ)^8251 ≤ (23749342861567/50000000000000 : ℝ)^6203 := by
    have hnat : (357119223 : ℕ)^8251*50000000000000^6203 ≤ 23749342861567^6203*625000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357119223 625000000 23749342861567 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617378627/5000000000 : ℝ), (-7203933/40000000 : ℝ), (357119223/625000000 : ℝ)] ![(42275294094783/100000000000000 : ℝ), (2045204033009/20000000000000 : ℝ), (23749342861567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617378627/5000000000 : ℝ)|^8251 ≤ (42275294094783/100000000000000 : ℝ)^6203
        have hw : |(2617378627/5000000000 : ℝ)|=(2617378627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7203933/40000000 : ℝ)|^8251 ≤ (2045204033009/20000000000000 : ℝ)^6203
        have hw : |(-7203933/40000000 : ℝ)|=(7203933/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(357119223/625000000 : ℝ)|^8251 ≤ (23749342861567/50000000000000 : ℝ)^6203
        have hw : |(357119223/625000000 : ℝ)|=(357119223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s1_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617377633/5000000000 : ℝ)*x 0 + (5713909757/10000000000 : ℝ)*x 1 + (-1800982873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617377633/5000000000 : ℝ)^8251 ≤ (42275272739209/100000000000000 : ℝ)^6203 := by
    have hnat : (2617377633 : ℕ)^8251*100000000000000^6203 ≤ 42275272739209^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617377633 5000000000 42275272739209 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5713909757/10000000000 : ℝ)^8251 ≤ (23749354963897/50000000000000 : ℝ)^6203 := by
    have hnat : (5713909757 : ℕ)^8251*50000000000000^6203 ≤ 23749354963897^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5713909757 10000000000 23749354963897 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800982873/10000000000 : ℝ)^8251 ≤ (127825216471/1250000000000 : ℝ)^6203 := by
    have hnat : (1800982873 : ℕ)^8251*1250000000000^6203 ≤ 127825216471^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800982873 10000000000 127825216471 1250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617377633/5000000000 : ℝ), (5713909757/10000000000 : ℝ), (-1800982873/10000000000 : ℝ)] ![(42275272739209/100000000000000 : ℝ), (23749354963897/50000000000000 : ℝ), (127825216471/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617377633/5000000000 : ℝ)|^8251 ≤ (42275272739209/100000000000000 : ℝ)^6203
        have hw : |(2617377633/5000000000 : ℝ)|=(2617377633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5713909757/10000000000 : ℝ)|^8251 ≤ (23749354963897/50000000000000 : ℝ)^6203
        have hw : |(5713909757/10000000000 : ℝ)|=(5713909757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1800982873/10000000000 : ℝ)|^8251 ≤ (127825216471/1250000000000 : ℝ)^6203
        have hw : |(-1800982873/10000000000 : ℝ)|=(1800982873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s1_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1081573151/2500000000 : ℝ)*x 0 + (1017854751/2000000000 : ℝ)*x 1 + (3681853993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081573151/2500000000 : ℝ)^8251 ≤ (32807631881967/100000000000000 : ℝ)^6203 := by
    have hnat : (1081573151 : ℕ)^8251*100000000000000^6203 ≤ 32807631881967^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081573151 2500000000 32807631881967 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017854751/2000000000 : ℝ)^8251 ≤ (20359845183543/50000000000000 : ℝ)^6203 := by
    have hnat : (1017854751 : ℕ)^8251*50000000000000^6203 ≤ 20359845183543^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017854751 2000000000 20359845183543 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3681853993/10000000000 : ℝ)^8251 ≤ (26472677732383/100000000000000 : ℝ)^6203 := by
    have hnat : (3681853993 : ℕ)^8251*100000000000000^6203 ≤ 26472677732383^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681853993 10000000000 26472677732383 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081573151/2500000000 : ℝ), (1017854751/2000000000 : ℝ), (3681853993/10000000000 : ℝ)] ![(32807631881967/100000000000000 : ℝ), (20359845183543/50000000000000 : ℝ), (26472677732383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081573151/2500000000 : ℝ)|^8251 ≤ (32807631881967/100000000000000 : ℝ)^6203
        have hw : |(1081573151/2500000000 : ℝ)|=(1081573151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1017854751/2000000000 : ℝ)|^8251 ≤ (20359845183543/50000000000000 : ℝ)^6203
        have hw : |(1017854751/2000000000 : ℝ)|=(1017854751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3681853993/10000000000 : ℝ)|^8251 ≤ (26472677732383/100000000000000 : ℝ)^6203
        have hw : |(3681853993/10000000000 : ℝ)|=(3681853993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20829/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1407/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (63/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1407/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (63/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1407/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (63/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1407/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (63/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1407/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (63/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1407/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (63/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (63/100000 : ℝ) ^ (4125/1024 : ℝ) ≤ (3196381/25000000000000000000 : ℝ) := by
    have hpowers : (63/100000 : ℝ)^4125 ≤ (3196381/25000000000000000000 : ℝ)^1024 := by
      have hnat : (63 : ℕ)^4125*25000000000000000000^1024 ≤ 3196381^1024*100000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63 100000 3196381 25000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63/100000 : ℝ)) (X := (3196381/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1407/5000 : ℝ) ^ (4125/1024 : ℝ) ≤ (302462169515160073/50000000000000000000 : ℝ) := by
    have hpowers : (1407/5000 : ℝ)^4125 ≤ (302462169515160073/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1407 : ℕ)^4125*50000000000000000000^1024 ≤ 302462169515160073^1024*5000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 5000 302462169515160073 50000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/5000 : ℝ)) (X := (302462169515160073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000000003196381/12500000000000000000 : ℝ) ≤ (2000000000000127/2000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (12500000000003196381/12500000000000000000 : ℝ)^1024 ≤ (2000000000000127/2000000000000000 : ℝ)^4125 := by
      have hnat : (12500000000003196381 : ℕ)^1024*2000000000000000^4125 ≤ 2000000000000127^4125*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000000003196381 12500000000000000000 2000000000000127 2000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000000127/2000000000000000 : ℝ)) (X := (12500000000003196381/12500000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10060492433904310567/10000000000000000000 : ℝ) ≤ (5007491381821367/5000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (10060492433904310567/10000000000000000000 : ℝ)^1024 ≤ (5007491381821367/5000000000000000 : ℝ)^4125 := by
      have hnat : (10060492433904310567 : ℕ)^1024*5000000000000000^4125 ≤ 5007491381821367^4125*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10060492433904310567 10000000000000000000 5007491381821367 5000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007491381821367/5000000000000000 : ℝ)) (X := (10060492433904310567/10000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25302462169515160073/25000000000000000000 : ℝ) ≤ (10029965527284833/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (25302462169515160073/25000000000000000000 : ℝ)^1024 ≤ (10029965527284833/10000000000000000 : ℝ)^4125 := by
      have hnat : (25302462169515160073 : ℕ)^1024*10000000000000000^4125 ≤ 10029965527284833^4125*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25302462169515160073 25000000000000000000 10029965527284833 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029965527284833/10000000000000000 : ℝ)) (X := (25302462169515160073/25000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3196381/25000000000000000000 : ℝ) ≤ ((13369910103418996401/13370000000000000000 : ℝ)+2*(14982763642099/2807700000000000 : ℝ)*(63/100000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (13369910103418996401/13370000000000000000 : ℝ)+2*(14982763642099/2807700000000000 : ℝ)*(63/100000 : ℝ)=(2000000000000127/2000000000000000 : ℝ) by norm_num, show 1+2*(3196381/25000000000000000000 : ℝ)=(12500000000003196381/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(302462169515160073/50000000000000000000 : ℝ)+(3196381/25000000000000000000 : ℝ) ≤ ((13369910103418996401/13370000000000000000 : ℝ)+(14982763642099/2807700000000000 : ℝ)*((1407/5000 : ℝ)+(63/100000 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (13369910103418996401/13370000000000000000 : ℝ)+(14982763642099/2807700000000000 : ℝ)*((1407/5000 : ℝ)+(63/100000 : ℝ))=(5007491381821367/5000000000000000 : ℝ) by norm_num, show 1+(302462169515160073/50000000000000000000 : ℝ)+(3196381/25000000000000000000 : ℝ)=(10060492433904310567/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(302462169515160073/50000000000000000000 : ℝ) ≤ ((13369910103418996401/13370000000000000000 : ℝ)+2*(14982763642099/2807700000000000 : ℝ)*(1407/5000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (13369910103418996401/13370000000000000000 : ℝ)+2*(14982763642099/2807700000000000 : ℝ)*(1407/5000 : ℝ)=(10029965527284833/10000000000000000 : ℝ) by norm_num, show 1+2*(302462169515160073/50000000000000000000 : ℝ)=(25302462169515160073/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13369910103418996401/13370000000000000000 : ℝ)*(X 1 0+X 2 0)+(14982763642099/2807700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (63/100000 : ℝ)) (hi := (1407/5000 : ℝ)) (c := (13369910103418996401/13370000000000000000 : ℝ)) (alpha := (14982763642099/2807700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13369910103418996401/13370000000000000000 : ℝ)*(X 0 1+X 2 1)+(14982763642099/2807700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (63/100000 : ℝ)) (hi := (1407/5000 : ℝ)) (c := (13369910103418996401/13370000000000000000 : ℝ)) (alpha := (14982763642099/2807700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13369910103418996401/13370000000000000000 : ℝ)*(X 0 2+X 1 2)+(14982763642099/2807700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (63/100000 : ℝ)) (hi := (1407/5000 : ℝ)) (c := (13369910103418996401/13370000000000000000 : ℝ)) (alpha := (14982763642099/2807700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2129392337/10000000000 : ℝ)*X 0 0+(2862278067/5000000000 : ℝ)*X 0 1+(4867388/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5423751711/10000000000 : ℝ)*X 1 0+(-2530685639/10000000000 : ℝ)*X 1 1+(4984205637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355938053/2500000000 : ℝ)*X 2 0+(4984205049/10000000000 : ℝ)*X 2 1+(-253068573/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081116859/2500000000 : ℝ)*X 0 0+(915254401/2500000000 : ℝ)*X 0 1+(5109696751/10000000000 : ℝ)*X 0 2+(1081116859/2500000000 : ℝ)*X 1 0+(915254401/2500000000 : ℝ)*X 1 1+(5109696751/10000000000 : ℝ)*X 1 2+(1081116859/2500000000 : ℝ)*X 2 0+(915254401/2500000000 : ℝ)*X 2 1+(5109696751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065163479/5000000000 : ℝ)*X 0 0+(4994640769/10000000000 : ℝ)*X 0 1+(1428476513/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617378627/5000000000 : ℝ)*X 1 0+(-7203933/40000000 : ℝ)*X 1 1+(357119223/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2617377633/5000000000 : ℝ)*X 2 0+(5713909757/10000000000 : ℝ)*X 2 1+(-1800982873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081573151/2500000000 : ℝ)*X 0 0+(1017854751/2000000000 : ℝ)*X 0 1+(3681853993/10000000000 : ℝ)*X 0 2+(1081573151/2500000000 : ℝ)*X 1 0+(1017854751/2000000000 : ℝ)*X 1 1+(3681853993/10000000000 : ℝ)*X 1 2+(1081573151/2500000000 : ℝ)*X 2 0+(1017854751/2000000000 : ℝ)*X 2 1+(3681853993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15338648697450758124138791443/2339750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115679663/100000000000000 : ℝ)*(base1) + (288534211/20000000000000 : ℝ)*(base19) + (783719723/50000000000000 : ℝ)*(base23) + (7619751/5000000000000 : ℝ)*(upper3) + (38948341/25000000000000 : ℝ)*(upper5) + (510254207125417/50000000000000 : ℝ)*(major0) + (510254207125417/50000000000000 : ℝ)*(major1) + (510254207125417/50000000000000 : ℝ)*(major2) + (1350718149789107/100000000000000 : ℝ)*(sp0) + (1350724231016493/100000000000000 : ℝ)*(sp1) + (1350724106248101/100000000000000 : ℝ)*(sp2) + (690287292710161/100000000000000 : ℝ)*(sp3) + (954947263/12500000000000 : ℝ)*(sp4) + (3527901673/100000000000000 : ℝ)*(sp7) + (690290936291497/100000000000000 : ℝ)*(f.failure) + (337681418421887/25000000000000 : ℝ)*(f.sum) + (60769136626721/140385000000000000000000000000 : ℝ)*base65 + (59217377239968908557/14038500000000000000000000000000000 : ℝ)*base67 + (8823277881312591443/14038500000000000000000000000000000 : ℝ)*base70 + (30629480595255908557/14038500000000000000000000000000000 : ℝ)*base71 + (308165818341373/70192500000000000000000000000 : ℝ)*base73 + (46574899613399091443/14038500000000000000000000000000000 : ℝ)*base76 + (63738161323529408557/14038500000000000000000000000000000 : ℝ)*base77 + (87722444306021408557/14038500000000000000000000000000000 : ℝ)*base79 + (18945838571899/8774062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (14241961/2000000000000000000000 : ℝ)*base90 + (14241961/2000000000000000000000 : ℝ)*base92 + (14241961/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52434889126507307513039/23397500000000000000000000000 : ℝ) := by norm_num
    linear_combination (226508621/10000000000000 : ℝ)*(base19) + (2184002473/100000000000000 : ℝ)*(base23) + (53608371/25000000000000 : ℝ)*(upper2) + (181324071/50000000000000 : ℝ)*(upper3) + (248392113/50000000000000 : ℝ)*(upper5) + (525206428177181/50000000000000 : ℝ)*(major0) + (525206428177181/50000000000000 : ℝ)*(major1) + (525206428177181/50000000000000 : ℝ)*(major2) + (448928099/4000000000000 : ℝ)*(sp1) + (6127771169/50000000000000 : ℝ)*(sp2) + (1390306778995331/100000000000000 : ℝ)*(sp4) + (695146645353323/50000000000000 : ℝ)*(sp5) + (34757308486263/2500000000000 : ℝ)*(sp6) + (355259429505917/50000000000000 : ℝ)*(sp7) + (355259429505917/50000000000000 : ℝ)*(f.failure) + (1390306778995331/100000000000000 : ℝ)*(f.sum) + (3399100347653/2193515625000000000000000000 : ℝ)*base66 + (11036810617338762799/14038500000000000000000000000000000 : ℝ)*base68 + (103462175761308737201/14038500000000000000000000000000000 : ℝ)*base69 + (901074488274762799/14038500000000000000000000000000000 : ℝ)*base72 + (278180039362487/140385000000000000000000000000 : ℝ)*base74 + (83050122483605237201/14038500000000000000000000000000000 : ℝ)*base75 + (21795910040204262799/14038500000000000000000000000000000 : ℝ)*base78 + (10493494062135737201/14038500000000000000000000000000000 : ℝ)*base79 + (20789514481499/4387031250000000000000000000 : ℝ)*base81 + (2679421/1000000000000000000000 : ℝ)*base90 + (2679421/1000000000000000000000 : ℝ)*base92 + (2679421/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1058_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20829/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1058_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1058_s2_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-437452727/2000000000 : ℝ)*x 0 + (5527565119/10000000000 : ℝ)*x 1 + (1028897699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437452727/2000000000 : ℝ)^8251 ≤ (6621113464713/50000000000000 : ℝ)^6203 := by
    have hnat : (437452727 : ℕ)^8251*50000000000000^6203 ≤ 6621113464713^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437452727 2000000000 6621113464713 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527565119/10000000000 : ℝ)^8251 ≤ (9089879327681/20000000000000 : ℝ)^6203 := by
    have hnat : (5527565119 : ℕ)^8251*20000000000000^6203 ≤ 9089879327681^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527565119 10000000000 9089879327681 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028897699/2000000000 : ℝ)^8251 ≤ (41308376422457/100000000000000 : ℝ)^6203 := by
    have hnat : (1028897699 : ℕ)^8251*100000000000000^6203 ≤ 41308376422457^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028897699 2000000000 41308376422457 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437452727/2000000000 : ℝ), (5527565119/10000000000 : ℝ), (1028897699/2000000000 : ℝ)] ![(6621113464713/50000000000000 : ℝ), (9089879327681/20000000000000 : ℝ), (41308376422457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437452727/2000000000 : ℝ)|^8251 ≤ (6621113464713/50000000000000 : ℝ)^6203
        have hw : |(-437452727/2000000000 : ℝ)|=(437452727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527565119/10000000000 : ℝ)|^8251 ≤ (9089879327681/20000000000000 : ℝ)^6203
        have hw : |(5527565119/10000000000 : ℝ)|=(5527565119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028897699/2000000000 : ℝ)|^8251 ≤ (41308376422457/100000000000000 : ℝ)^6203
        have hw : |(1028897699/2000000000 : ℝ)|=(1028897699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s2_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5377561737/10000000000 : ℝ)*x 0 + (-37298583/156250000 : ℝ)*x 1 + (5144489897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377561737/10000000000 : ℝ)^8251 ≤ (21908100559691/50000000000000 : ℝ)^6203 := by
    have hnat : (5377561737 : ℕ)^8251*50000000000000^6203 ≤ 21908100559691^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377561737 10000000000 21908100559691 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37298583/156250000 : ℝ)^8251 ≤ (1859425932913/12500000000000 : ℝ)^6203 := by
    have hnat : (37298583 : ℕ)^8251*12500000000000^6203 ≤ 1859425932913^6203*156250000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37298583 156250000 1859425932913 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144489897/10000000000 : ℝ)^8251 ≤ (20654195698417/50000000000000 : ℝ)^6203 := by
    have hnat : (5144489897 : ℕ)^8251*50000000000000^6203 ≤ 20654195698417^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144489897 10000000000 20654195698417 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377561737/10000000000 : ℝ), (-37298583/156250000 : ℝ), (5144489897/10000000000 : ℝ)] ![(21908100559691/50000000000000 : ℝ), (1859425932913/12500000000000 : ℝ), (20654195698417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377561737/10000000000 : ℝ)|^8251 ≤ (21908100559691/50000000000000 : ℝ)^6203
        have hw : |(5377561737/10000000000 : ℝ)|=(5377561737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37298583/156250000 : ℝ)|^8251 ≤ (1859425932913/12500000000000 : ℝ)^6203
        have hw : |(-37298583/156250000 : ℝ)|=(37298583/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144489897/10000000000 : ℝ)|^8251 ≤ (20654195698417/50000000000000 : ℝ)^6203
        have hw : |(5144489897/10000000000 : ℝ)|=(5144489897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s2_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (215102477/400000000 : ℝ)*x 0 + (1028897911/2000000000 : ℝ)*x 1 + (-2387109507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215102477/400000000 : ℝ)^8251 ≤ (876324063139/2000000000000 : ℝ)^6203 := by
    have hnat : (215102477 : ℕ)^8251*2000000000000^6203 ≤ 876324063139^6203*400000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215102477 400000000 876324063139 2000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028897911/2000000000 : ℝ)^8251 ≤ (1652335509761/4000000000000 : ℝ)^6203 := by
    have hnat : (1028897911 : ℕ)^8251*4000000000000^6203 ≤ 1652335509761^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028897911 2000000000 1652335509761 4000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387109507/10000000000 : ℝ)^8251 ≤ (1859426134957/12500000000000 : ℝ)^6203 := by
    have hnat : (2387109507 : ℕ)^8251*12500000000000^6203 ≤ 1859426134957^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387109507 10000000000 1859426134957 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215102477/400000000 : ℝ), (1028897911/2000000000 : ℝ), (-2387109507/10000000000 : ℝ)] ![(876324063139/2000000000000 : ℝ), (1652335509761/4000000000000 : ℝ), (1859426134957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215102477/400000000 : ℝ)|^8251 ≤ (876324063139/2000000000000 : ℝ)^6203
        have hw : |(215102477/400000000 : ℝ)|=(215102477/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028897911/2000000000 : ℝ)|^8251 ≤ (1652335509761/4000000000000 : ℝ)^6203
        have hw : |(1028897911/2000000000 : ℝ)|=(1028897911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2387109507/10000000000 : ℝ)|^8251 ≤ (1859426134957/12500000000000 : ℝ)^6203
        have hw : |(-2387109507/10000000000 : ℝ)|=(2387109507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s2_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545491569/1250000000 : ℝ)*x 0 + (2002700889/5000000000 : ℝ)*x 1 + (118874487/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545491569/1250000000 : ℝ)^8251 ≤ (8296962962077/25000000000000 : ℝ)^6203 := by
    have hnat : (545491569 : ℕ)^8251*25000000000000^6203 ≤ 8296962962077^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545491569 1250000000 8296962962077 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002700889/5000000000 : ℝ)^8251 ≤ (29611103739507/100000000000000 : ℝ)^6203 := by
    have hnat : (2002700889 : ℕ)^8251*100000000000000^6203 ≤ 29611103739507^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002700889 5000000000 29611103739507 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118874487/250000000 : ℝ)^8251 ≤ (37201044390923/100000000000000 : ℝ)^6203 := by
    have hnat : (118874487 : ℕ)^8251*100000000000000^6203 ≤ 37201044390923^6203*250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118874487 250000000 37201044390923 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545491569/1250000000 : ℝ), (2002700889/5000000000 : ℝ), (118874487/250000000 : ℝ)] ![(8296962962077/25000000000000 : ℝ), (29611103739507/100000000000000 : ℝ), (37201044390923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545491569/1250000000 : ℝ)|^8251 ≤ (8296962962077/25000000000000 : ℝ)^6203
        have hw : |(545491569/1250000000 : ℝ)|=(545491569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002700889/5000000000 : ℝ)|^8251 ≤ (29611103739507/100000000000000 : ℝ)^6203
        have hw : |(2002700889/5000000000 : ℝ)|=(2002700889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118874487/250000000 : ℝ)|^8251 ≤ (37201044390923/100000000000000 : ℝ)^6203
        have hw : |(118874487/250000000 : ℝ)|=(118874487/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s2_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093696019/5000000000 : ℝ)*x 0 + (514729211/1000000000 : ℝ)*x 1 + (5524732171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093696019/5000000000 : ℝ)^8251 ≤ (6621630492737/50000000000000 : ℝ)^6203 := by
    have hnat : (1093696019 : ℕ)^8251*50000000000000^6203 ≤ 6621630492737^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093696019 5000000000 6621630492737 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514729211/1000000000 : ℝ)^8251 ≤ (41338323756801/100000000000000 : ℝ)^6203 := by
    have hnat : (514729211 : ℕ)^8251*100000000000000^6203 ≤ 41338323756801^6203*1000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514729211 1000000000 41338323756801 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5524732171/10000000000 : ℝ)^8251 ≤ (11354603811837/25000000000000 : ℝ)^6203 := by
    have hnat : (5524732171 : ℕ)^8251*25000000000000^6203 ≤ 11354603811837^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524732171 10000000000 11354603811837 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093696019/5000000000 : ℝ), (514729211/1000000000 : ℝ), (5524732171/10000000000 : ℝ)] ![(6621630492737/50000000000000 : ℝ), (41338323756801/100000000000000 : ℝ), (11354603811837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093696019/5000000000 : ℝ)|^8251 ≤ (6621630492737/50000000000000 : ℝ)^6203
        have hw : |(-1093696019/5000000000 : ℝ)|=(1093696019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514729211/1000000000 : ℝ)|^8251 ≤ (41338323756801/100000000000000 : ℝ)^6203
        have hw : |(514729211/1000000000 : ℝ)|=(514729211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5524732171/10000000000 : ℝ)|^8251 ≤ (11354603811837/25000000000000 : ℝ)^6203
        have hw : |(5524732171/10000000000 : ℝ)|=(5524732171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s2_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5280924131/10000000000 : ℝ)*x 0 + (-2006867899/10000000000 : ℝ)*x 1 + (690591531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280924131/10000000000 : ℝ)^8251 ≤ (42771950436201/100000000000000 : ℝ)^6203 := by
    have hnat : (5280924131 : ℕ)^8251*100000000000000^6203 ≤ 42771950436201^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280924131 10000000000 42771950436201 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006867899/10000000000 : ℝ)^8251 ≤ (11809633466311/100000000000000 : ℝ)^6203 := by
    have hnat : (2006867899 : ℕ)^8251*100000000000000^6203 ≤ 11809633466311^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006867899 10000000000 11809633466311 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690591531/1250000000 : ℝ)^8251 ≤ (11354604022339/25000000000000 : ℝ)^6203 := by
    have hnat : (690591531 : ℕ)^8251*25000000000000^6203 ≤ 11354604022339^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690591531 1250000000 11354604022339 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280924131/10000000000 : ℝ), (-2006867899/10000000000 : ℝ), (690591531/1250000000 : ℝ)] ![(42771950436201/100000000000000 : ℝ), (11809633466311/100000000000000 : ℝ), (11354604022339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280924131/10000000000 : ℝ)|^8251 ≤ (42771950436201/100000000000000 : ℝ)^6203
        have hw : |(5280924131/10000000000 : ℝ)|=(5280924131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2006867899/10000000000 : ℝ)|^8251 ≤ (11809633466311/100000000000000 : ℝ)^6203
        have hw : |(-2006867899/10000000000 : ℝ)|=(2006867899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(690591531/1250000000 : ℝ)|^8251 ≤ (11354604022339/25000000000000 : ℝ)^6203
        have hw : |(690591531/1250000000 : ℝ)|=(690591531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s2_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5280924371/10000000000 : ℝ)*x 0 + (1381183021/2500000000 : ℝ)*x 1 + (-1003433899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280924371/10000000000 : ℝ)^8251 ≤ (334155882983/781250000000 : ℝ)^6203 := by
    have hnat : (5280924371 : ℕ)^8251*781250000000^6203 ≤ 334155882983^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280924371 10000000000 334155882983 781250000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381183021/2500000000 : ℝ)^8251 ≤ (11354603573997/25000000000000 : ℝ)^6203 := by
    have hnat : (1381183021 : ℕ)^8251*25000000000000^6203 ≤ 11354603573997^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381183021 2500000000 11354603573997 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003433899/5000000000 : ℝ)^8251 ≤ (5904816337867/50000000000000 : ℝ)^6203 := by
    have hnat : (1003433899 : ℕ)^8251*50000000000000^6203 ≤ 5904816337867^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003433899 5000000000 5904816337867 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280924371/10000000000 : ℝ), (1381183021/2500000000 : ℝ), (-1003433899/5000000000 : ℝ)] ![(334155882983/781250000000 : ℝ), (11354603573997/25000000000000 : ℝ), (5904816337867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280924371/10000000000 : ℝ)|^8251 ≤ (334155882983/781250000000 : ℝ)^6203
        have hw : |(5280924371/10000000000 : ℝ)|=(5280924371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381183021/2500000000 : ℝ)|^8251 ≤ (11354603573997/25000000000000 : ℝ)^6203
        have hw : |(1381183021/2500000000 : ℝ)|=(1381183021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003433899/5000000000 : ℝ)|^8251 ≤ (5904816337867/50000000000000 : ℝ)^6203
        have hw : |(-1003433899/5000000000 : ℝ)|=(1003433899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s2_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218209157/500000000 : ℝ)*x 0 + (4749498063/10000000000 : ℝ)*x 1 + (802188493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218209157/500000000 : ℝ)^8251 ≤ (33190386803609/100000000000000 : ℝ)^6203 := by
    have hnat : (218209157 : ℕ)^8251*100000000000000^6203 ≤ 33190386803609^6203*500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218209157 500000000 33190386803609 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4749498063/10000000000 : ℝ)^8251 ≤ (37144012015869/100000000000000 : ℝ)^6203 := by
    have hnat : (4749498063 : ℕ)^8251*100000000000000^6203 ≤ 37144012015869^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749498063 10000000000 37144012015869 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802188493/2000000000 : ℝ)^8251 ≤ (3708200146861/12500000000000 : ℝ)^6203 := by
    have hnat : (802188493 : ℕ)^8251*12500000000000^6203 ≤ 3708200146861^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802188493 2000000000 3708200146861 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218209157/500000000 : ℝ), (4749498063/10000000000 : ℝ), (802188493/2000000000 : ℝ)] ![(33190386803609/100000000000000 : ℝ), (37144012015869/100000000000000 : ℝ), (3708200146861/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218209157/500000000 : ℝ)|^8251 ≤ (33190386803609/100000000000000 : ℝ)^6203
        have hw : |(218209157/500000000 : ℝ)|=(218209157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4749498063/10000000000 : ℝ)|^8251 ≤ (37144012015869/100000000000000 : ℝ)^6203
        have hw : |(4749498063/10000000000 : ℝ)|=(4749498063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802188493/2000000000 : ℝ)|^8251 ≤ (3708200146861/12500000000000 : ℝ)^6203
        have hw : |(802188493/2000000000 : ℝ)|=(802188493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (271/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2583/50000 : ℝ) ^ (4125/1024 : ℝ) ≤ (654898111190389/100000000000000000000 : ℝ) := by
    have hpowers : (2583/50000 : ℝ)^4125 ≤ (654898111190389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2583 : ℕ)^4125*100000000000000000000^1024 ≤ 654898111190389^1024*50000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2583 50000 654898111190389 100000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2583/50000 : ℝ)) (X := (654898111190389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20829/100000 : ℝ) ^ (4125/1024 : ℝ) ≤ (90021897112687377/50000000000000000000 : ℝ) := by
    have hpowers : (20829/100000 : ℝ)^4125 ≤ (90021897112687377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (20829 : ℕ)^4125*50000000000000000000^1024 ≤ 90021897112687377^1024*100000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20829 100000 90021897112687377 50000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20829/100000 : ℝ)) (X := (90021897112687377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000654898111190389/50000000000000000000 : ℝ) ≤ (80000260116311/80000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (50000654898111190389/50000000000000000000 : ℝ)^1024 ≤ (80000260116311/80000000000000 : ℝ)^4125 := by
      have hnat : (50000654898111190389 : ℕ)^1024*80000000000000^4125 ≤ 80000260116311^4125*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000654898111190389 50000000000000000000 80000260116311 80000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80000260116311/80000000000000 : ℝ)) (X := (50000654898111190389/50000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100180698692336565143/100000000000000000000 : ℝ) ≤ (10004482664625923/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (100180698692336565143/100000000000000000000 : ℝ)^1024 ≤ (10004482664625923/10000000000000000 : ℝ)^4125 := by
      have hnat : (100180698692336565143 : ℕ)^1024*10000000000000000^4125 ≤ 10004482664625923^4125*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100180698692336565143 100000000000000000000 10004482664625923 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004482664625923/10000000000000000 : ℝ)) (X := (100180698692336565143/100000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25090021897112687377/25000000000000000000 : ℝ) ≤ (10008932814712971/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (25090021897112687377/25000000000000000000 : ℝ)^1024 ≤ (10008932814712971/10000000000000000 : ℝ)^4125 := by
      have hnat : (25090021897112687377 : ℕ)^1024*10000000000000000^4125 ≤ 10008932814712971^4125*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25090021897112687377 25000000000000000000 10008932814712971 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008932814712971/10000000000000000 : ℝ)) (X := (25090021897112687377/25000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(654898111190389/100000000000000000000 : ℝ) ≤ ((52194843441507673063/52210000000000000000 : ℝ)+2*(556268760881/195787500000000 : ℝ)*(2583/50000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (52194843441507673063/52210000000000000000 : ℝ)+2*(556268760881/195787500000000 : ℝ)*(2583/50000 : ℝ)=(80000260116311/80000000000000 : ℝ) by norm_num, show 1+2*(654898111190389/100000000000000000000 : ℝ)=(50000654898111190389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(90021897112687377/50000000000000000000 : ℝ)+(654898111190389/100000000000000000000 : ℝ) ≤ ((52194843441507673063/52210000000000000000 : ℝ)+(556268760881/195787500000000 : ℝ)*((20829/100000 : ℝ)+(2583/50000 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (52194843441507673063/52210000000000000000 : ℝ)+(556268760881/195787500000000 : ℝ)*((20829/100000 : ℝ)+(2583/50000 : ℝ))=(10004482664625923/10000000000000000 : ℝ) by norm_num, show 1+(90021897112687377/50000000000000000000 : ℝ)+(654898111190389/100000000000000000000 : ℝ)=(100180698692336565143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(90021897112687377/50000000000000000000 : ℝ) ≤ ((52194843441507673063/52210000000000000000 : ℝ)+2*(556268760881/195787500000000 : ℝ)*(20829/100000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (52194843441507673063/52210000000000000000 : ℝ)+2*(556268760881/195787500000000 : ℝ)*(20829/100000 : ℝ)=(10008932814712971/10000000000000000 : ℝ) by norm_num, show 1+2*(90021897112687377/50000000000000000000 : ℝ)=(25090021897112687377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52194843441507673063/52210000000000000000 : ℝ)*(X 1 0+X 2 0)+(556268760881/195787500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (2583/50000 : ℝ)) (hi := (20829/100000 : ℝ)) (c := (52194843441507673063/52210000000000000000 : ℝ)) (alpha := (556268760881/195787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52194843441507673063/52210000000000000000 : ℝ)*(X 0 1+X 2 1)+(556268760881/195787500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (2583/50000 : ℝ)) (hi := (20829/100000 : ℝ)) (c := (52194843441507673063/52210000000000000000 : ℝ)) (alpha := (556268760881/195787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52194843441507673063/52210000000000000000 : ℝ)*(X 0 2+X 1 2)+(556268760881/195787500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (2583/50000 : ℝ)) (hi := (20829/100000 : ℝ)) (c := (52194843441507673063/52210000000000000000 : ℝ)) (alpha := (556268760881/195787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437452727/2000000000 : ℝ)*X 0 0+(5527565119/10000000000 : ℝ)*X 0 1+(1028897699/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377561737/10000000000 : ℝ)*X 1 0+(-37298583/156250000 : ℝ)*X 1 1+(5144489897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((215102477/400000000 : ℝ)*X 2 0+(1028897911/2000000000 : ℝ)*X 2 1+(-2387109507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545491569/1250000000 : ℝ)*X 0 0+(2002700889/5000000000 : ℝ)*X 0 1+(118874487/250000000 : ℝ)*X 0 2+(545491569/1250000000 : ℝ)*X 1 0+(2002700889/5000000000 : ℝ)*X 1 1+(118874487/250000000 : ℝ)*X 1 2+(545491569/1250000000 : ℝ)*X 2 0+(2002700889/5000000000 : ℝ)*X 2 1+(118874487/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1093696019/5000000000 : ℝ)*X 0 0+(514729211/1000000000 : ℝ)*X 0 1+(5524732171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280924131/10000000000 : ℝ)*X 1 0+(-2006867899/10000000000 : ℝ)*X 1 1+(690591531/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280924371/10000000000 : ℝ)*X 2 0+(1381183021/2500000000 : ℝ)*X 2 1+(-1003433899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218209157/500000000 : ℝ)*X 0 0+(4749498063/10000000000 : ℝ)*X 0 1+(802188493/2000000000 : ℝ)*X 0 2+(218209157/500000000 : ℝ)*X 1 0+(4749498063/10000000000 : ℝ)*X 1 1+(802188493/2000000000 : ℝ)*X 1 2+(218209157/500000000 : ℝ)*X 2 0+(4749498063/10000000000 : ℝ)*X 2 1+(802188493/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (301957211751257573898239237/56750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168752727/100000000000000 : ℝ)*(base1) + (166870823/6250000000000 : ℝ)*(base19) + (138059837/5000000000000 : ℝ)*(base23) + (157505051/50000000000000 : ℝ)*(upper3) + (221433483/100000000000000 : ℝ)*(upper5) + (986154315892759/50000000000000 : ℝ)*(major0) + (986154315892759/50000000000000 : ℝ)*(major1) + (986154315892759/50000000000000 : ℝ)*(major2) + (2610477737571827/100000000000000 : ℝ)*(sp0) + (652627012549007/25000000000000 : ℝ)*(sp1) + (1305253979466227/50000000000000 : ℝ)*(sp2) + (166761854918327/12500000000000 : ℝ)*(sp3) + (2071956881/6250000000000 : ℝ)*(sp4) + (454319257/4000000000000 : ℝ)*(sp7) + (5211352992503/390625000000 : ℝ)*(f.failure) + (522102144025839/20000000000000 : ℝ)*(f.sum) + (9797078857873/3405000000000000000000000000 : ℝ)*base65 + (2479440501543810763/340500000000000000000000000000000 : ℝ)*base68 + (206117138688810763/340500000000000000000000000000000 : ℝ)*base70 + (1345912995609810763/340500000000000000000000000000000 : ℝ)*base72 + (2601093001933/3405000000000000000000000000 : ℝ)*base73 + (1401136052756310763/340500000000000000000000000000000 : ℝ)*base76 + (1120998160973189237/340500000000000000000000000000000 : ℝ)*base77 + (1413471142977689237/340500000000000000000000000000000 : ℝ)*base79 + (10980927936733/3405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (43789/7812500000000000000 : ℝ)*base90 + (43789/7812500000000000000 : ℝ)*base92 + (43789/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102130176248451301705059/26105000000000000000000000000 : ℝ) := by norm_num
    linear_combination (726473147/100000000000000 : ℝ)*(base19) + (224301133/25000000000000 : ℝ)*(base23) + (22939729/20000000000000 : ℝ)*(upper3) + (1153841/10000000000000 : ℝ)*(lower4) + (83180891/100000000000000 : ℝ)*(upper5) + (1000855485609503/50000000000000 : ℝ)*(major0) + (1000855485609503/50000000000000 : ℝ)*(major1) + (1000855485609503/50000000000000 : ℝ)*(major2) + (6070289867/100000000000000 : ℝ)*(sp1) + (7626345439/100000000000000 : ℝ)*(sp2) + (331178394355471/12500000000000 : ℝ)*(sp4) + (1324710179040377/50000000000000 : ℝ)*(sp5) + (662354657823449/25000000000000 : ℝ)*(sp6) + (1353994657184769/100000000000000 : ℝ)*(sp7) + (1353994657184769/100000000000000 : ℝ)*(f.failure) + (331178394355471/12500000000000 : ℝ)*(f.sum) + (9693729967163/19578750000000000000000000000 : ℝ)*base66 + (24322482520656346933/7831500000000000000000000000000000 : ℝ)*base68 + (13254246955515346933/7831500000000000000000000000000000 : ℝ)*base70 + (5689115849265346933/7831500000000000000000000000000000 : ℝ)*base72 + (306132119237267/78315000000000000000000000000 : ℝ)*base74 + (1574946059650153067/7831500000000000000000000000000000 : ℝ)*base75 + (38965951187237653067/7831500000000000000000000000000000 : ℝ)*base77 + (56814441647230153067/7831500000000000000000000000000000 : ℝ)*base79 + (97470558901493/19578750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5994497/2000000000000000000000 : ℝ)*base90 + (5994497/2000000000000000000000 : ℝ)*base92 + (5994497/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1058_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (271/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1058_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1058_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (271/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16767/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1058_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1058_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1058_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (271/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16767/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1058_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
