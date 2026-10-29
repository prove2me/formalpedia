-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1566_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:55.719203+00:00
-- url     : https://prove2.me/submissions/322d97e8-0718-40db-88ee-d6153d381c86

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
theorem support_rectangle_w1566_s3_0 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1790832613/10000000000 : ℝ)*x 0 + (2714024047/5000000000 : ℝ)*x 1 + (1043669499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1790832613/10000000000 : ℝ)^4629 ≤ (1373394585291/12500000000000 : ℝ)^3605 := by
    have hnat : (1790832613 : ℕ)^4629*12500000000000^3605 ≤ 1373394585291^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790832613 10000000000 1373394585291 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714024047/5000000000 : ℝ)^4629 ≤ (45631972768021/100000000000000 : ℝ)^3605 := by
    have hnat : (2714024047 : ℕ)^4629*100000000000000^3605 ≤ 45631972768021^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714024047 5000000000 45631972768021 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043669499/2000000000 : ℝ)^4629 ≤ (8676174107477/20000000000000 : ℝ)^3605 := by
    have hnat : (1043669499 : ℕ)^4629*20000000000000^3605 ≤ 8676174107477^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043669499 2000000000 8676174107477 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1790832613/10000000000 : ℝ), (2714024047/5000000000 : ℝ), (1043669499/2000000000 : ℝ)] ![(1373394585291/12500000000000 : ℝ), (45631972768021/100000000000000 : ℝ), (8676174107477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1790832613/10000000000 : ℝ)|^4629 ≤ (1373394585291/12500000000000 : ℝ)^3605
        have hw : |(-1790832613/10000000000 : ℝ)|=(1790832613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714024047/5000000000 : ℝ)|^4629 ≤ (45631972768021/100000000000000 : ℝ)^3605
        have hw : |(2714024047/5000000000 : ℝ)|=(2714024047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043669499/2000000000 : ℝ)|^4629 ≤ (8676174107477/20000000000000 : ℝ)^3605
        have hw : |(1043669499/2000000000 : ℝ)|=(1043669499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s3_1 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668612373/1250000000 : ℝ)*x 0 + (-474539839/2500000000 : ℝ)*x 1 + (1043669499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668612373/1250000000 : ℝ)^4629 ≤ (44779363557937/100000000000000 : ℝ)^3605 := by
    have hnat : (668612373 : ℕ)^4629*100000000000000^3605 ≤ 44779363557937^3605*1250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668612373 1250000000 44779363557937 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474539839/2500000000 : ℝ)^4629 ≤ (2367953176681/20000000000000 : ℝ)^3605 := by
    have hnat : (474539839 : ℕ)^4629*20000000000000^3605 ≤ 2367953176681^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474539839 2500000000 2367953176681 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043669499/2000000000 : ℝ)^4629 ≤ (8676174107477/20000000000000 : ℝ)^3605 := by
    have hnat : (1043669499 : ℕ)^4629*20000000000000^3605 ≤ 8676174107477^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043669499 2000000000 8676174107477 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668612373/1250000000 : ℝ), (-474539839/2500000000 : ℝ), (1043669499/2000000000 : ℝ)] ![(44779363557937/100000000000000 : ℝ), (2367953176681/20000000000000 : ℝ), (8676174107477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668612373/1250000000 : ℝ)|^4629 ≤ (44779363557937/100000000000000 : ℝ)^3605
        have hw : |(668612373/1250000000 : ℝ)|=(668612373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474539839/2500000000 : ℝ)|^4629 ≤ (2367953176681/20000000000000 : ℝ)^3605
        have hw : |(-474539839/2500000000 : ℝ)|=(474539839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043669499/2000000000 : ℝ)|^4629 ≤ (8676174107477/20000000000000 : ℝ)^3605
        have hw : |(1043669499/2000000000 : ℝ)|=(1043669499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s3_2 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668612373/1250000000 : ℝ)*x 0 + (652293437/1250000000 : ℝ)*x 1 + (-474539839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668612373/1250000000 : ℝ)^4629 ≤ (44779363557937/100000000000000 : ℝ)^3605 := by
    have hnat : (668612373 : ℕ)^4629*100000000000000^3605 ≤ 44779363557937^3605*1250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668612373 1250000000 44779363557937 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652293437/1250000000 : ℝ)^4629 ≤ (2169043527403/5000000000000 : ℝ)^3605 := by
    have hnat : (652293437 : ℕ)^4629*5000000000000^3605 ≤ 2169043527403^3605*1250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652293437 1250000000 2169043527403 5000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474539839/2500000000 : ℝ)^4629 ≤ (2367953176681/20000000000000 : ℝ)^3605 := by
    have hnat : (474539839 : ℕ)^4629*20000000000000^3605 ≤ 2367953176681^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474539839 2500000000 2367953176681 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668612373/1250000000 : ℝ), (652293437/1250000000 : ℝ), (-474539839/2500000000 : ℝ)] ![(44779363557937/100000000000000 : ℝ), (2169043527403/5000000000000 : ℝ), (2367953176681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668612373/1250000000 : ℝ)|^4629 ≤ (44779363557937/100000000000000 : ℝ)^3605
        have hw : |(668612373/1250000000 : ℝ)|=(668612373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652293437/1250000000 : ℝ)|^4629 ≤ (2169043527403/5000000000000 : ℝ)^3605
        have hw : |(652293437/1250000000 : ℝ)|=(652293437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474539839/2500000000 : ℝ)|^4629 ≤ (2367953176681/20000000000000 : ℝ)^3605
        have hw : |(-474539839/2500000000 : ℝ)|=(474539839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s3_3 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061276371/2500000000 : ℝ)*x 0 + (4004104019/10000000000 : ℝ)*x 1 + (2248883347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061276371/2500000000 : ℝ)^4629 ≤ (16640265100981/50000000000000 : ℝ)^3605 := by
    have hnat : (1061276371 : ℕ)^4629*50000000000000^3605 ≤ 16640265100981^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061276371 2500000000 16640265100981 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4004104019/10000000000 : ℝ)^4629 ≤ (30874293163853/100000000000000 : ℝ)^3605 := by
    have hnat : (4004104019 : ℕ)^4629*100000000000000^3605 ≤ 30874293163853^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4004104019 10000000000 30874293163853 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248883347/5000000000 : ℝ)^4629 ≤ (2240323538313/6250000000000 : ℝ)^3605 := by
    have hnat : (2248883347 : ℕ)^4629*6250000000000^3605 ≤ 2240323538313^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248883347 5000000000 2240323538313 6250000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061276371/2500000000 : ℝ), (4004104019/10000000000 : ℝ), (2248883347/5000000000 : ℝ)] ![(16640265100981/50000000000000 : ℝ), (30874293163853/100000000000000 : ℝ), (2240323538313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061276371/2500000000 : ℝ)|^4629 ≤ (16640265100981/50000000000000 : ℝ)^3605
        have hw : |(1061276371/2500000000 : ℝ)|=(1061276371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4004104019/10000000000 : ℝ)|^4629 ≤ (30874293163853/100000000000000 : ℝ)^3605
        have hw : |(4004104019/10000000000 : ℝ)|=(4004104019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248883347/5000000000 : ℝ)|^4629 ≤ (2240323538313/6250000000000 : ℝ)^3605
        have hw : |(2248883347/5000000000 : ℝ)|=(2248883347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s3_4 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-71634437/400000000 : ℝ)*x 0 + (5219456349/10000000000 : ℝ)*x 1 + (1356732713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71634437/400000000 : ℝ)^4629 ≤ (2746844930711/25000000000000 : ℝ)^3605 := by
    have hnat : (71634437 : ℕ)^4629*25000000000000^3605 ≤ 2746844930711^3605*400000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71634437 400000000 2746844930711 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219456349/10000000000 : ℝ)^4629 ≤ (10848176836679/25000000000000 : ℝ)^3605 := by
    have hnat : (5219456349 : ℕ)^4629*25000000000000^3605 ≤ 10848176836679^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219456349 10000000000 10848176836679 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356732713/2500000000 : ℝ)^4629 ≤ (1824796516587/4000000000000 : ℝ)^3605 := by
    have hnat : (1356732713 : ℕ)^4629*4000000000000^3605 ≤ 1824796516587^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356732713 2500000000 1824796516587 4000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71634437/400000000 : ℝ), (5219456349/10000000000 : ℝ), (1356732713/2500000000 : ℝ)] ![(2746844930711/25000000000000 : ℝ), (10848176836679/25000000000000 : ℝ), (1824796516587/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71634437/400000000 : ℝ)|^4629 ≤ (2746844930711/25000000000000 : ℝ)^3605
        have hw : |(-71634437/400000000 : ℝ)|=(71634437/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219456349/10000000000 : ℝ)|^4629 ≤ (10848176836679/25000000000000 : ℝ)^3605
        have hw : |(5219456349/10000000000 : ℝ)|=(5219456349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356732713/2500000000 : ℝ)|^4629 ≤ (1824796516587/4000000000000 : ℝ)^3605
        have hw : |(1356732713/2500000000 : ℝ)|=(1356732713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s3_5 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293445221/10000000000 : ℝ)*x 0 + (-1689575773/10000000000 : ℝ)*x 1 + (5426930587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293445221/10000000000 : ℝ)^4629 ≤ (5523016674809/12500000000000 : ℝ)^3605 := by
    have hnat : (5293445221 : ℕ)^4629*12500000000000^3605 ≤ 5523016674809^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293445221 10000000000 5523016674809 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1689575773/10000000000 : ℝ)^4629 ≤ (2039191306049/20000000000000 : ℝ)^3605 := by
    have hnat : (1689575773 : ℕ)^4629*20000000000000^3605 ≤ 2039191306049^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689575773 10000000000 2039191306049 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426930587/10000000000 : ℝ)^4629 ≤ (45619910054267/100000000000000 : ℝ)^3605 := by
    have hnat : (5426930587 : ℕ)^4629*100000000000000^3605 ≤ 45619910054267^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426930587 10000000000 45619910054267 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293445221/10000000000 : ℝ), (-1689575773/10000000000 : ℝ), (5426930587/10000000000 : ℝ)] ![(5523016674809/12500000000000 : ℝ), (2039191306049/20000000000000 : ℝ), (45619910054267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293445221/10000000000 : ℝ)|^4629 ≤ (5523016674809/12500000000000 : ℝ)^3605
        have hw : |(5293445221/10000000000 : ℝ)|=(5293445221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1689575773/10000000000 : ℝ)|^4629 ≤ (2039191306049/20000000000000 : ℝ)^3605
        have hw : |(-1689575773/10000000000 : ℝ)|=(1689575773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426930587/10000000000 : ℝ)|^4629 ≤ (45619910054267/100000000000000 : ℝ)^3605
        have hw : |(5426930587/10000000000 : ℝ)|=(5426930587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s3_6 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646722267/5000000000 : ℝ)*x 0 + (67836639/125000000 : ℝ)*x 1 + (-1689575981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646722267/5000000000 : ℝ)^4629 ≤ (44184126035273/100000000000000 : ℝ)^3605 := by
    have hnat : (2646722267 : ℕ)^4629*100000000000000^3605 ≤ 44184126035273^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646722267 5000000000 44184126035273 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67836639/125000000 : ℝ)^4629 ≤ (9123983161493/20000000000000 : ℝ)^3605 := by
    have hnat : (67836639 : ℕ)^4629*20000000000000^3605 ≤ 9123983161493^3605*125000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67836639 125000000 9123983161493 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1689575981/10000000000 : ℝ)^4629 ≤ (10195958141987/100000000000000 : ℝ)^3605 := by
    have hnat : (1689575981 : ℕ)^4629*100000000000000^3605 ≤ 10195958141987^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689575981 10000000000 10195958141987 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646722267/5000000000 : ℝ), (67836639/125000000 : ℝ), (-1689575981/10000000000 : ℝ)] ![(44184126035273/100000000000000 : ℝ), (9123983161493/20000000000000 : ℝ), (10195958141987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646722267/5000000000 : ℝ)|^4629 ≤ (44184126035273/100000000000000 : ℝ)^3605
        have hw : |(2646722267/5000000000 : ℝ)|=(2646722267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67836639/125000000 : ℝ)|^4629 ≤ (9123983161493/20000000000000 : ℝ)^3605
        have hw : |(67836639/125000000 : ℝ)|=(67836639/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1689575981/10000000000 : ℝ)|^4629 ≤ (10195958141987/100000000000000 : ℝ)^3605
        have hw : |(-1689575981/10000000000 : ℝ)|=(1689575981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s3_7 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4245171767/10000000000 : ℝ)*x 0 + (140473641/312500000 : ℝ)*x 1 + (4006733979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245171767/10000000000 : ℝ)^4629 ≤ (6656239489839/20000000000000 : ℝ)^3605 := by
    have hnat : (4245171767 : ℕ)^4629*20000000000000^3605 ≤ 6656239489839^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245171767 10000000000 6656239489839 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140473641/312500000 : ℝ)^4629 ≤ (4477308504877/12500000000000 : ℝ)^3605 := by
    have hnat : (140473641 : ℕ)^4629*12500000000000^3605 ≤ 4477308504877^3605*312500000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140473641 312500000 4477308504877 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4006733979/10000000000 : ℝ)^4629 ≤ (30900334498113/100000000000000 : ℝ)^3605 := by
    have hnat : (4006733979 : ℕ)^4629*100000000000000^3605 ≤ 30900334498113^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006733979 10000000000 30900334498113 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245171767/10000000000 : ℝ), (140473641/312500000 : ℝ), (4006733979/10000000000 : ℝ)] ![(6656239489839/20000000000000 : ℝ), (4477308504877/12500000000000 : ℝ), (30900334498113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245171767/10000000000 : ℝ)|^4629 ≤ (6656239489839/20000000000000 : ℝ)^3605
        have hw : |(4245171767/10000000000 : ℝ)|=(4245171767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140473641/312500000 : ℝ)|^4629 ≤ (4477308504877/12500000000000 : ℝ)^3605
        have hw : |(140473641/312500000 : ℝ)|=(140473641/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4006733979/10000000000 : ℝ)|^4629 ≤ (30900334498113/100000000000000 : ℝ)^3605
        have hw : |(4006733979/10000000000 : ℝ)|=(4006733979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1566_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7911/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5537/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15521/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7911/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7911/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7911/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7911/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7911/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7911/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10797/100000 : ℝ) ^ (4627/1024 : ℝ) ≤ (856953373908979/20000000000000000000 : ℝ) := by
    have hpowers : (10797/100000 : ℝ)^4627 ≤ (856953373908979/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10797 : ℕ)^4627*20000000000000000000^1024 ≤ 856953373908979^1024*100000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10797 100000 856953373908979 20000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10797/100000 : ℝ)) (X := (856953373908979/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7911/50000 : ℝ) ^ (4627/1024 : ℝ) ≤ (1505562445611587/6250000000000000000 : ℝ) := by
    have hpowers : (7911/50000 : ℝ)^4627 ≤ (1505562445611587/6250000000000000000 : ℝ)^1024 := by
      have hnat : (7911 : ℕ)^4627*6250000000000000000^1024 ≤ 1505562445611587^1024*50000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7911 50000 1505562445611587 6250000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7911/50000 : ℝ)) (X := (1505562445611587/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000856953373908979/10000000000000000000 : ℝ) ≤ (5000094822885007/5000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (10000856953373908979/10000000000000000000 : ℝ)^1024 ≤ (5000094822885007/5000000000000000 : ℝ)^4627 := by
      have hnat : (10000856953373908979 : ℕ)^1024*5000000000000000^4627 ≤ 5000094822885007^4627*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000856953373908979 10000000000000000000 5000094822885007 5000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000094822885007/5000000000000000 : ℝ)) (X := (10000856953373908979/10000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028373765999330287/100000000000000000000 : ℝ) ≤ (5000313934808643/5000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (100028373765999330287/100000000000000000000 : ℝ)^1024 ≤ (5000313934808643/5000000000000000 : ℝ)^4627 := by
      have hnat : (100028373765999330287 : ℕ)^1024*5000000000000000^4627 ≤ 5000313934808643^4627*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028373765999330287 100000000000000000000 5000313934808643 5000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000313934808643/5000000000000000 : ℝ)) (X := (100028373765999330287/100000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126505562445611587/3125000000000000000 : ℝ) ≤ (5000533046732279/5000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (3126505562445611587/3125000000000000000 : ℝ)^1024 ≤ (5000533046732279/5000000000000000 : ℝ)^4627 := by
      have hnat : (3126505562445611587 : ℕ)^1024*5000000000000000^4627 ≤ 5000533046732279^4627*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126505562445611587 3125000000000000000 5000533046732279 5000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000533046732279/5000000000000000 : ℝ)) (X := (3126505562445611587/3125000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(856953373908979/20000000000000000000 : ℝ) ≤ ((8373581660706054797/8375000000000000000 : ℝ)+2*(54777980909/62812500000000 : ℝ)*(10797/100000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (8373581660706054797/8375000000000000000 : ℝ)+2*(54777980909/62812500000000 : ℝ)*(10797/100000 : ℝ)=(5000094822885007/5000000000000000 : ℝ) by norm_num, show 1+2*(856953373908979/20000000000000000000 : ℝ)=(10000856953373908979/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1505562445611587/6250000000000000000 : ℝ)+(856953373908979/20000000000000000000 : ℝ) ≤ ((8373581660706054797/8375000000000000000 : ℝ)+(54777980909/62812500000000 : ℝ)*((7911/50000 : ℝ)+(10797/100000 : ℝ)))^(4627/1024 : ℝ) := by
    rw [show (8373581660706054797/8375000000000000000 : ℝ)+(54777980909/62812500000000 : ℝ)*((7911/50000 : ℝ)+(10797/100000 : ℝ))=(5000313934808643/5000000000000000 : ℝ) by norm_num, show 1+(1505562445611587/6250000000000000000 : ℝ)+(856953373908979/20000000000000000000 : ℝ)=(100028373765999330287/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1505562445611587/6250000000000000000 : ℝ) ≤ ((8373581660706054797/8375000000000000000 : ℝ)+2*(54777980909/62812500000000 : ℝ)*(7911/50000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (8373581660706054797/8375000000000000000 : ℝ)+2*(54777980909/62812500000000 : ℝ)*(7911/50000 : ℝ)=(5000533046732279/5000000000000000 : ℝ) by norm_num, show 1+2*(1505562445611587/6250000000000000000 : ℝ)=(3126505562445611587/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8373581660706054797/8375000000000000000 : ℝ)*(X 1 0+X 2 0)+(54777980909/62812500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (7911/50000 : ℝ)) (c := (8373581660706054797/8375000000000000000 : ℝ)) (alpha := (54777980909/62812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8373581660706054797/8375000000000000000 : ℝ)*(X 0 1+X 2 1)+(54777980909/62812500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (7911/50000 : ℝ)) (c := (8373581660706054797/8375000000000000000 : ℝ)) (alpha := (54777980909/62812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8373581660706054797/8375000000000000000 : ℝ)*(X 0 2+X 1 2)+(54777980909/62812500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (7911/50000 : ℝ)) (c := (8373581660706054797/8375000000000000000 : ℝ)) (alpha := (54777980909/62812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1790832613/10000000000 : ℝ)*X 0 0+(2714024047/5000000000 : ℝ)*X 0 1+(1043669499/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668612373/1250000000 : ℝ)*X 1 0+(-474539839/2500000000 : ℝ)*X 1 1+(1043669499/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668612373/1250000000 : ℝ)*X 2 0+(652293437/1250000000 : ℝ)*X 2 1+(-474539839/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061276371/2500000000 : ℝ)*X 0 0+(4004104019/10000000000 : ℝ)*X 0 1+(2248883347/5000000000 : ℝ)*X 0 2+(1061276371/2500000000 : ℝ)*X 1 0+(4004104019/10000000000 : ℝ)*X 1 1+(2248883347/5000000000 : ℝ)*X 1 2+(1061276371/2500000000 : ℝ)*X 2 0+(4004104019/10000000000 : ℝ)*X 2 1+(2248883347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-71634437/400000000 : ℝ)*X 0 0+(5219456349/10000000000 : ℝ)*X 0 1+(1356732713/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293445221/10000000000 : ℝ)*X 1 0+(-1689575773/10000000000 : ℝ)*X 1 1+(5426930587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646722267/5000000000 : ℝ)*X 2 0+(67836639/125000000 : ℝ)*X 2 1+(-1689575981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4245171767/10000000000 : ℝ)*X 0 0+(140473641/312500000 : ℝ)*X 0 1+(4006733979/10000000000 : ℝ)*X 0 2+(4245171767/10000000000 : ℝ)*X 1 0+(140473641/312500000 : ℝ)*X 1 1+(4006733979/10000000000 : ℝ)*X 1 2+(4245171767/10000000000 : ℝ)*X 2 0+(140473641/312500000 : ℝ)*X 2 1+(4006733979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5212681122525145413502009769/418750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1057764373/50000000000000 : ℝ)*(base19) + (1976273153/100000000000000 : ℝ)*(base23) + (7448641/10000000000000 : ℝ)*(lower2) + (307972779/100000000000000 : ℝ)*(upper3) + (207589139/100000000000000 : ℝ)*(upper5) + (3397238418519253/100000000000000 : ℝ)*(major0) + (3397238418519253/100000000000000 : ℝ)*(major1) + (3397238418519253/100000000000000 : ℝ)*(major2) + (476873860205169/10000000000000 : ℝ)*(sp0) + (4768770218818887/100000000000000 : ℝ)*(sp1) + (4768770358074479/100000000000000 : ℝ)*(sp2) + (506422142889239/25000000000000 : ℝ)*(sp3) + (33732295943/100000000000000 : ℝ)*(sp4) + (3879048529/25000000000000 : ℝ)*(sp7) + (63303252742221/3125000000000 : ℝ)*(f.failure) + (298048270896727/6250000000000 : ℝ)*(f.sum) + (87832380698941/25125000000000000000000000000 : ℝ)*base65 + (36076003060994180077/2512500000000000000000000000000000 : ℝ)*base68 + (24240320294631680077/2512500000000000000000000000000000 : ℝ)*base70 + (21621640713006680077/2512500000000000000000000000000000 : ℝ)*base72 + (14528343458773/3140625000000000000000000000 : ℝ)*base74 + (50877815343119180077/2512500000000000000000000000000000 : ℝ)*base76 + (7966501014606680077/2512500000000000000000000000000000 : ℝ)*base78 + (22103698148706680077/2512500000000000000000000000000000 : ℝ)*base80 + (9274965751273/3140625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4880329/312500000000000000000 : ℝ)*base89 + (4880329/312500000000000000000 : ℝ)*base91 + (4880329/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (432942591563070793323199791/104687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (597887783/50000000000000 : ℝ)*(base19) + (313123443/50000000000000 : ℝ)*(base23) + (25156129/50000000000000 : ℝ)*(upper2) + (14928919/12500000000000 : ℝ)*(upper3) + (7128499/12500000000000 : ℝ)*(upper5) + (858408668593533/25000000000000 : ℝ)*(major0) + (858408668593533/25000000000000 : ℝ)*(major1) + (858408668593533/25000000000000 : ℝ)*(major2) + (1795919489/12500000000000 : ℝ)*(sp1) + (10640765487/100000000000000 : ℝ)*(sp2) + (301241423559393/6250000000000 : ℝ)*(sp4) + (4819847213818811/100000000000000 : ℝ)*(sp5) + (963970301987583/20000000000000 : ℝ)*(sp6) + (2047406433945601/100000000000000 : ℝ)*(sp7) + (2047406433945601/100000000000000 : ℝ)*(f.failure) + (301241423559393/6250000000000 : ℝ)*(f.sum) + (42342184142657/8375000000000000000000000000 : ℝ)*base66 + (1870310684767427801/209375000000000000000000000000000 : ℝ)*base67 + (1025800907964302801/209375000000000000000000000000000 : ℝ)*base69 + (93929136036177801/209375000000000000000000000000000 : ℝ)*base71 + (19343253833593/8375000000000000000000000000 : ℝ)*base73 + (2023885854504927801/209375000000000000000000000000000 : ℝ)*base75 + (1240963654808052801/209375000000000000000000000000000 : ℝ)*base77 + (5381088315142427801/209375000000000000000000000000000 : ℝ)*base79 + (1205521584629/1046875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2559051/10000000000000000000000 : ℝ)*base90 + (2559051/10000000000000000000000 : ℝ)*base92 + (2559051/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1566_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7911/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15521/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1566_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1566_s4_0 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1791068913/10000000000 : ℝ)*x 0 + (1356617547/2500000000 : ℝ)*x 1 + (2609884321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1791068913/10000000000 : ℝ)^4629 ≤ (439560730903/4000000000000 : ℝ)^3605 := by
    have hnat : (1791068913 : ℕ)^4629*4000000000000^3605 ≤ 439560730903^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791068913 10000000000 439560730903 4000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356617547/2500000000 : ℝ)^4629 ≤ (45614940571277/100000000000000 : ℝ)^3605 := by
    have hnat : (1356617547 : ℕ)^4629*100000000000000^3605 ≤ 45614940571277^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356617547 2500000000 45614940571277 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609884321/5000000000 : ℝ)^4629 ≤ (21698020572541/50000000000000 : ℝ)^3605 := by
    have hnat : (2609884321 : ℕ)^4629*50000000000000^3605 ≤ 21698020572541^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609884321 5000000000 21698020572541 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1791068913/10000000000 : ℝ), (1356617547/2500000000 : ℝ), (2609884321/5000000000 : ℝ)] ![(439560730903/4000000000000 : ℝ), (45614940571277/100000000000000 : ℝ), (21698020572541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1791068913/10000000000 : ℝ)|^4629 ≤ (439560730903/4000000000000 : ℝ)^3605
        have hw : |(-1791068913/10000000000 : ℝ)|=(1791068913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356617547/2500000000 : ℝ)|^4629 ≤ (45614940571277/100000000000000 : ℝ)^3605
        have hw : |(1356617547/2500000000 : ℝ)|=(1356617547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609884321/5000000000 : ℝ)|^4629 ≤ (21698020572541/50000000000000 : ℝ)^3605
        have hw : |(2609884321/5000000000 : ℝ)|=(2609884321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s4_1 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348481151/10000000000 : ℝ)*x 0 + (-1896825881/10000000000 : ℝ)*x 1 + (5219768643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348481151/10000000000 : ℝ)^4629 ≤ (44774872037801/100000000000000 : ℝ)^3605 := by
    have hnat : (5348481151 : ℕ)^4629*100000000000000^3605 ≤ 44774872037801^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348481151 10000000000 44774872037801 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896825881/10000000000 : ℝ)^4629 ≤ (5914543401039/50000000000000 : ℝ)^3605 := by
    have hnat : (1896825881 : ℕ)^4629*50000000000000^3605 ≤ 5914543401039^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896825881 10000000000 5914543401039 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219768643/10000000000 : ℝ)^4629 ≤ (43396041155757/100000000000000 : ℝ)^3605 := by
    have hnat : (5219768643 : ℕ)^4629*100000000000000^3605 ≤ 43396041155757^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219768643 10000000000 43396041155757 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348481151/10000000000 : ℝ), (-1896825881/10000000000 : ℝ), (5219768643/10000000000 : ℝ)] ![(44774872037801/100000000000000 : ℝ), (5914543401039/50000000000000 : ℝ), (43396041155757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348481151/10000000000 : ℝ)|^4629 ≤ (44774872037801/100000000000000 : ℝ)^3605
        have hw : |(5348481151/10000000000 : ℝ)|=(5348481151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1896825881/10000000000 : ℝ)|^4629 ≤ (5914543401039/50000000000000 : ℝ)^3605
        have hw : |(-1896825881/10000000000 : ℝ)|=(1896825881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219768643/10000000000 : ℝ)|^4629 ≤ (43396041155757/100000000000000 : ℝ)^3605
        have hw : |(5219768643/10000000000 : ℝ)|=(5219768643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s4_2 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41785009/78125000 : ℝ)*x 0 + (2609884321/5000000000 : ℝ)*x 1 + (-47420647/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41785009/78125000 : ℝ)^4629 ≤ (895497440971/2000000000000 : ℝ)^3605 := by
    have hnat : (41785009 : ℕ)^4629*2000000000000^3605 ≤ 895497440971^3605*78125000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41785009 78125000 895497440971 2000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609884321/5000000000 : ℝ)^4629 ≤ (21698020572541/50000000000000 : ℝ)^3605 := by
    have hnat : (2609884321 : ℕ)^4629*50000000000000^3605 ≤ 21698020572541^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609884321 5000000000 21698020572541 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47420647/250000000 : ℝ)^4629 ≤ (1182908679407/10000000000000 : ℝ)^3605 := by
    have hnat : (47420647 : ℕ)^4629*10000000000000^3605 ≤ 1182908679407^3605*250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47420647 250000000 1182908679407 10000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41785009/78125000 : ℝ), (2609884321/5000000000 : ℝ), (-47420647/250000000 : ℝ)] ![(895497440971/2000000000000 : ℝ), (21698020572541/50000000000000 : ℝ), (1182908679407/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41785009/78125000 : ℝ)|^4629 ≤ (895497440971/2000000000000 : ℝ)^3605
        have hw : |(41785009/78125000 : ℝ)|=(41785009/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609884321/5000000000 : ℝ)|^4629 ≤ (21698020572541/50000000000000 : ℝ)^3605
        have hw : |(2609884321/5000000000 : ℝ)|=(2609884321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47420647/250000000 : ℝ)|^4629 ≤ (1182908679407/10000000000000 : ℝ)^3605
        have hw : |(-47420647/250000000 : ℝ)|=(47420647/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s4_3 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849050863/2000000000 : ℝ)*x 0 + (2003808777/5000000000 : ℝ)*x 1 + (4494220067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849050863/2000000000 : ℝ)^4629 ≤ (33282028434499/100000000000000 : ℝ)^3605 := by
    have hnat : (849050863 : ℕ)^4629*100000000000000^3605 ≤ 33282028434499^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849050863 2000000000 33282028434499 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003808777/5000000000 : ℝ)^4629 ≤ (30909084569653/100000000000000 : ℝ)^3605 := by
    have hnat : (2003808777 : ℕ)^4629*100000000000000^3605 ≤ 30909084569653^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003808777 5000000000 30909084569653 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494220067/10000000000 : ℝ)^4629 ≤ (35808886979763/100000000000000 : ℝ)^3605 := by
    have hnat : (4494220067 : ℕ)^4629*100000000000000^3605 ≤ 35808886979763^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494220067 10000000000 35808886979763 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849050863/2000000000 : ℝ), (2003808777/5000000000 : ℝ), (4494220067/10000000000 : ℝ)] ![(33282028434499/100000000000000 : ℝ), (30909084569653/100000000000000 : ℝ), (35808886979763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849050863/2000000000 : ℝ)|^4629 ≤ (33282028434499/100000000000000 : ℝ)^3605
        have hw : |(849050863/2000000000 : ℝ)|=(849050863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003808777/5000000000 : ℝ)|^4629 ≤ (30909084569653/100000000000000 : ℝ)^3605
        have hw : |(2003808777/5000000000 : ℝ)|=(2003808777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494220067/10000000000 : ℝ)|^4629 ≤ (35808886979763/100000000000000 : ℝ)^3605
        have hw : |(4494220067/10000000000 : ℝ)|=(4494220067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s4_4 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1791095987/10000000000 : ℝ)*x 0 + (2610423031/5000000000 : ℝ)*x 1 + (1085076953/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1791095987/10000000000 : ℝ)^4629 ≤ (10989231568161/100000000000000 : ℝ)^3605 := by
    have hnat : (1791095987 : ℕ)^4629*100000000000000^3605 ≤ 10989231568161^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791095987 10000000000 10989231568161 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610423031/5000000000 : ℝ)^4629 ≤ (21703771641011/50000000000000 : ℝ)^3605 := by
    have hnat : (2610423031 : ℕ)^4629*50000000000000^3605 ≤ 21703771641011^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610423031 5000000000 21703771641011 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085076953/2000000000 : ℝ)^4629 ≤ (22801612569939/50000000000000 : ℝ)^3605 := by
    have hnat : (1085076953 : ℕ)^4629*50000000000000^3605 ≤ 22801612569939^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085076953 2000000000 22801612569939 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1791095987/10000000000 : ℝ), (2610423031/5000000000 : ℝ), (1085076953/2000000000 : ℝ)] ![(10989231568161/100000000000000 : ℝ), (21703771641011/50000000000000 : ℝ), (22801612569939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1791095987/10000000000 : ℝ)|^4629 ≤ (10989231568161/100000000000000 : ℝ)^3605
        have hw : |(-1791095987/10000000000 : ℝ)|=(1791095987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610423031/5000000000 : ℝ)|^4629 ≤ (21703771641011/50000000000000 : ℝ)^3605
        have hw : |(2610423031/5000000000 : ℝ)|=(2610423031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085076953/2000000000 : ℝ)|^4629 ≤ (22801612569939/50000000000000 : ℝ)^3605
        have hw : |(1085076953/2000000000 : ℝ)|=(1085076953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s4_5 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529382047/1000000000 : ℝ)*x 0 + (-1691209753/10000000000 : ℝ)*x 1 + (5425384759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529382047/1000000000 : ℝ)^4629 ≤ (44188155321419/100000000000000 : ℝ)^3605 := by
    have hnat : (529382047 : ℕ)^4629*100000000000000^3605 ≤ 44188155321419^3605*1000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529382047 1000000000 44188155321419 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1691209753/10000000000 : ℝ)^4629 ≤ (5104309793933/50000000000000 : ℝ)^3605 := by
    have hnat : (1691209753 : ℕ)^4629*50000000000000^3605 ≤ 5104309793933^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691209753 10000000000 5104309793933 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425384759/10000000000 : ℝ)^4629 ≤ (45603225075119/100000000000000 : ℝ)^3605 := by
    have hnat : (5425384759 : ℕ)^4629*100000000000000^3605 ≤ 45603225075119^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425384759 10000000000 45603225075119 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529382047/1000000000 : ℝ), (-1691209753/10000000000 : ℝ), (5425384759/10000000000 : ℝ)] ![(44188155321419/100000000000000 : ℝ), (5104309793933/50000000000000 : ℝ), (45603225075119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529382047/1000000000 : ℝ)|^4629 ≤ (44188155321419/100000000000000 : ℝ)^3605
        have hw : |(529382047/1000000000 : ℝ)|=(529382047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1691209753/10000000000 : ℝ)|^4629 ≤ (5104309793933/50000000000000 : ℝ)^3605
        have hw : |(-1691209753/10000000000 : ℝ)|=(1691209753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425384759/10000000000 : ℝ)|^4629 ≤ (45603225075119/100000000000000 : ℝ)^3605
        have hw : |(5425384759/10000000000 : ℝ)|=(5425384759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s4_6 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646910243/5000000000 : ℝ)*x 0 + (1085076947/2000000000 : ℝ)*x 1 + (-338241953/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646910243/5000000000 : ℝ)^4629 ≤ (44188155492909/100000000000000 : ℝ)^3605 := by
    have hnat : (2646910243 : ℕ)^4629*100000000000000^3605 ≤ 44188155492909^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646910243 5000000000 44188155492909 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085076947/2000000000 : ℝ)^4629 ≤ (11400806204021/25000000000000 : ℝ)^3605 := by
    have hnat : (1085076947 : ℕ)^4629*25000000000000^3605 ≤ 11400806204021^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085076947 2000000000 11400806204021 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338241953/2000000000 : ℝ)^4629 ≤ (10208619680877/100000000000000 : ℝ)^3605 := by
    have hnat : (338241953 : ℕ)^4629*100000000000000^3605 ≤ 10208619680877^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338241953 2000000000 10208619680877 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646910243/5000000000 : ℝ), (1085076947/2000000000 : ℝ), (-338241953/2000000000 : ℝ)] ![(44188155492909/100000000000000 : ℝ), (11400806204021/25000000000000 : ℝ), (10208619680877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646910243/5000000000 : ℝ)|^4629 ≤ (44188155492909/100000000000000 : ℝ)^3605
        have hw : |(2646910243/5000000000 : ℝ)|=(2646910243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085076947/2000000000 : ℝ)|^4629 ≤ (11400806204021/25000000000000 : ℝ)^3605
        have hw : |(1085076947/2000000000 : ℝ)|=(1085076947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-338241953/2000000000 : ℝ)|^4629 ≤ (10208619680877/100000000000000 : ℝ)^3605
        have hw : |(-338241953/2000000000 : ℝ)|=(338241953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s4_7 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2122658987/5000000000 : ℝ)*x 0 + (4491683551/10000000000 : ℝ)*x 1 + (4010172843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122658987/5000000000 : ℝ)^4629 ≤ (33282669273189/100000000000000 : ℝ)^3605 := by
    have hnat : (2122658987 : ℕ)^4629*100000000000000^3605 ≤ 33282669273189^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122658987 5000000000 33282669273189 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491683551/10000000000 : ℝ)^4629 ≤ (17891468973113/50000000000000 : ℝ)^3605 := by
    have hnat : (4491683551 : ℕ)^4629*50000000000000^3605 ≤ 17891468973113^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491683551 10000000000 17891468973113 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4010172843/10000000000 : ℝ)^4629 ≤ (15467196381103/50000000000000 : ℝ)^3605 := by
    have hnat : (4010172843 : ℕ)^4629*50000000000000^3605 ≤ 15467196381103^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010172843 10000000000 15467196381103 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122658987/5000000000 : ℝ), (4491683551/10000000000 : ℝ), (4010172843/10000000000 : ℝ)] ![(33282669273189/100000000000000 : ℝ), (17891468973113/50000000000000 : ℝ), (15467196381103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122658987/5000000000 : ℝ)|^4629 ≤ (33282669273189/100000000000000 : ℝ)^3605
        have hw : |(2122658987/5000000000 : ℝ)|=(2122658987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491683551/10000000000 : ℝ)|^4629 ≤ (17891468973113/50000000000000 : ℝ)^3605
        have hw : |(4491683551/10000000000 : ℝ)|=(4491683551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4010172843/10000000000 : ℝ)|^4629 ≤ (15467196381103/50000000000000 : ℝ)^3605
        have hw : |(4010172843/10000000000 : ℝ)|=(4010172843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1566_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15521/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2221/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15521/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15521/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15521/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15521/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15521/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15521/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5537/50000 : ℝ) ^ (4627/1024 : ℝ) ≤ (960876785234999/20000000000000000000 : ℝ) := by
    have hpowers : (5537/50000 : ℝ)^4627 ≤ (960876785234999/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5537 : ℕ)^4627*20000000000000000000^1024 ≤ 960876785234999^1024*50000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5537 50000 960876785234999 20000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5537/50000 : ℝ)) (X := (960876785234999/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15521/100000 : ℝ) ^ (4627/1024 : ℝ) ≤ (1380404703160561/6250000000000000000 : ℝ) := by
    have hpowers : (15521/100000 : ℝ)^4627 ≤ (1380404703160561/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15521 : ℕ)^4627*6250000000000000000^1024 ≤ 1380404703160561^1024*100000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15521 100000 1380404703160561 6250000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15521/100000 : ℝ)) (X := (1380404703160561/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000960876785234999/10000000000000000000 : ℝ) ≤ (2500053160850433/2500000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (10000960876785234999/10000000000000000000 : ℝ)^1024 ≤ (2500053160850433/2500000000000000 : ℝ)^4627 := by
      have hnat : (10000960876785234999 : ℕ)^1024*2500000000000000^4627 ≤ 2500053160850433^4627*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000960876785234999 10000000000000000000 2500053160850433 2500000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500053160850433/2500000000000000 : ℝ)) (X := (10000960876785234999/10000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026890859176743971/100000000000000000000 : ℝ) ≤ (1250074382313757/1250000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (100026890859176743971/100000000000000000000 : ℝ)^1024 ≤ (1250074382313757/1250000000000000 : ℝ)^4627 := by
      have hnat : (100026890859176743971 : ℕ)^1024*1250000000000000^4627 ≤ 1250074382313757^4627*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026890859176743971 100000000000000000000 1250074382313757 1250000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250074382313757/1250000000000000 : ℝ)) (X := (100026890859176743971/100000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126380404703160561/3125000000000000000 : ℝ) ≤ (500048873680919/500000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (3126380404703160561/3125000000000000000 : ℝ)^1024 ≤ (500048873680919/500000000000000 : ℝ)^4627 := by
      have hnat : (3126380404703160561 : ℕ)^1024*500000000000000^4627 ≤ 500048873680919^4627*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126380404703160561 3125000000000000000 500048873680919 500000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500048873680919/500000000000000 : ℝ)) (X := (3126380404703160561/3125000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(960876785234999/20000000000000000000 : ℝ) ≤ ((11115618973847085563/11117500000000000000 : ℝ)+2*(95603777081/111175000000000 : ℝ)*(5537/50000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (11115618973847085563/11117500000000000000 : ℝ)+2*(95603777081/111175000000000 : ℝ)*(5537/50000 : ℝ)=(2500053160850433/2500000000000000 : ℝ) by norm_num, show 1+2*(960876785234999/20000000000000000000 : ℝ)=(10000960876785234999/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1380404703160561/6250000000000000000 : ℝ)+(960876785234999/20000000000000000000 : ℝ) ≤ ((11115618973847085563/11117500000000000000 : ℝ)+(95603777081/111175000000000 : ℝ)*((15521/100000 : ℝ)+(5537/50000 : ℝ)))^(4627/1024 : ℝ) := by
    rw [show (11115618973847085563/11117500000000000000 : ℝ)+(95603777081/111175000000000 : ℝ)*((15521/100000 : ℝ)+(5537/50000 : ℝ))=(1250074382313757/1250000000000000 : ℝ) by norm_num, show 1+(1380404703160561/6250000000000000000 : ℝ)+(960876785234999/20000000000000000000 : ℝ)=(100026890859176743971/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1380404703160561/6250000000000000000 : ℝ) ≤ ((11115618973847085563/11117500000000000000 : ℝ)+2*(95603777081/111175000000000 : ℝ)*(15521/100000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (11115618973847085563/11117500000000000000 : ℝ)+2*(95603777081/111175000000000 : ℝ)*(15521/100000 : ℝ)=(500048873680919/500000000000000 : ℝ) by norm_num, show 1+2*(1380404703160561/6250000000000000000 : ℝ)=(3126380404703160561/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11115618973847085563/11117500000000000000 : ℝ)*(X 1 0+X 2 0)+(95603777081/111175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (15521/100000 : ℝ)) (c := (11115618973847085563/11117500000000000000 : ℝ)) (alpha := (95603777081/111175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11115618973847085563/11117500000000000000 : ℝ)*(X 0 1+X 2 1)+(95603777081/111175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (15521/100000 : ℝ)) (c := (11115618973847085563/11117500000000000000 : ℝ)) (alpha := (95603777081/111175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11115618973847085563/11117500000000000000 : ℝ)*(X 0 2+X 1 2)+(95603777081/111175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (15521/100000 : ℝ)) (c := (11115618973847085563/11117500000000000000 : ℝ)) (alpha := (95603777081/111175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1791068913/10000000000 : ℝ)*X 0 0+(1356617547/2500000000 : ℝ)*X 0 1+(2609884321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348481151/10000000000 : ℝ)*X 1 0+(-1896825881/10000000000 : ℝ)*X 1 1+(5219768643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41785009/78125000 : ℝ)*X 2 0+(2609884321/5000000000 : ℝ)*X 2 1+(-47420647/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((849050863/2000000000 : ℝ)*X 0 0+(2003808777/5000000000 : ℝ)*X 0 1+(4494220067/10000000000 : ℝ)*X 0 2+(849050863/2000000000 : ℝ)*X 1 0+(2003808777/5000000000 : ℝ)*X 1 1+(4494220067/10000000000 : ℝ)*X 1 2+(849050863/2000000000 : ℝ)*X 2 0+(2003808777/5000000000 : ℝ)*X 2 1+(4494220067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1791095987/10000000000 : ℝ)*X 0 0+(2610423031/5000000000 : ℝ)*X 0 1+(1085076953/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529382047/1000000000 : ℝ)*X 1 0+(-1691209753/10000000000 : ℝ)*X 1 1+(5425384759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646910243/5000000000 : ℝ)*X 2 0+(1085076947/2000000000 : ℝ)*X 2 1+(-338241953/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2122658987/5000000000 : ℝ)*X 0 0+(4491683551/10000000000 : ℝ)*X 0 1+(4010172843/10000000000 : ℝ)*X 0 2+(2122658987/5000000000 : ℝ)*X 1 0+(4491683551/10000000000 : ℝ)*X 1 1+(4010172843/10000000000 : ℝ)*X 1 2+(2122658987/5000000000 : ℝ)*X 2 0+(4491683551/10000000000 : ℝ)*X 2 1+(4010172843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (469584872551705708751382549/69484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1145244189/100000000000000 : ℝ)*(base19) + (214028749/20000000000000 : ℝ)*(base23) + (40651123/100000000000000 : ℝ)*(lower2) + (166636953/100000000000000 : ℝ)*(upper3) + (112607797/100000000000000 : ℝ)*(upper5) + (107703323592279/3125000000000 : ℝ)*(major0) + (107703323592279/3125000000000 : ℝ)*(major1) + (107703323592279/3125000000000 : ℝ)*(major2) + (24189561927049/500000000000 : ℝ)*(sp0) + (4837929784434047/100000000000000 : ℝ)*(sp1) + (4837929859534491/100000000000000 : ℝ)*(sp2) + (2055073031429837/100000000000000 : ℝ)*(sp3) + (3708853687/20000000000000 : ℝ)*(sp4) + (852352657/10000000000000 : ℝ)*(sp7) + (2055081554956407/100000000000000 : ℝ)*(f.failure) + (1209482732419559/25000000000000 : ℝ)*(f.sum) + (56317751404239/11117500000000000000000000000 : ℝ)*base66 + (23522350730448101/17371093750000000000000000000000 : ℝ)*base67 + (290849467459161827/34742187500000000000000000000000 : ℝ)*base69 + (74209347397838173/34742187500000000000000000000000 : ℝ)*base72 + (20740254984163/22235000000000000000000000000 : ℝ)*base74 + (34423478001520649/17371093750000000000000000000000 : ℝ)*base76 + (775533629704191971/69484375000000000000000000000000 : ℝ)*base78 + (4519583079516253/2171386718750000000000000000000 : ℝ)*base80 + (39391808905057/22235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (63409443/10000000000000000000000 : ℝ)*base89 + (63409443/10000000000000000000000 : ℝ)*base91 + (63409443/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47394793295409755572251651/11117500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151095127/20000000000000 : ℝ)*(base19) + (781277031/100000000000000 : ℝ)*(base23) + (40629551/50000000000000 : ℝ)*(upper3) + (9816777/100000000000000 : ℝ)*(lower4) + (28430811/25000000000000 : ℝ)*(upper5) + (139316957533059/4000000000000 : ℝ)*(major0) + (139316957533059/4000000000000 : ℝ)*(major1) + (139316957533059/4000000000000 : ℝ)*(major2) + (3178356191/25000000000000 : ℝ)*(sp1) + (5992607583/50000000000000 : ℝ)*(sp2) + (611131389529283/12500000000000 : ℝ)*(sp4) + (977807529466773/20000000000000 : ℝ)*(sp5) + (1222259587435517/25000000000000 : ℝ)*(sp6) + (1038398309158003/50000000000000 : ℝ)*(sp7) + (1038398309158003/50000000000000 : ℝ)*(f.failure) + (611131389529283/12500000000000 : ℝ)*(f.sum) + (1450559435349/555875000000000000000000000 : ℝ)*base66 + (473949868470752783/44470000000000000000000000000000 : ℝ)*base68 + (333314709458432783/44470000000000000000000000000000 : ℝ)*base70 + (436544650173767217/44470000000000000000000000000000 : ℝ)*base71 + (42520560242439/4447000000000000000000000000 : ℝ)*base74 + (615514695735122783/44470000000000000000000000000000 : ℝ)*base76 + (9850384622252783/44470000000000000000000000000000 : ℝ)*base78 + (765241184013232783/44470000000000000000000000000000 : ℝ)*base80 + (9586282721323/2223500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (28861647/5000000000000000000000 : ℝ)*base89 + (28861647/5000000000000000000000 : ℝ)*base91 + (28861647/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1566_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15521/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1566_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1566_s5_0 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1791092433/10000000000 : ℝ)*x 0 + (84786051/156250000 : ℝ)*x 1 + (2609958007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1791092433/10000000000 : ℝ)^4629 ≤ (2747300892207/25000000000000 : ℝ)^3605 := by
    have hnat : (1791092433 : ℕ)^4629*25000000000000^3605 ≤ 2747300892207^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791092433 10000000000 2747300892207 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84786051/156250000 : ℝ)^4629 ≤ (45613182020893/100000000000000 : ℝ)^3605 := by
    have hnat : (84786051 : ℕ)^4629*100000000000000^3605 ≤ 45613182020893^3605*156250000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84786051 156250000 45613182020893 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609958007/5000000000 : ℝ)^4629 ≤ (43397614394171/100000000000000 : ℝ)^3605 := by
    have hnat : (2609958007 : ℕ)^4629*100000000000000^3605 ≤ 43397614394171^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609958007 5000000000 43397614394171 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1791092433/10000000000 : ℝ), (84786051/156250000 : ℝ), (2609958007/5000000000 : ℝ)] ![(2747300892207/25000000000000 : ℝ), (45613182020893/100000000000000 : ℝ), (43397614394171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1791092433/10000000000 : ℝ)|^4629 ≤ (2747300892207/25000000000000 : ℝ)^3605
        have hw : |(-1791092433/10000000000 : ℝ)|=(1791092433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84786051/156250000 : ℝ)|^4629 ≤ (45613182020893/100000000000000 : ℝ)^3605
        have hw : |(84786051/156250000 : ℝ)|=(84786051/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609958007/5000000000 : ℝ)|^4629 ≤ (43397614394171/100000000000000 : ℝ)^3605
        have hw : |(2609958007/5000000000 : ℝ)|=(2609958007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s5_1 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674219077/5000000000 : ℝ)*x 0 + (-948343527/5000000000 : ℝ)*x 1 + (5219916071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674219077/5000000000 : ℝ)^4629 ≤ (1399200307647/3125000000000 : ℝ)^3605 := by
    have hnat : (2674219077 : ℕ)^4629*3125000000000^3605 ≤ 1399200307647^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674219077 5000000000 1399200307647 3125000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948343527/5000000000 : ℝ)^4629 ≤ (295699378353/2500000000000 : ℝ)^3605 := by
    have hnat : (948343527 : ℕ)^4629*2500000000000^3605 ≤ 295699378353^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948343527 5000000000 295699378353 2500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219916071/10000000000 : ℝ)^4629 ≤ (43397615002669/100000000000000 : ℝ)^3605 := by
    have hnat : (5219916071 : ℕ)^4629*100000000000000^3605 ≤ 43397615002669^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219916071 10000000000 43397615002669 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674219077/5000000000 : ℝ), (-948343527/5000000000 : ℝ), (5219916071/10000000000 : ℝ)] ![(1399200307647/3125000000000 : ℝ), (295699378353/2500000000000 : ℝ), (43397615002669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674219077/5000000000 : ℝ)|^4629 ≤ (1399200307647/3125000000000 : ℝ)^3605
        have hw : |(2674219077/5000000000 : ℝ)|=(2674219077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948343527/5000000000 : ℝ)|^4629 ≤ (295699378353/2500000000000 : ℝ)^3605
        have hw : |(-948343527/5000000000 : ℝ)|=(948343527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219916071/10000000000 : ℝ)|^4629 ≤ (43397615002669/100000000000000 : ℝ)^3605
        have hw : |(5219916071/10000000000 : ℝ)|=(5219916071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s5_2 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668554773/1250000000 : ℝ)*x 0 + (65248951/125000000 : ℝ)*x 1 + (-948343501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668554773/1250000000 : ℝ)^4629 ≤ (22387205083593/50000000000000 : ℝ)^3605 := by
    have hnat : (668554773 : ℕ)^4629*50000000000000^3605 ≤ 22387205083593^3605*1250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668554773 1250000000 22387205083593 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65248951/125000000 : ℝ)^4629 ≤ (43397615098747/100000000000000 : ℝ)^3605 := by
    have hnat : (65248951 : ℕ)^4629*100000000000000^3605 ≤ 43397615098747^3605*125000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65248951 125000000 43397615098747 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948343501/5000000000 : ℝ)^4629 ≤ (1182797471773/10000000000000 : ℝ)^3605 := by
    have hnat : (948343501 : ℕ)^4629*10000000000000^3605 ≤ 1182797471773^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948343501 5000000000 1182797471773 10000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668554773/1250000000 : ℝ), (65248951/125000000 : ℝ), (-948343501/5000000000 : ℝ)] ![(22387205083593/50000000000000 : ℝ), (43397615098747/100000000000000 : ℝ), (1182797471773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668554773/1250000000 : ℝ)|^4629 ≤ (22387205083593/50000000000000 : ℝ)^3605
        have hw : |(668554773/1250000000 : ℝ)|=(668554773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65248951/125000000 : ℝ)|^4629 ≤ (43397615098747/100000000000000 : ℝ)^3605
        have hw : |(65248951/125000000 : ℝ)|=(65248951/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948343501/5000000000 : ℝ)|^4629 ≤ (1182797471773/10000000000000 : ℝ)^3605
        have hw : |(-948343501/5000000000 : ℝ)|=(948343501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s5_3 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061317389/2500000000 : ℝ)*x 0 + (4007981259/10000000000 : ℝ)*x 1 + (898770601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061317389/2500000000 : ℝ)^4629 ≤ (2080136366341/6250000000000 : ℝ)^3605 := by
    have hnat : (1061317389 : ℕ)^4629*6250000000000^3605 ≤ 2080136366341^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061317389 2500000000 2080136366341 6250000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007981259/10000000000 : ℝ)^4629 ≤ (30912686511139/100000000000000 : ℝ)^3605 := by
    have hnat : (4007981259 : ℕ)^4629*100000000000000^3605 ≤ 30912686511139^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007981259 10000000000 30912686511139 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898770601/2000000000 : ℝ)^4629 ≤ (35805131609281/100000000000000 : ℝ)^3605 := by
    have hnat : (898770601 : ℕ)^4629*100000000000000^3605 ≤ 35805131609281^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898770601 2000000000 35805131609281 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061317389/2500000000 : ℝ), (4007981259/10000000000 : ℝ), (898770601/2000000000 : ℝ)] ![(2080136366341/6250000000000 : ℝ), (30912686511139/100000000000000 : ℝ), (35805131609281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061317389/2500000000 : ℝ)|^4629 ≤ (2080136366341/6250000000000 : ℝ)^3605
        have hw : |(1061317389/2500000000 : ℝ)|=(1061317389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007981259/10000000000 : ℝ)|^4629 ≤ (30912686511139/100000000000000 : ℝ)^3605
        have hw : |(4007981259/10000000000 : ℝ)|=(4007981259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898770601/2000000000 : ℝ)|^4629 ≤ (35805131609281/100000000000000 : ℝ)^3605
        have hw : |(898770601/2000000000 : ℝ)|=(898770601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s5_4 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1791119133/10000000000 : ℝ)*x 0 + (5220990537/10000000000 : ℝ)*x 1 + (2712612481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1791119133/10000000000 : ℝ)^4629 ≤ (10989413918729/100000000000000 : ℝ)^3605 := by
    have hnat : (1791119133 : ℕ)^4629*100000000000000^3605 ≤ 10989413918729^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791119133 10000000000 10989413918729 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220990537/10000000000 : ℝ)^4629 ≤ (43409085694893/100000000000000 : ℝ)^3605 := by
    have hnat : (5220990537 : ℕ)^4629*100000000000000^3605 ≤ 43409085694893^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220990537 10000000000 43409085694893 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712612481/5000000000 : ℝ)^4629 ≤ (22800750187227/50000000000000 : ℝ)^3605 := by
    have hnat : (2712612481 : ℕ)^4629*50000000000000^3605 ≤ 22800750187227^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712612481 5000000000 22800750187227 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1791119133/10000000000 : ℝ), (5220990537/10000000000 : ℝ), (2712612481/5000000000 : ℝ)] ![(10989413918729/100000000000000 : ℝ), (43409085694893/100000000000000 : ℝ), (22800750187227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1791119133/10000000000 : ℝ)|^4629 ≤ (10989413918729/100000000000000 : ℝ)^3605
        have hw : |(-1791119133/10000000000 : ℝ)|=(1791119133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220990537/10000000000 : ℝ)|^4629 ≤ (43409085694893/100000000000000 : ℝ)^3605
        have hw : |(5220990537/10000000000 : ℝ)|=(5220990537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712612481/5000000000 : ℝ)|^4629 ≤ (22800750187227/50000000000000 : ℝ)^3605
        have hw : |(2712612481/5000000000 : ℝ)|=(2712612481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s5_5 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293859479/10000000000 : ℝ)*x 0 + (-422844557/2500000000 : ℝ)*x 1 + (5425225031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293859479/10000000000 : ℝ)^4629 ≤ (44188573424961/100000000000000 : ℝ)^3605 := by
    have hnat : (5293859479 : ℕ)^4629*100000000000000^3605 ≤ 44188573424961^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293859479 10000000000 44188573424961 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422844557/2500000000 : ℝ)^4629 ≤ (5104962718593/50000000000000 : ℝ)^3605 := by
    have hnat : (422844557 : ℕ)^4629*50000000000000^3605 ≤ 5104962718593^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422844557 2500000000 5104962718593 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425225031/10000000000 : ℝ)^4629 ≤ (45601501119173/100000000000000 : ℝ)^3605 := by
    have hnat : (5425225031 : ℕ)^4629*100000000000000^3605 ≤ 45601501119173^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425225031 10000000000 45601501119173 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293859479/10000000000 : ℝ), (-422844557/2500000000 : ℝ), (5425225031/10000000000 : ℝ)] ![(44188573424961/100000000000000 : ℝ), (5104962718593/50000000000000 : ℝ), (45601501119173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293859479/10000000000 : ℝ)|^4629 ≤ (44188573424961/100000000000000 : ℝ)^3605
        have hw : |(5293859479/10000000000 : ℝ)|=(5293859479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422844557/2500000000 : ℝ)|^4629 ≤ (5104962718593/50000000000000 : ℝ)^3605
        have hw : |(-422844557/2500000000 : ℝ)|=(422844557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425225031/10000000000 : ℝ)|^4629 ≤ (45601501119173/100000000000000 : ℝ)^3605
        have hw : |(5425225031/10000000000 : ℝ)|=(5425225031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s5_6 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293859357/10000000000 : ℝ)*x 0 + (5425225333/10000000000 : ℝ)*x 1 + (-1691377977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293859357/10000000000 : ℝ)^4629 ≤ (44188572117347/100000000000000 : ℝ)^3605 := by
    have hnat : (5293859357 : ℕ)^4629*100000000000000^3605 ≤ 44188572117347^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293859357 10000000000 44188572117347 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425225333/10000000000 : ℝ)^4629 ≤ (45601504378667/100000000000000 : ℝ)^3605 := by
    have hnat : (5425225333 : ℕ)^4629*100000000000000^3605 ≤ 45601504378667^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425225333 10000000000 45601504378667 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691377977/10000000000 : ℝ)^4629 ≤ (5104961745829/50000000000000 : ℝ)^3605 := by
    have hnat : (1691377977 : ℕ)^4629*50000000000000^3605 ≤ 5104961745829^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691377977 10000000000 5104961745829 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293859357/10000000000 : ℝ), (5425225333/10000000000 : ℝ), (-1691377977/10000000000 : ℝ)] ![(44188572117347/100000000000000 : ℝ), (45601504378667/100000000000000 : ℝ), (5104961745829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293859357/10000000000 : ℝ)|^4629 ≤ (44188572117347/100000000000000 : ℝ)^3605
        have hw : |(5293859357/10000000000 : ℝ)|=(5293859357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425225333/10000000000 : ℝ)|^4629 ≤ (45601504378667/100000000000000 : ℝ)^3605
        have hw : |(5425225333/10000000000 : ℝ)|=(5425225333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1691377977/10000000000 : ℝ)|^4629 ≤ (5104961745829/50000000000000 : ℝ)^3605
        have hw : |(-1691377977/10000000000 : ℝ)|=(1691377977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s5_7 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4145833/9765625 : ℝ)*x 0 + (4491324047/10000000000 : ℝ)*x 1 + (4010528843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145833/9765625 : ℝ)^4629 ≤ (33282820455909/100000000000000 : ℝ)^3605 := by
    have hnat : (4145833 : ℕ)^4629*100000000000000^3605 ≤ 33282820455909^3605*9765625^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145833 9765625 33282820455909 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491324047/10000000000 : ℝ)^4629 ≤ (8944815122429/25000000000000 : ℝ)^3605 := by
    have hnat : (4491324047 : ℕ)^4629*25000000000000^3605 ≤ 8944815122429^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491324047 10000000000 8944815122429 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4010528843/10000000000 : ℝ)^4629 ≤ (30937919034857/100000000000000 : ℝ)^3605 := by
    have hnat : (4010528843 : ℕ)^4629*100000000000000^3605 ≤ 30937919034857^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010528843 10000000000 30937919034857 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145833/9765625 : ℝ), (4491324047/10000000000 : ℝ), (4010528843/10000000000 : ℝ)] ![(33282820455909/100000000000000 : ℝ), (8944815122429/25000000000000 : ℝ), (30937919034857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145833/9765625 : ℝ)|^4629 ≤ (33282820455909/100000000000000 : ℝ)^3605
        have hw : |(4145833/9765625 : ℝ)|=(4145833/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491324047/10000000000 : ℝ)|^4629 ≤ (8944815122429/25000000000000 : ℝ)^3605
        have hw : |(4491324047/10000000000 : ℝ)|=(4491324047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4010528843/10000000000 : ℝ)|^4629 ≤ (30937919034857/100000000000000 : ℝ)^3605
        have hw : |(4010528843/10000000000 : ℝ)|=(4010528843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1566_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2777/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2221/20000 : ℝ) ^ (4627/1024 : ℝ) ≤ (1216363660417993/25000000000000000000 : ℝ) := by
    have hpowers : (2221/20000 : ℝ)^4627 ≤ (1216363660417993/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2221 : ℕ)^4627*25000000000000000000^1024 ≤ 1216363660417993^1024*20000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2221 20000 1216363660417993 25000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2221/20000 : ℝ)) (X := (1216363660417993/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4627/1024 : ℝ) ≤ (4375015965048973/20000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4627 ≤ (4375015965048973/20000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4627*20000000000000000000^1024 ≤ 4375015965048973^1024*3125^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 4375015965048973 20000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (4375015965048973/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501216363660417993/12500000000000000000 : ℝ) ≤ (2500053836576651/2500000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (12501216363660417993/12500000000000000000 : ℝ)^1024 ≤ (2500053836576651/2500000000000000 : ℝ)^4627 := by
      have hnat : (12501216363660417993 : ℕ)^1024*2500000000000000^4627 ≤ 2500053836576651^4627*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501216363660417993 12500000000000000000 2500053836576651 2500000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500053836576651/2500000000000000 : ℝ)) (X := (12501216363660417993/12500000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026740534466916837/100000000000000000000 : ℝ) ≤ (2500147933093217/2500000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (100026740534466916837/100000000000000000000 : ℝ)^1024 ≤ (2500147933093217/2500000000000000 : ℝ)^4627 := by
      have hnat : (100026740534466916837 : ℕ)^1024*2500000000000000^4627 ≤ 2500147933093217^4627*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026740534466916837 100000000000000000000 2500147933093217 2500000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500147933093217/2500000000000000 : ℝ)) (X := (100026740534466916837/100000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004375015965048973/10000000000000000000 : ℝ) ≤ (2500242029609783/2500000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (10004375015965048973/10000000000000000000 : ℝ)^1024 ≤ (2500242029609783/2500000000000000 : ℝ)^4627 := by
      have hnat : (10004375015965048973 : ℕ)^1024*2500000000000000^4627 ≤ 2500242029609783^4627*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004375015965048973 10000000000000000000 2500242029609783 2500000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500242029609783/2500000000000000 : ℝ)) (X := (10004375015965048973/10000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1216363660417993/25000000000000000000 : ℝ) ≤ ((3651882027360843491/3652500000000000000 : ℝ)+2*(15682752761/18262500000000 : ℝ)*(2221/20000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (3651882027360843491/3652500000000000000 : ℝ)+2*(15682752761/18262500000000 : ℝ)*(2221/20000 : ℝ)=(2500053836576651/2500000000000000 : ℝ) by norm_num, show 1+2*(1216363660417993/25000000000000000000 : ℝ)=(12501216363660417993/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4375015965048973/20000000000000000000 : ℝ)+(1216363660417993/25000000000000000000 : ℝ) ≤ ((3651882027360843491/3652500000000000000 : ℝ)+(15682752761/18262500000000 : ℝ)*((484/3125 : ℝ)+(2221/20000 : ℝ)))^(4627/1024 : ℝ) := by
    rw [show (3651882027360843491/3652500000000000000 : ℝ)+(15682752761/18262500000000 : ℝ)*((484/3125 : ℝ)+(2221/20000 : ℝ))=(2500147933093217/2500000000000000 : ℝ) by norm_num, show 1+(4375015965048973/20000000000000000000 : ℝ)+(1216363660417993/25000000000000000000 : ℝ)=(100026740534466916837/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4375015965048973/20000000000000000000 : ℝ) ≤ ((3651882027360843491/3652500000000000000 : ℝ)+2*(15682752761/18262500000000 : ℝ)*(484/3125 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (3651882027360843491/3652500000000000000 : ℝ)+2*(15682752761/18262500000000 : ℝ)*(484/3125 : ℝ)=(2500242029609783/2500000000000000 : ℝ) by norm_num, show 1+2*(4375015965048973/20000000000000000000 : ℝ)=(10004375015965048973/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3651882027360843491/3652500000000000000 : ℝ)*(X 1 0+X 2 0)+(15682752761/18262500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (3651882027360843491/3652500000000000000 : ℝ)) (alpha := (15682752761/18262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3651882027360843491/3652500000000000000 : ℝ)*(X 0 1+X 2 1)+(15682752761/18262500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (3651882027360843491/3652500000000000000 : ℝ)) (alpha := (15682752761/18262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3651882027360843491/3652500000000000000 : ℝ)*(X 0 2+X 1 2)+(15682752761/18262500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (3651882027360843491/3652500000000000000 : ℝ)) (alpha := (15682752761/18262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1791092433/10000000000 : ℝ)*X 0 0+(84786051/156250000 : ℝ)*X 0 1+(2609958007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674219077/5000000000 : ℝ)*X 1 0+(-948343527/5000000000 : ℝ)*X 1 1+(5219916071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668554773/1250000000 : ℝ)*X 2 0+(65248951/125000000 : ℝ)*X 2 1+(-948343501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061317389/2500000000 : ℝ)*X 0 0+(4007981259/10000000000 : ℝ)*X 0 1+(898770601/2000000000 : ℝ)*X 0 2+(1061317389/2500000000 : ℝ)*X 1 0+(4007981259/10000000000 : ℝ)*X 1 1+(898770601/2000000000 : ℝ)*X 1 2+(1061317389/2500000000 : ℝ)*X 2 0+(4007981259/10000000000 : ℝ)*X 2 1+(898770601/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1791119133/10000000000 : ℝ)*X 0 0+(5220990537/10000000000 : ℝ)*X 0 1+(2712612481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293859479/10000000000 : ℝ)*X 1 0+(-422844557/2500000000 : ℝ)*X 1 1+(5425225031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293859357/10000000000 : ℝ)*X 2 0+(5425225333/10000000000 : ℝ)*X 2 1+(-1691377977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4145833/9765625 : ℝ)*X 0 0+(4491324047/10000000000 : ℝ)*X 0 1+(4010528843/10000000000 : ℝ)*X 0 2+(4145833/9765625 : ℝ)*X 1 0+(4491324047/10000000000 : ℝ)*X 1 1+(4010528843/10000000000 : ℝ)*X 1 2+(4145833/9765625 : ℝ)*X 2 0+(4491324047/10000000000 : ℝ)*X 2 1+(4010528843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262344277900875880348288659/30437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682542631/50000000000000 : ℝ)*(base19) + (252880853/20000000000000 : ℝ)*(base23) + (68384249/100000000000000 : ℝ)*(lower2) + (1791189/1000000000000 : ℝ)*(upper3) + (14353517/10000000000000 : ℝ)*(upper5) + (1725847686714617/50000000000000 : ℝ)*(major0) + (1725847686714617/50000000000000 : ℝ)*(major1) + (1725847686714617/50000000000000 : ℝ)*(major2) + (605648799409559/12500000000000 : ℝ)*(sp0) + (4845213433464519/100000000000000 : ℝ)*(sp1) + (969042706829103/20000000000000 : ℝ)*(sp2) + (257270687951603/12500000000000 : ℝ)*(sp3) + (6100818327/25000000000000 : ℝ)*(sp4) + (10157392063/100000000000000 : ℝ)*(sp7) + (2058175661004887/100000000000000 : ℝ)*(f.failure) + (242260739927489/5000000000000 : ℝ)*(f.sum) + (2012889180227/1826250000000000000000000000 : ℝ)*base66 + (221591244090427649/60875000000000000000000000000000 : ℝ)*base67 + (63202849062427649/60875000000000000000000000000000 : ℝ)*base69 + (333351462703552649/60875000000000000000000000000000 : ℝ)*base71 + (3998575078463/7305000000000000000000000000 : ℝ)*base74 + (19601255410552649/60875000000000000000000000000000 : ℝ)*base75 + (551680451683802649/60875000000000000000000000000000 : ℝ)*base77 + (914726035408927649/60875000000000000000000000000000 : ℝ)*base79 + (41585326498103/7305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (70904963/10000000000000000000000 : ℝ)*base89 + (70904963/10000000000000000000000 : ℝ)*base91 + (70904963/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4913328278730613878487/487000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52061943/6250000000000 : ℝ)*(base19) + (1242001861/100000000000000 : ℝ)*(base23) + (220896421/100000000000000 : ℝ)*(lower1) + (193962833/100000000000000 : ℝ)*(upper3) + (7924771/4000000000000 : ℝ)*(lower4) + (5997559/6250000000000 : ℝ)*(upper5) + (348809993674453/10000000000000 : ℝ)*(major0) + (348809993674453/10000000000000 : ℝ)*(major1) + (348809993674453/10000000000000 : ℝ)*(major2) + (14316968001/100000000000000 : ℝ)*(sp2) + (4896316576421159/100000000000000 : ℝ)*(sp4) + (489631574343007/10000000000000 : ℝ)*(sp5) + (4896301017451297/100000000000000 : ℝ)*(sp6) + (2079882960768891/100000000000000 : ℝ)*(sp7) + (2079882960768891/100000000000000 : ℝ)*(f.failure) + (4896316576421159/100000000000000 : ℝ)*(f.sum) + (8688944399497/1461000000000000000000000000 : ℝ)*base66 + (34202492046045141/12175000000000000000000000000000 : ℝ)*base67 + (106926453152879859/12175000000000000000000000000000 : ℝ)*base70 + (548715664892195141/12175000000000000000000000000000 : ℝ)*base71 + (1215628690991/1461000000000000000000000000 : ℝ)*base73 + (1045987992158979859/12175000000000000000000000000000 : ℝ)*base76 + (17746331523329859/12175000000000000000000000000000 : ℝ)*base78 + (53951674015395141/12175000000000000000000000000000 : ℝ)*base79 + (950559083233/730500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (96167159/10000000000000000000000 : ℝ)*base89 + (96167159/10000000000000000000000 : ℝ)*base91 + (96167159/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1566_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1566_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1566_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7911/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1566_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1566_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1566_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7911/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1566_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
