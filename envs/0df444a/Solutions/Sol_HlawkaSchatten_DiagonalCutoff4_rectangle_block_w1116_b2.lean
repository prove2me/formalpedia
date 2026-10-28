-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1116_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:07:21.963765+00:00
-- url     : https://prove2.me/submissions/9a68f0d3-8702-436d-bc49-e43a87b204be

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
theorem support_rectangle_w1116_s6_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272418591/1250000000 : ℝ)*x 0 + (1348475783/2500000000 : ℝ)*x 1 + (5264928901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272418591/1250000000 : ℝ)^8309 ≤ (13240078489063/100000000000000 : ℝ)^6261 := by
    have hnat : (272418591 : ℕ)^8309*100000000000000^6261 ≤ 13240078489063^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272418591 1250000000 13240078489063 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348475783/2500000000 : ℝ)^8309 ≤ (11019135349531/25000000000000 : ℝ)^6261 := by
    have hnat : (1348475783 : ℕ)^8309*25000000000000^6261 ≤ 11019135349531^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348475783 2500000000 11019135349531 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264928901/10000000000 : ℝ)^8309 ≤ (21341690052343/50000000000000 : ℝ)^6261 := by
    have hnat : (5264928901 : ℕ)^8309*50000000000000^6261 ≤ 21341690052343^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264928901 10000000000 21341690052343 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272418591/1250000000 : ℝ), (1348475783/2500000000 : ℝ), (5264928901/10000000000 : ℝ)] ![(13240078489063/100000000000000 : ℝ), (11019135349531/25000000000000 : ℝ), (21341690052343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272418591/1250000000 : ℝ)|^8309 ≤ (13240078489063/100000000000000 : ℝ)^6261
        have hw : |(-272418591/1250000000 : ℝ)|=(272418591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348475783/2500000000 : ℝ)|^8309 ≤ (11019135349531/25000000000000 : ℝ)^6261
        have hw : |(1348475783/2500000000 : ℝ)|=(1348475783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264928901/10000000000 : ℝ)|^8309 ≤ (21341690052343/50000000000000 : ℝ)^6261
        have hw : |(5264928901/10000000000 : ℝ)|=(5264928901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s6_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336237003/2500000000 : ℝ)*x 0 + (-1122389579/5000000000 : ℝ)*x 1 + (5264928813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336237003/2500000000 : ℝ)^8309 ≤ (348371499243/800000000000 : ℝ)^6261 := by
    have hnat : (1336237003 : ℕ)^8309*800000000000^6261 ≤ 348371499243^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336237003 2500000000 348371499243 800000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122389579/5000000000 : ℝ)^8309 ≤ (6885091713503/50000000000000 : ℝ)^6261 := by
    have hnat : (1122389579 : ℕ)^8309*50000000000000^6261 ≤ 6885091713503^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122389579 5000000000 6885091713503 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264928813/10000000000 : ℝ)^8309 ≤ (8536675831579/20000000000000 : ℝ)^6261 := by
    have hnat : (5264928813 : ℕ)^8309*20000000000000^6261 ≤ 8536675831579^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264928813 10000000000 8536675831579 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336237003/2500000000 : ℝ), (-1122389579/5000000000 : ℝ), (5264928813/10000000000 : ℝ)] ![(348371499243/800000000000 : ℝ), (6885091713503/50000000000000 : ℝ), (8536675831579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336237003/2500000000 : ℝ)|^8309 ≤ (348371499243/800000000000 : ℝ)^6261
        have hw : |(1336237003/2500000000 : ℝ)|=(1336237003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122389579/5000000000 : ℝ)|^8309 ≤ (6885091713503/50000000000000 : ℝ)^6261
        have hw : |(-1122389579/5000000000 : ℝ)|=(1122389579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264928813/10000000000 : ℝ)|^8309 ≤ (8536675831579/20000000000000 : ℝ)^6261
        have hw : |(5264928813/10000000000 : ℝ)|=(5264928813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s6_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068989613/2000000000 : ℝ)*x 0 + (329058041/625000000 : ℝ)*x 1 + (-1122389647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068989613/2000000000 : ℝ)^8309 ≤ (21773218989211/50000000000000 : ℝ)^6261 := by
    have hnat : (1068989613 : ℕ)^8309*50000000000000^6261 ≤ 21773218989211^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068989613 2000000000 21773218989211 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329058041/625000000 : ℝ)^8309 ≤ (21341688734367/50000000000000 : ℝ)^6261 := by
    have hnat : (329058041 : ℕ)^8309*50000000000000^6261 ≤ 21341688734367^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329058041 625000000 21341688734367 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122389647/5000000000 : ℝ)^8309 ≤ (2754036906833/20000000000000 : ℝ)^6261 := by
    have hnat : (1122389647 : ℕ)^8309*20000000000000^6261 ≤ 2754036906833^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122389647 5000000000 2754036906833 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068989613/2000000000 : ℝ), (329058041/625000000 : ℝ), (-1122389647/5000000000 : ℝ)] ![(21773218989211/50000000000000 : ℝ), (21341688734367/50000000000000 : ℝ), (2754036906833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068989613/2000000000 : ℝ)|^8309 ≤ (21773218989211/50000000000000 : ℝ)^6261
        have hw : |(1068989613/2000000000 : ℝ)|=(1068989613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329058041/625000000 : ℝ)|^8309 ≤ (21341688734367/50000000000000 : ℝ)^6261
        have hw : |(329058041/625000000 : ℝ)|=(329058041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122389647/5000000000 : ℝ)|^8309 ≤ (2754036906833/20000000000000 : ℝ)^6261
        have hw : |(-1122389647/5000000000 : ℝ)|=(1122389647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s6_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368328581/10000000000 : ℝ)*x 0 + (4242554271/10000000000 : ℝ)*x 1 + (281114859/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368328581/10000000000 : ℝ)^8309 ≤ (33316616265267/100000000000000 : ℝ)^6261 := by
    have hnat : (4368328581 : ℕ)^8309*100000000000000^6261 ≤ 33316616265267^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368328581 10000000000 33316616265267 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242554271/10000000000 : ℝ)^8309 ≤ (32049608688963/100000000000000 : ℝ)^6261 := by
    have hnat : (4242554271 : ℕ)^8309*100000000000000^6261 ≤ 32049608688963^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242554271 10000000000 32049608688963 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281114859/625000000 : ℝ)^8309 ≤ (34633775033283/100000000000000 : ℝ)^6261 := by
    have hnat : (281114859 : ℕ)^8309*100000000000000^6261 ≤ 34633775033283^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281114859 625000000 34633775033283 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368328581/10000000000 : ℝ), (4242554271/10000000000 : ℝ), (281114859/625000000 : ℝ)] ![(33316616265267/100000000000000 : ℝ), (32049608688963/100000000000000 : ℝ), (34633775033283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368328581/10000000000 : ℝ)|^8309 ≤ (33316616265267/100000000000000 : ℝ)^6261
        have hw : |(4368328581/10000000000 : ℝ)|=(4368328581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242554271/10000000000 : ℝ)|^8309 ≤ (32049608688963/100000000000000 : ℝ)^6261
        have hw : |(4242554271/10000000000 : ℝ)|=(4242554271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281114859/625000000 : ℝ)|^8309 ≤ (34633775033283/100000000000000 : ℝ)^6261
        have hw : |(281114859/625000000 : ℝ)|=(281114859/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s6_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179353883/10000000000 : ℝ)*x 0 + (5265254403/10000000000 : ℝ)*x 1 + (5393576357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179353883/10000000000 : ℝ)^8309 ≤ (6620060025593/50000000000000 : ℝ)^6261 := by
    have hnat : (2179353883 : ℕ)^8309*50000000000000^6261 ≤ 6620060025593^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179353883 10000000000 6620060025593 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265254403/10000000000 : ℝ)^8309 ≤ (21343441105803/50000000000000 : ℝ)^6261 := by
    have hnat : (5265254403 : ℕ)^8309*50000000000000^6261 ≤ 21343441105803^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265254403 10000000000 21343441105803 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393576357/10000000000 : ℝ)^8309 ≤ (44072997722661/100000000000000 : ℝ)^6261 := by
    have hnat : (5393576357 : ℕ)^8309*100000000000000^6261 ≤ 44072997722661^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393576357 10000000000 44072997722661 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179353883/10000000000 : ℝ), (5265254403/10000000000 : ℝ), (5393576357/10000000000 : ℝ)] ![(6620060025593/50000000000000 : ℝ), (21343441105803/50000000000000 : ℝ), (44072997722661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179353883/10000000000 : ℝ)|^8309 ≤ (6620060025593/50000000000000 : ℝ)^6261
        have hw : |(-2179353883/10000000000 : ℝ)|=(2179353883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265254403/10000000000 : ℝ)|^8309 ≤ (21343441105803/50000000000000 : ℝ)^6261
        have hw : |(5265254403/10000000000 : ℝ)|=(5265254403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393576357/10000000000 : ℝ)|^8309 ≤ (44072997722661/100000000000000 : ℝ)^6261
        have hw : |(5393576357/10000000000 : ℝ)|=(5393576357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s6_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312335507/10000000000 : ℝ)*x 0 + (-1058065821/5000000000 : ℝ)*x 1 + (269678817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312335507/10000000000 : ℝ)^8309 ≤ (8638835347351/20000000000000 : ℝ)^6261 := by
    have hnat : (5312335507 : ℕ)^8309*20000000000000^6261 ≤ 8638835347351^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312335507 10000000000 8638835347351 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058065821/5000000000 : ℝ)^8309 ≤ (12732825709597/100000000000000 : ℝ)^6261 := by
    have hnat : (1058065821 : ℕ)^8309*100000000000000^6261 ≤ 12732825709597^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058065821 5000000000 12732825709597 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269678817/500000000 : ℝ)^8309 ≤ (11018249384577/25000000000000 : ℝ)^6261 := by
    have hnat : (269678817 : ℕ)^8309*25000000000000^6261 ≤ 11018249384577^6261*500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269678817 500000000 11018249384577 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312335507/10000000000 : ℝ), (-1058065821/5000000000 : ℝ), (269678817/500000000 : ℝ)] ![(8638835347351/20000000000000 : ℝ), (12732825709597/100000000000000 : ℝ), (11018249384577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312335507/10000000000 : ℝ)|^8309 ≤ (8638835347351/20000000000000 : ℝ)^6261
        have hw : |(5312335507/10000000000 : ℝ)|=(5312335507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058065821/5000000000 : ℝ)|^8309 ≤ (12732825709597/100000000000000 : ℝ)^6261
        have hw : |(-1058065821/5000000000 : ℝ)|=(1058065821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269678817/500000000 : ℝ)|^8309 ≤ (11018249384577/25000000000000 : ℝ)^6261
        have hw : |(269678817/500000000 : ℝ)|=(269678817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s6_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312335543/10000000000 : ℝ)*x 0 + (4314861/8000000 : ℝ)*x 1 + (-423226343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312335543/10000000000 : ℝ)^8309 ≤ (1349818035163/3125000000000 : ℝ)^6261 := by
    have hnat : (5312335543 : ℕ)^8309*3125000000000^6261 ≤ 1349818035163^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312335543 10000000000 1349818035163 3125000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314861/8000000 : ℝ)^8309 ≤ (44072996562323/100000000000000 : ℝ)^6261 := by
    have hnat : (4314861 : ℕ)^8309*100000000000000^6261 ≤ 44072996562323^6261*8000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314861 8000000 44072996562323 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423226343/2000000000 : ℝ)^8309 ≤ (12732826292519/100000000000000 : ℝ)^6261 := by
    have hnat : (423226343 : ℕ)^8309*100000000000000^6261 ≤ 12732826292519^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423226343 2000000000 12732826292519 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312335543/10000000000 : ℝ), (4314861/8000000 : ℝ), (-423226343/2000000000 : ℝ)] ![(1349818035163/3125000000000 : ℝ), (44072996562323/100000000000000 : ℝ), (12732826292519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312335543/10000000000 : ℝ)|^8309 ≤ (1349818035163/3125000000000 : ℝ)^6261
        have hw : |(5312335543/10000000000 : ℝ)|=(5312335543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314861/8000000 : ℝ)|^8309 ≤ (44072996562323/100000000000000 : ℝ)^6261
        have hw : |(4314861/8000000 : ℝ)|=(4314861/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423226343/2000000000 : ℝ)|^8309 ≤ (12732826292519/100000000000000 : ℝ)^6261
        have hw : |(-423226343/2000000000 : ℝ)|=(423226343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s6_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174733553/400000000 : ℝ)*x 0 + (2248596447/5000000000 : ℝ)*x 1 + (424320119/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174733553/400000000 : ℝ)^8309 ≤ (33316719951329/100000000000000 : ℝ)^6261 := by
    have hnat : (174733553 : ℕ)^8309*100000000000000^6261 ≤ 33316719951329^6261*400000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174733553 400000000 33316719951329 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248596447/5000000000 : ℝ)^8309 ≤ (34627185576371/100000000000000 : ℝ)^6261 := by
    have hnat : (2248596447 : ℕ)^8309*100000000000000^6261 ≤ 34627185576371^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248596447 5000000000 34627185576371 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424320119/1000000000 : ℝ)^8309 ≤ (32056094452591/100000000000000 : ℝ)^6261 := by
    have hnat : (424320119 : ℕ)^8309*100000000000000^6261 ≤ 32056094452591^6261*1000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424320119 1000000000 32056094452591 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174733553/400000000 : ℝ), (2248596447/5000000000 : ℝ), (424320119/1000000000 : ℝ)] ![(33316719951329/100000000000000 : ℝ), (34627185576371/100000000000000 : ℝ), (32056094452591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174733553/400000000 : ℝ)|^8309 ≤ (33316719951329/100000000000000 : ℝ)^6261
        have hw : |(174733553/400000000 : ℝ)|=(174733553/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248596447/5000000000 : ℝ)|^8309 ≤ (34627185576371/100000000000000 : ℝ)^6261
        have hw : |(2248596447/5000000000 : ℝ)|=(2248596447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424320119/1000000000 : ℝ)|^8309 ≤ (32056094452591/100000000000000 : ℝ)^6261
        have hw : |(424320119/1000000000 : ℝ)|=(424320119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2819/25000 : ℝ) ^ (2077/512 : ℝ) ≤ (571470387134859/4000000000000000000 : ℝ) := by
    have hpowers : (2819/25000 : ℝ)^2077 ≤ (571470387134859/4000000000000000000 : ℝ)^512 := by
      have hnat : (2819 : ℕ)^2077*4000000000000000000^512 ≤ 571470387134859^512*25000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 25000 571470387134859 4000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/25000 : ℝ)) (X := (571470387134859/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7039/50000 : ℝ) ^ (2077/512 : ℝ) ≤ (35150917984531231/100000000000000000000 : ℝ) := by
    have hpowers : (7039/50000 : ℝ)^2077 ≤ (35150917984531231/100000000000000000000 : ℝ)^512 := by
      have hnat : (7039 : ℕ)^2077*100000000000000000000^512 ≤ 35150917984531231^512*50000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7039 50000 35150917984531231 100000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7039/50000 : ℝ)) (X := (35150917984531231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000571470387134859/2000000000000000000 : ℝ) ≤ (5000352144133403/5000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (2000571470387134859/2000000000000000000 : ℝ)^512 ≤ (5000352144133403/5000000000000000 : ℝ)^2077 := by
      have hnat : (2000571470387134859 : ℕ)^512*5000000000000000^2077 ≤ 5000352144133403^2077*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000571470387134859 2000000000000000000 5000352144133403 5000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000352144133403/5000000000000000 : ℝ)) (X := (2000571470387134859/2000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024718838831451353/50000000000000000000 : ℝ) ≤ (500060922912479/500000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50024718838831451353/50000000000000000000 : ℝ)^512 ≤ (500060922912479/500000000000000 : ℝ)^2077 := by
      have hnat : (50024718838831451353 : ℕ)^512*500000000000000^2077 ≤ 500060922912479^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024718838831451353 50000000000000000000 500060922912479 500000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500060922912479/500000000000000 : ℝ)) (X := (50024718838831451353/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035150917984531231/50000000000000000000 : ℝ) ≤ (5000866314116177/5000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50035150917984531231/50000000000000000000 : ℝ)^512 ≤ (5000866314116177/5000000000000000 : ℝ)^2077 := by
      have hnat : (50035150917984531231 : ℕ)^512*5000000000000000^2077 ≤ 5000866314116177^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035150917984531231 50000000000000000000 5000866314116177 5000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000866314116177/5000000000000000 : ℝ)) (X := (50035150917984531231/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(571470387134859/4000000000000000000 : ℝ) ≤ ((2334198154522672597/2335000000000000000 : ℝ)+2*(85694997129/46700000000000 : ℝ)*(2819/25000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (2334198154522672597/2335000000000000000 : ℝ)+2*(85694997129/46700000000000 : ℝ)*(2819/25000 : ℝ)=(5000352144133403/5000000000000000 : ℝ) by norm_num, show 1+2*(571470387134859/4000000000000000000 : ℝ)=(2000571470387134859/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35150917984531231/100000000000000000000 : ℝ)+(571470387134859/4000000000000000000 : ℝ) ≤ ((2334198154522672597/2335000000000000000 : ℝ)+(85694997129/46700000000000 : ℝ)*((7039/50000 : ℝ)+(2819/25000 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (2334198154522672597/2335000000000000000 : ℝ)+(85694997129/46700000000000 : ℝ)*((7039/50000 : ℝ)+(2819/25000 : ℝ))=(500060922912479/500000000000000 : ℝ) by norm_num, show 1+(35150917984531231/100000000000000000000 : ℝ)+(571470387134859/4000000000000000000 : ℝ)=(50024718838831451353/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35150917984531231/100000000000000000000 : ℝ) ≤ ((2334198154522672597/2335000000000000000 : ℝ)+2*(85694997129/46700000000000 : ℝ)*(7039/50000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (2334198154522672597/2335000000000000000 : ℝ)+2*(85694997129/46700000000000 : ℝ)*(7039/50000 : ℝ)=(5000866314116177/5000000000000000 : ℝ) by norm_num, show 1+2*(35150917984531231/100000000000000000000 : ℝ)=(50035150917984531231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2334198154522672597/2335000000000000000 : ℝ)*(X 1 0+X 2 0)+(85694997129/46700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (2334198154522672597/2335000000000000000 : ℝ)) (alpha := (85694997129/46700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2334198154522672597/2335000000000000000 : ℝ)*(X 0 1+X 2 1)+(85694997129/46700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (2334198154522672597/2335000000000000000 : ℝ)) (alpha := (85694997129/46700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2334198154522672597/2335000000000000000 : ℝ)*(X 0 2+X 1 2)+(85694997129/46700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (2334198154522672597/2335000000000000000 : ℝ)) (alpha := (85694997129/46700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-272418591/1250000000 : ℝ)*X 0 0+(1348475783/2500000000 : ℝ)*X 0 1+(5264928901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336237003/2500000000 : ℝ)*X 1 0+(-1122389579/5000000000 : ℝ)*X 1 1+(5264928813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068989613/2000000000 : ℝ)*X 2 0+(329058041/625000000 : ℝ)*X 2 1+(-1122389647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368328581/10000000000 : ℝ)*X 0 0+(4242554271/10000000000 : ℝ)*X 0 1+(281114859/625000000 : ℝ)*X 0 2+(4368328581/10000000000 : ℝ)*X 1 0+(4242554271/10000000000 : ℝ)*X 1 1+(281114859/625000000 : ℝ)*X 1 2+(4368328581/10000000000 : ℝ)*X 2 0+(4242554271/10000000000 : ℝ)*X 2 1+(281114859/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2179353883/10000000000 : ℝ)*X 0 0+(5265254403/10000000000 : ℝ)*X 0 1+(5393576357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312335507/10000000000 : ℝ)*X 1 0+(-1058065821/5000000000 : ℝ)*X 1 1+(269678817/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312335543/10000000000 : ℝ)*X 2 0+(4314861/8000000 : ℝ)*X 2 1+(-423226343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174733553/400000000 : ℝ)*X 0 0+(2248596447/5000000000 : ℝ)*X 0 1+(424320119/1000000000 : ℝ)*X 0 2+(174733553/400000000 : ℝ)*X 1 0+(2248596447/5000000000 : ℝ)*X 1 1+(424320119/1000000000 : ℝ)*X 1 2+(174733553/400000000 : ℝ)*X 2 0+(2248596447/5000000000 : ℝ)*X 2 1+(424320119/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91586501488704271188793353/29187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54607739/12500000000000 : ℝ)*(base19) + (615986019/100000000000000 : ℝ)*(base23) + (67932859/100000000000000 : ℝ)*(upper2) + (803013/10000000000000 : ℝ)*(upper3) + (1458842679518717/25000000000000 : ℝ)*(major0) + (1458842679518717/25000000000000 : ℝ)*(major1) + (1458842679518717/25000000000000 : ℝ)*(major2) + (1550699748545409/20000000000000 : ℝ)*(sp0) + (1938377114336443/25000000000000 : ℝ)*(sp1) + (7753504204465307/100000000000000 : ℝ)*(sp2) + (30603307035431/781250000000 : ℝ)*(sp3) + (10151480639/100000000000000 : ℝ)*(sp4) + (4073756357/100000000000000 : ℝ)*(sp6) + (4568405649/50000000000000 : ℝ)*(sp7) + (3917232437346467/100000000000000 : ℝ)*(f.failure) + (1938377223551921/25000000000000 : ℝ)*(f.sum) + (8285380042537/2335000000000000000000000000 : ℝ)*base65 + (480554268399273049/58375000000000000000000000000000 : ℝ)*base67 + (89902453020851951/58375000000000000000000000000000 : ℝ)*base70 + (1355883930302398049/58375000000000000000000000000000 : ℝ)*base71 + (265870434129/291875000000000000000000000 : ℝ)*base73 + (713233561527851951/58375000000000000000000000000000 : ℝ)*base76 + (481743258163148049/58375000000000000000000000000000 : ℝ)*base77 + (382878288849898049/58375000000000000000000000000000 : ℝ)*base79 + (207362027193/2335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2525489/1000000000000000000000 : ℝ)*base89 + (2525489/1000000000000000000000 : ℝ)*base91 + (2525489/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23798274507788609751513/2335000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2285712911/100000000000000 : ℝ)*(base19) + (1148517903/50000000000000 : ℝ)*(base23) + (47741/4000000000000 : ℝ)*(upper2) + (105119273/50000000000000 : ℝ)*(upper3) + (284392239/100000000000000 : ℝ)*(upper5) + (22910230146469/390625000000 : ℝ)*(major0) + (22910230146469/390625000000 : ℝ)*(major1) + (22910230146469/390625000000 : ℝ)*(major2) + (32235743059/50000000000000 : ℝ)*(sp1) + (57347544033/100000000000000 : ℝ)*(sp2) + (1948225621366061/25000000000000 : ℝ)*(sp4) + (3896417864132607/50000000000000 : ℝ)*(sp5) + (1948210710221101/25000000000000 : ℝ)*(sp6) + (984283752448797/25000000000000 : ℝ)*(sp7) + (984283752448797/25000000000000 : ℝ)*(f.failure) + (1948225621366061/25000000000000 : ℝ)*(f.sum) + (684527237853/291875000000000000000000000 : ℝ)*base66 + (28209076470210611/1824218750000000000000000000000 : ℝ)*base67 + (39990604631383139/1824218750000000000000000000000 : ℝ)*base70 + (7203900753875653/3648437500000000000000000000000 : ℝ)*base72 + (673859029143/291875000000000000000000000 : ℝ)*base74 + (13214932153936847/3648437500000000000000000000000 : ℝ)*base75 + (143375445314016931/7296875000000000000000000000000 : ℝ)*base78 + (17065930884378743/912109375000000000000000000000 : ℝ)*base79 + (1262407425663/1167500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3459599/250000000000000000000 : ℝ)*base89 + (3459599/250000000000000000000 : ℝ)*base91 + (3459599/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1116_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1116_s7_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089687559/5000000000 : ℝ)*x 0 + (5393540931/10000000000 : ℝ)*x 1 + (1316318549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089687559/5000000000 : ℝ)^8309 ≤ (13240291258447/100000000000000 : ℝ)^6261 := by
    have hnat : (1089687559 : ℕ)^8309*100000000000000^6261 ≤ 13240291258447^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089687559 5000000000 13240291258447 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393540931/10000000000 : ℝ)^8309 ≤ (44072613553529/100000000000000 : ℝ)^6261 := by
    have hnat : (5393540931 : ℕ)^8309*100000000000000^6261 ≤ 44072613553529^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393540931 10000000000 44072613553529 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316318549/2500000000 : ℝ)^8309 ≤ (42687095168657/100000000000000 : ℝ)^6261 := by
    have hnat : (1316318549 : ℕ)^8309*100000000000000^6261 ≤ 42687095168657^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316318549 2500000000 42687095168657 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089687559/5000000000 : ℝ), (5393540931/10000000000 : ℝ), (1316318549/2500000000 : ℝ)] ![(13240291258447/100000000000000 : ℝ), (44072613553529/100000000000000 : ℝ), (42687095168657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089687559/5000000000 : ℝ)|^8309 ≤ (13240291258447/100000000000000 : ℝ)^6261
        have hw : |(-1089687559/5000000000 : ℝ)|=(1089687559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393540931/10000000000 : ℝ)|^8309 ≤ (44072613553529/100000000000000 : ℝ)^6261
        have hw : |(5393540931/10000000000 : ℝ)|=(5393540931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316318549/2500000000 : ℝ)|^8309 ≤ (42687095168657/100000000000000 : ℝ)^6261
        have hw : |(1316318549/2500000000 : ℝ)|=(1316318549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s7_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344858603/10000000000 : ℝ)*x 0 + (-2244441421/10000000000 : ℝ)*x 1 + (2632637103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344858603/10000000000 : ℝ)^8309 ≤ (43545470699741/100000000000000 : ℝ)^6261 := by
    have hnat : (5344858603 : ℕ)^8309*100000000000000^6261 ≤ 43545470699741^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344858603 10000000000 43545470699741 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244441421/10000000000 : ℝ)^8309 ≤ (2753486803901/20000000000000 : ℝ)^6261 := by
    have hnat : (2244441421 : ℕ)^8309*20000000000000^6261 ≤ 2753486803901^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244441421 10000000000 2753486803901 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632637103/5000000000 : ℝ)^8309 ≤ (42687095276249/100000000000000 : ℝ)^6261 := by
    have hnat : (2632637103 : ℕ)^8309*100000000000000^6261 ≤ 42687095276249^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632637103 5000000000 42687095276249 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344858603/10000000000 : ℝ), (-2244441421/10000000000 : ℝ), (2632637103/5000000000 : ℝ)] ![(43545470699741/100000000000000 : ℝ), (2753486803901/20000000000000 : ℝ), (42687095276249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344858603/10000000000 : ℝ)|^8309 ≤ (43545470699741/100000000000000 : ℝ)^6261
        have hw : |(5344858603/10000000000 : ℝ)|=(5344858603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2244441421/10000000000 : ℝ)|^8309 ≤ (2753486803901/20000000000000 : ℝ)^6261
        have hw : |(-2244441421/10000000000 : ℝ)|=(2244441421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632637103/5000000000 : ℝ)|^8309 ≤ (42687095276249/100000000000000 : ℝ)^6261
        have hw : |(2632637103/5000000000 : ℝ)|=(2632637103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s7_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672429303/5000000000 : ℝ)*x 0 + (164539819/312500000 : ℝ)*x 1 + (-2244441413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672429303/5000000000 : ℝ)^8309 ≤ (43545470732177/100000000000000 : ℝ)^6261 := by
    have hnat : (2672429303 : ℕ)^8309*100000000000000^6261 ≤ 43545470732177^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672429303 5000000000 43545470732177 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164539819/312500000 : ℝ)^8309 ≤ (42687095297767/100000000000000 : ℝ)^6261 := by
    have hnat : (164539819 : ℕ)^8309*100000000000000^6261 ≤ 42687095297767^6261*312500000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164539819 312500000 42687095297767 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244441413/10000000000 : ℝ)^8309 ≤ (13767433954381/100000000000000 : ℝ)^6261 := by
    have hnat : (2244441413 : ℕ)^8309*100000000000000^6261 ≤ 13767433954381^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244441413 10000000000 13767433954381 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672429303/5000000000 : ℝ), (164539819/312500000 : ℝ), (-2244441413/10000000000 : ℝ)] ![(43545470732177/100000000000000 : ℝ), (42687095297767/100000000000000 : ℝ), (13767433954381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672429303/5000000000 : ℝ)|^8309 ≤ (43545470732177/100000000000000 : ℝ)^6261
        have hw : |(2672429303/5000000000 : ℝ)|=(2672429303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164539819/312500000 : ℝ)|^8309 ≤ (42687095297767/100000000000000 : ℝ)^6261
        have hw : |(164539819/312500000 : ℝ)|=(164539819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2244441413/10000000000 : ℝ)|^8309 ≤ (13767433954381/100000000000000 : ℝ)^6261
        have hw : |(-2244441413/10000000000 : ℝ)|=(2244441413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s7_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368346909/10000000000 : ℝ)*x 0 + (2121626117/5000000000 : ℝ)*x 1 + (1124283701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368346909/10000000000 : ℝ)^8309 ≤ (8329200443677/25000000000000 : ℝ)^6261 := by
    have hnat : (4368346909 : ℕ)^8309*25000000000000^6261 ≤ 8329200443677^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368346909 10000000000 8329200443677 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121626117/5000000000 : ℝ)^8309 ≤ (4007075776759/12500000000000 : ℝ)^6261 := by
    have hnat : (2121626117 : ℕ)^8309*12500000000000^6261 ≤ 4007075776759^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121626117 5000000000 4007075776759 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124283701/2500000000 : ℝ)^8309 ≤ (270520249951/781250000000 : ℝ)^6261 := by
    have hnat : (1124283701 : ℕ)^8309*781250000000^6261 ≤ 270520249951^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124283701 2500000000 270520249951 781250000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368346909/10000000000 : ℝ), (2121626117/5000000000 : ℝ), (1124283701/2500000000 : ℝ)] ![(8329200443677/25000000000000 : ℝ), (4007075776759/12500000000000 : ℝ), (270520249951/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368346909/10000000000 : ℝ)|^8309 ≤ (8329200443677/25000000000000 : ℝ)^6261
        have hw : |(4368346909/10000000000 : ℝ)|=(4368346909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121626117/5000000000 : ℝ)|^8309 ≤ (4007075776759/12500000000000 : ℝ)^6261
        have hw : |(2121626117/5000000000 : ℝ)|=(2121626117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124283701/2500000000 : ℝ)|^8309 ≤ (270520249951/781250000000 : ℝ)^6261
        have hw : |(1124283701/2500000000 : ℝ)|=(1124283701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s7_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089690031/5000000000 : ℝ)*x 0 + (1053119263/2000000000 : ℝ)*x 1 + (674152207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089690031/5000000000 : ℝ)^8309 ≤ (6620165559771/50000000000000 : ℝ)^6261 := by
    have hnat : (1089690031 : ℕ)^8309*50000000000000^6261 ≤ 6620165559771^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089690031 5000000000 6620165559771 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053119263/2000000000 : ℝ)^8309 ≤ (2134528047577/5000000000000 : ℝ)^6261 := by
    have hnat : (1053119263 : ℕ)^8309*5000000000000^6261 ≤ 2134528047577^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053119263 2000000000 2134528047577 5000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674152207/1250000000 : ℝ)^8309 ≤ (22034553955033/50000000000000 : ℝ)^6261 := by
    have hnat : (674152207 : ℕ)^8309*50000000000000^6261 ≤ 22034553955033^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674152207 1250000000 22034553955033 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089690031/5000000000 : ℝ), (1053119263/2000000000 : ℝ), (674152207/1250000000 : ℝ)] ![(6620165559771/50000000000000 : ℝ), (2134528047577/5000000000000 : ℝ), (22034553955033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089690031/5000000000 : ℝ)|^8309 ≤ (6620165559771/50000000000000 : ℝ)^6261
        have hw : |(-1089690031/5000000000 : ℝ)|=(1089690031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053119263/2000000000 : ℝ)|^8309 ≤ (2134528047577/5000000000000 : ℝ)^6261
        have hw : |(1053119263/2000000000 : ℝ)|=(1053119263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674152207/1250000000 : ℝ)|^8309 ≤ (22034553955033/50000000000000 : ℝ)^6261
        have hw : |(674152207/1250000000 : ℝ)|=(674152207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s7_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312424877/10000000000 : ℝ)*x 0 + (-211649797/1000000000 : ℝ)*x 1 + (2696608827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312424877/10000000000 : ℝ)^8309 ≤ (1079878527337/2500000000000 : ℝ)^6261 := by
    have hnat : (5312424877 : ℕ)^8309*2500000000000^6261 ≤ 1079878527337^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312424877 10000000000 1079878527337 2500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211649797/1000000000 : ℝ)^8309 ≤ (1273575100399/10000000000000 : ℝ)^6261 := by
    have hnat : (211649797 : ℕ)^8309*10000000000000^6261 ≤ 1273575100399^6261*1000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211649797 1000000000 1273575100399 10000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696608827/5000000000 : ℝ)^8309 ≤ (44069107888377/100000000000000 : ℝ)^6261 := by
    have hnat : (2696608827 : ℕ)^8309*100000000000000^6261 ≤ 44069107888377^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696608827 5000000000 44069107888377 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312424877/10000000000 : ℝ), (-211649797/1000000000 : ℝ), (2696608827/5000000000 : ℝ)] ![(1079878527337/2500000000000 : ℝ), (1273575100399/10000000000000 : ℝ), (44069107888377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312424877/10000000000 : ℝ)|^8309 ≤ (1079878527337/2500000000000 : ℝ)^6261
        have hw : |(5312424877/10000000000 : ℝ)|=(5312424877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211649797/1000000000 : ℝ)|^8309 ≤ (1273575100399/10000000000000 : ℝ)^6261
        have hw : |(-211649797/1000000000 : ℝ)|=(211649797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696608827/5000000000 : ℝ)|^8309 ≤ (44069107888377/100000000000000 : ℝ)^6261
        have hw : |(2696608827/5000000000 : ℝ)|=(2696608827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s7_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328106219/2500000000 : ℝ)*x 0 + (674152207/1250000000 : ℝ)*x 1 + (-2116497969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328106219/2500000000 : ℝ)^8309 ≤ (43195141082689/100000000000000 : ℝ)^6261 := by
    have hnat : (1328106219 : ℕ)^8309*100000000000000^6261 ≤ 43195141082689^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328106219 2500000000 43195141082689 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674152207/1250000000 : ℝ)^8309 ≤ (22034553955033/50000000000000 : ℝ)^6261 := by
    have hnat : (674152207 : ℕ)^8309*50000000000000^6261 ≤ 22034553955033^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674152207 1250000000 22034553955033 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116497969/10000000000 : ℝ)^8309 ≤ (2547150199201/20000000000000 : ℝ)^6261 := by
    have hnat : (2116497969 : ℕ)^8309*20000000000000^6261 ≤ 2547150199201^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116497969 10000000000 2547150199201 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328106219/2500000000 : ℝ), (674152207/1250000000 : ℝ), (-2116497969/10000000000 : ℝ)] ![(43195141082689/100000000000000 : ℝ), (22034553955033/50000000000000 : ℝ), (2547150199201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328106219/2500000000 : ℝ)|^8309 ≤ (43195141082689/100000000000000 : ℝ)^6261
        have hw : |(1328106219/2500000000 : ℝ)|=(1328106219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674152207/1250000000 : ℝ)|^8309 ≤ (22034553955033/50000000000000 : ℝ)^6261
        have hw : |(674152207/1250000000 : ℝ)|=(674152207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2116497969/10000000000 : ℝ)|^8309 ≤ (2547150199201/20000000000000 : ℝ)^6261
        have hw : |(-2116497969/10000000000 : ℝ)|=(2116497969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s7_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546044589/1250000000 : ℝ)*x 0 + (281031079/625000000 : ℝ)*x 1 + (2121946041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546044589/1250000000 : ℝ)^8309 ≤ (16658450498631/50000000000000 : ℝ)^6261 := by
    have hnat : (546044589 : ℕ)^8309*50000000000000^6261 ≤ 16658450498631^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546044589 1250000000 16658450498631 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281031079/625000000 : ℝ)^8309 ≤ (34620077566051/100000000000000 : ℝ)^6261 := by
    have hnat : (281031079 : ℕ)^8309*100000000000000^6261 ≤ 34620077566051^6261*625000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281031079 625000000 34620077566051 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121946041/5000000000 : ℝ)^8309 ≤ (32063021429959/100000000000000 : ℝ)^6261 := by
    have hnat : (2121946041 : ℕ)^8309*100000000000000^6261 ≤ 32063021429959^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121946041 5000000000 32063021429959 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546044589/1250000000 : ℝ), (281031079/625000000 : ℝ), (2121946041/5000000000 : ℝ)] ![(16658450498631/50000000000000 : ℝ), (34620077566051/100000000000000 : ℝ), (32063021429959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546044589/1250000000 : ℝ)|^8309 ≤ (16658450498631/50000000000000 : ℝ)^6261
        have hw : |(546044589/1250000000 : ℝ)|=(546044589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281031079/625000000 : ℝ)|^8309 ≤ (34620077566051/100000000000000 : ℝ)^6261
        have hw : |(281031079/625000000 : ℝ)|=(281031079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121946041/5000000000 : ℝ)|^8309 ≤ (32063021429959/100000000000000 : ℝ)^6261
        have hw : |(2121946041/5000000000 : ℝ)|=(2121946041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2807/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11311/100000 : ℝ) ^ (2077/512 : ℝ) ≤ (1446750745282017/10000000000000000000 : ℝ) := by
    have hpowers : (11311/100000 : ℝ)^2077 ≤ (1446750745282017/10000000000000000000 : ℝ)^512 := by
      have hnat : (11311 : ℕ)^2077*10000000000000000000^512 ≤ 1446750745282017^512*100000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11311 100000 1446750745282017 10000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11311/100000 : ℝ)) (X := (1446750745282017/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14043/100000 : ℝ) ^ (2077/512 : ℝ) ≤ (34797751233716191/100000000000000000000 : ℝ) := by
    have hpowers : (14043/100000 : ℝ)^2077 ≤ (34797751233716191/100000000000000000000 : ℝ)^512 := by
      have hnat : (14043 : ℕ)^2077*100000000000000000000^512 ≤ 34797751233716191^512*100000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14043 100000 34797751233716191 100000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14043/100000 : ℝ)) (X := (34797751233716191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001446750745282017/5000000000000000000 : ℝ) ≤ (10000713197541257/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (5001446750745282017/5000000000000000000 : ℝ)^512 ≤ (10000713197541257/10000000000000000 : ℝ)^2077 := by
      have hnat : (5001446750745282017 : ℕ)^512*10000000000000000^2077 ≤ 10000713197541257^2077*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001446750745282017 5000000000000000000 10000713197541257 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000713197541257/10000000000000000 : ℝ)) (X := (5001446750745282017/5000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049265258686536361/100000000000000000000 : ℝ) ≤ (125015177619247/125000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (100049265258686536361/100000000000000000000 : ℝ)^512 ≤ (125015177619247/125000000000000 : ℝ)^2077 := by
      have hnat : (100049265258686536361 : ℕ)^512*125000000000000^2077 ≤ 125015177619247^2077*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049265258686536361 100000000000000000000 125015177619247 125000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125015177619247/125000000000000 : ℝ)) (X := (100049265258686536361/100000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034797751233716191/50000000000000000000 : ℝ) ≤ (10001715221538263/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50034797751233716191/50000000000000000000 : ℝ)^512 ≤ (10001715221538263/10000000000000000 : ℝ)^2077 := by
      have hnat : (50034797751233716191 : ℕ)^512*10000000000000000^2077 ≤ 10001715221538263^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034797751233716191 50000000000000000000 10001715221538263 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001715221538263/10000000000000000 : ℝ)) (X := (50034797751233716191/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1446750745282017/10000000000000000000 : ℝ) ≤ ((13655307281126289629/13660000000000000000 : ℝ)+2*(501011998503/273200000000000 : ℝ)*(11311/100000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (13655307281126289629/13660000000000000000 : ℝ)+2*(501011998503/273200000000000 : ℝ)*(11311/100000 : ℝ)=(10000713197541257/10000000000000000 : ℝ) by norm_num, show 1+2*(1446750745282017/10000000000000000000 : ℝ)=(5001446750745282017/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34797751233716191/100000000000000000000 : ℝ)+(1446750745282017/10000000000000000000 : ℝ) ≤ ((13655307281126289629/13660000000000000000 : ℝ)+(501011998503/273200000000000 : ℝ)*((14043/100000 : ℝ)+(11311/100000 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (13655307281126289629/13660000000000000000 : ℝ)+(501011998503/273200000000000 : ℝ)*((14043/100000 : ℝ)+(11311/100000 : ℝ))=(125015177619247/125000000000000 : ℝ) by norm_num, show 1+(34797751233716191/100000000000000000000 : ℝ)+(1446750745282017/10000000000000000000 : ℝ)=(100049265258686536361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34797751233716191/100000000000000000000 : ℝ) ≤ ((13655307281126289629/13660000000000000000 : ℝ)+2*(501011998503/273200000000000 : ℝ)*(14043/100000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (13655307281126289629/13660000000000000000 : ℝ)+2*(501011998503/273200000000000 : ℝ)*(14043/100000 : ℝ)=(10001715221538263/10000000000000000 : ℝ) by norm_num, show 1+2*(34797751233716191/100000000000000000000 : ℝ)=(50034797751233716191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13655307281126289629/13660000000000000000 : ℝ)*(X 1 0+X 2 0)+(501011998503/273200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (13655307281126289629/13660000000000000000 : ℝ)) (alpha := (501011998503/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13655307281126289629/13660000000000000000 : ℝ)*(X 0 1+X 2 1)+(501011998503/273200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (13655307281126289629/13660000000000000000 : ℝ)) (alpha := (501011998503/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13655307281126289629/13660000000000000000 : ℝ)*(X 0 2+X 1 2)+(501011998503/273200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (13655307281126289629/13660000000000000000 : ℝ)) (alpha := (501011998503/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1089687559/5000000000 : ℝ)*X 0 0+(5393540931/10000000000 : ℝ)*X 0 1+(1316318549/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344858603/10000000000 : ℝ)*X 1 0+(-2244441421/10000000000 : ℝ)*X 1 1+(2632637103/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672429303/5000000000 : ℝ)*X 2 0+(164539819/312500000 : ℝ)*X 2 1+(-2244441413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368346909/10000000000 : ℝ)*X 0 0+(2121626117/5000000000 : ℝ)*X 0 1+(1124283701/2500000000 : ℝ)*X 0 2+(4368346909/10000000000 : ℝ)*X 1 0+(2121626117/5000000000 : ℝ)*X 1 1+(1124283701/2500000000 : ℝ)*X 1 2+(4368346909/10000000000 : ℝ)*X 2 0+(2121626117/5000000000 : ℝ)*X 2 1+(1124283701/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089690031/5000000000 : ℝ)*X 0 0+(1053119263/2000000000 : ℝ)*X 0 1+(674152207/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312424877/10000000000 : ℝ)*X 1 0+(-211649797/1000000000 : ℝ)*X 1 1+(2696608827/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328106219/2500000000 : ℝ)*X 2 0+(674152207/1250000000 : ℝ)*X 2 1+(-2116497969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546044589/1250000000 : ℝ)*X 0 0+(281031079/625000000 : ℝ)*X 0 1+(2121946041/5000000000 : ℝ)*X 0 2+(546044589/1250000000 : ℝ)*X 1 0+(281031079/625000000 : ℝ)*X 1 1+(2121946041/5000000000 : ℝ)*X 1 2+(546044589/1250000000 : ℝ)*X 2 0+(281031079/625000000 : ℝ)*X 2 1+(2121946041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4225202123724181260039594939/683000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1240210953/100000000000000 : ℝ)*(base19) + (146391521/12500000000000 : ℝ)*(base23) + (2453783/6250000000000 : ℝ)*(lower2) + (150276909/100000000000000 : ℝ)*(upper3) + (108425567/100000000000000 : ℝ)*(upper5) + (5867593749716797/100000000000000 : ℝ)*(major0) + (5867593749716797/100000000000000 : ℝ)*(major1) + (5867593749716797/100000000000000 : ℝ)*(major2) + (974536132744379/12500000000000 : ℝ)*(sp0) + (7796322581261641/100000000000000 : ℝ)*(sp1) + (7796322650340427/100000000000000 : ℝ)*(sp2) + (24617784320017/625000000000 : ℝ)*(sp3) + (17379758781/50000000000000 : ℝ)*(sp4) + (3596110051/20000000000000 : ℝ)*(sp7) + (1969431735876487/50000000000000 : ℝ)*(f.failure) + (1559264764294519/20000000000000 : ℝ)*(f.sum) + (21896454042309/13660000000000000000000000000 : ℝ)*base66 + (16593045476240748313/1366000000000000000000000000000000 : ℝ)*base67 + (17248237310751251687/1366000000000000000000000000000000 : ℝ)*base70 + (19816362972834748313/1366000000000000000000000000000000 : ℝ)*base71 + (27819996768151/13660000000000000000000000000 : ℝ)*base73 + (7101730148083251687/1366000000000000000000000000000000 : ℝ)*base76 + (23332731975639251687/1366000000000000000000000000000000 : ℝ)*base78 + (6744255843563251687/1366000000000000000000000000000000 : ℝ)*base80 + (1700744918151/13660000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (5031171/500000000000000000000 : ℝ)*base90 + (5031171/500000000000000000000 : ℝ)*base92 + (5031171/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (307435468377126036997660911/42687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1315865461/100000000000000 : ℝ)*(base19) + (1432101671/100000000000000 : ℝ)*(base23) + (71705059/50000000000000 : ℝ)*(upper3) + (53410029/100000000000000 : ℝ)*(lower4) + (146296577/100000000000000 : ℝ)*(upper5) + (737151593272753/12500000000000 : ℝ)*(major0) + (737151593272753/12500000000000 : ℝ)*(major1) + (737151593272753/12500000000000 : ℝ)*(major2) + (36048217517/100000000000000 : ℝ)*(sp1) + (4857634049/12500000000000 : ℝ)*(sp2) + (783567881178009/10000000000000 : ℝ)*(sp4) + (979455180962139/12500000000000 : ℝ)*(sp5) + (1958909629651507/25000000000000 : ℝ)*(sp6) + (1979373220258607/50000000000000 : ℝ)*(sp7) + (1979373220258607/50000000000000 : ℝ)*(f.failure) + (783567881178009/10000000000000 : ℝ)*(f.sum) + (808084511751/1707500000000000000000000000 : ℝ)*base66 + (1532459094644371363/170750000000000000000000000000000 : ℝ)*base68 + (1207094584090871363/170750000000000000000000000000000 : ℝ)*base70 + (525390280742878637/170750000000000000000000000000000 : ℝ)*base71 + (10995785522067/3415000000000000000000000000 : ℝ)*base74 + (258307304323371363/170750000000000000000000000000000 : ℝ)*base76 + (167573682685871363/170750000000000000000000000000000 : ℝ)*base78 + (685834074489871363/170750000000000000000000000000000 : ℝ)*base80 + (221554389141/1707500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2362869/500000000000000000000 : ℝ)*base89 + (2362869/500000000000000000000 : ℝ)*base91 + (2362869/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1116_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1116_s8_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179383989/10000000000 : ℝ)*x 0 + (5393462673/10000000000 : ℝ)*x 1 + (210613857/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179383989/10000000000 : ℝ)^8309 ≤ (13240362781077/100000000000000 : ℝ)^6261 := by
    have hnat : (2179383989 : ℕ)^8309*100000000000000^6261 ≤ 13240362781077^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179383989 10000000000 13240362781077 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393462673/10000000000 : ℝ)^8309 ≤ (22035882452761/50000000000000 : ℝ)^6261 := by
    have hnat : (5393462673 : ℕ)^8309*50000000000000^6261 ≤ 22035882452761^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393462673 10000000000 22035882452761 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210613857/400000000 : ℝ)^8309 ≤ (21343936148941/50000000000000 : ℝ)^6261 := by
    have hnat : (210613857 : ℕ)^8309*50000000000000^6261 ≤ 21343936148941^6261*400000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210613857 400000000 21343936148941 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179383989/10000000000 : ℝ), (5393462673/10000000000 : ℝ), (210613857/400000000 : ℝ)] ![(13240362781077/100000000000000 : ℝ), (22035882452761/50000000000000 : ℝ), (21343936148941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179383989/10000000000 : ℝ)|^8309 ≤ (13240362781077/100000000000000 : ℝ)^6261
        have hw : |(-2179383989/10000000000 : ℝ)|=(2179383989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393462673/10000000000 : ℝ)|^8309 ≤ (22035882452761/50000000000000 : ℝ)^6261
        have hw : |(5393462673/10000000000 : ℝ)|=(5393462673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210613857/400000000 : ℝ)|^8309 ≤ (21343936148941/50000000000000 : ℝ)^6261
        have hw : |(210613857/400000000 : ℝ)|=(210613857/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s8_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336209583/2500000000 : ℝ)*x 0 + (-1122186423/5000000000 : ℝ)*x 1 + (263267323/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336209583/2500000000 : ℝ)^8309 ≤ (5443156440863/12500000000000 : ℝ)^6261 := by
    have hnat : (1336209583 : ℕ)^8309*12500000000000^6261 ≤ 5443156440863^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336209583 2500000000 5443156440863 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122186423/5000000000 : ℝ)^8309 ≤ (13766875789173/100000000000000 : ℝ)^6261 := by
    have hnat : (1122186423 : ℕ)^8309*100000000000000^6261 ≤ 13766875789173^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122186423 5000000000 13766875789173 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263267323/500000000 : ℝ)^8309 ≤ (5335984084307/12500000000000 : ℝ)^6261 := by
    have hnat : (263267323 : ℕ)^8309*12500000000000^6261 ≤ 5335984084307^6261*500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263267323 500000000 5335984084307 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336209583/2500000000 : ℝ), (-1122186423/5000000000 : ℝ), (263267323/500000000 : ℝ)] ![(5443156440863/12500000000000 : ℝ), (13766875789173/100000000000000 : ℝ), (5335984084307/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336209583/2500000000 : ℝ)|^8309 ≤ (5443156440863/12500000000000 : ℝ)^6261
        have hw : |(1336209583/2500000000 : ℝ)|=(1336209583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122186423/5000000000 : ℝ)|^8309 ≤ (13766875789173/100000000000000 : ℝ)^6261
        have hw : |(-1122186423/5000000000 : ℝ)|=(1122186423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263267323/500000000 : ℝ)|^8309 ≤ (5335984084307/12500000000000 : ℝ)^6261
        have hw : |(263267323/500000000 : ℝ)|=(263267323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s8_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672419177/5000000000 : ℝ)*x 0 + (5265346437/10000000000 : ℝ)*x 1 + (-1122186423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672419177/5000000000 : ℝ)^8309 ≤ (43545251764771/100000000000000 : ℝ)^6261 := by
    have hnat : (2672419177 : ℕ)^8309*100000000000000^6261 ≤ 43545251764771^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672419177 5000000000 43545251764771 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265346437/10000000000 : ℝ)^8309 ≤ (42687872426993/100000000000000 : ℝ)^6261 := by
    have hnat : (5265346437 : ℕ)^8309*100000000000000^6261 ≤ 42687872426993^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265346437 10000000000 42687872426993 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122186423/5000000000 : ℝ)^8309 ≤ (13766875789173/100000000000000 : ℝ)^6261 := by
    have hnat : (1122186423 : ℕ)^8309*100000000000000^6261 ≤ 13766875789173^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122186423 5000000000 13766875789173 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672419177/5000000000 : ℝ), (5265346437/10000000000 : ℝ), (-1122186423/5000000000 : ℝ)] ![(43545251764771/100000000000000 : ℝ), (42687872426993/100000000000000 : ℝ), (13766875789173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672419177/5000000000 : ℝ)|^8309 ≤ (43545251764771/100000000000000 : ℝ)^6261
        have hw : |(2672419177/5000000000 : ℝ)|=(2672419177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265346437/10000000000 : ℝ)|^8309 ≤ (42687872426993/100000000000000 : ℝ)^6261
        have hw : |(5265346437/10000000000 : ℝ)|=(5265346437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122186423/5000000000 : ℝ)|^8309 ≤ (13766875789173/100000000000000 : ℝ)^6261
        have hw : |(-1122186423/5000000000 : ℝ)|=(1122186423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s8_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092087691/2500000000 : ℝ)*x 0 + (1060850163/2500000000 : ℝ)*x 1 + (56212317/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092087691/2500000000 : ℝ)^8309 ≤ (8329210198417/25000000000000 : ℝ)^6261 := by
    have hnat : (1092087691 : ℕ)^8309*25000000000000^6261 ≤ 8329210198417^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092087691 2500000000 8329210198417 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060850163/2500000000 : ℝ)^8309 ≤ (16029047123957/50000000000000 : ℝ)^6261 := by
    have hnat : (1060850163 : ℕ)^8309*50000000000000^6261 ≤ 16029047123957^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060850163 2500000000 16029047123957 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56212317/125000000 : ℝ)^8309 ≤ (8656266234381/25000000000000 : ℝ)^6261 := by
    have hnat : (56212317 : ℕ)^8309*25000000000000^6261 ≤ 8656266234381^6261*125000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56212317 125000000 8656266234381 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092087691/2500000000 : ℝ), (1060850163/2500000000 : ℝ), (56212317/125000000 : ℝ)] ![(8329210198417/25000000000000 : ℝ), (16029047123957/50000000000000 : ℝ), (8656266234381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092087691/2500000000 : ℝ)|^8309 ≤ (8329210198417/25000000000000 : ℝ)^6261
        have hw : |(1092087691/2500000000 : ℝ)|=(1092087691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060850163/2500000000 : ℝ)|^8309 ≤ (16029047123957/50000000000000 : ℝ)^6261
        have hw : |(1060850163/2500000000 : ℝ)|=(1060850163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56212317/125000000 : ℝ)|^8309 ≤ (8656266234381/25000000000000 : ℝ)^6261
        have hw : |(56212317/125000000 : ℝ)|=(56212317/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s8_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-544847309/2500000000 : ℝ)*x 0 + (210626717/400000000 : ℝ)*x 1 + (674142473/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544847309/2500000000 : ℝ)^8309 ≤ (13240405085173/100000000000000 : ℝ)^6261 := by
    have hnat : (544847309 : ℕ)^8309*100000000000000^6261 ≤ 13240405085173^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544847309 2500000000 13240405085173 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210626717/400000000 : ℝ)^8309 ≤ (21345665718099/50000000000000 : ℝ)^6261 := by
    have hnat : (210626717 : ℕ)^8309*50000000000000^6261 ≤ 21345665718099^6261*400000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210626717 400000000 21345665718099 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674142473/1250000000 : ℝ)^8309 ≤ (44068263464479/100000000000000 : ℝ)^6261 := by
    have hnat : (674142473 : ℕ)^8309*100000000000000^6261 ≤ 44068263464479^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674142473 1250000000 44068263464479 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544847309/2500000000 : ℝ), (210626717/400000000 : ℝ), (674142473/1250000000 : ℝ)] ![(13240405085173/100000000000000 : ℝ), (21345665718099/50000000000000 : ℝ), (44068263464479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544847309/2500000000 : ℝ)|^8309 ≤ (13240405085173/100000000000000 : ℝ)^6261
        have hw : |(-544847309/2500000000 : ℝ)|=(544847309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210626717/400000000 : ℝ)|^8309 ≤ (21345665718099/50000000000000 : ℝ)^6261
        have hw : |(210626717/400000000 : ℝ)|=(210626717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674142473/1250000000 : ℝ)|^8309 ≤ (44068263464479/100000000000000 : ℝ)^6261
        have hw : |(674142473/1250000000 : ℝ)|=(674142473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s8_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312442757/10000000000 : ℝ)*x 0 + (-1058289583/5000000000 : ℝ)*x 1 + (1348285017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312442757/10000000000 : ℝ)^8309 ≤ (8639066806041/20000000000000 : ℝ)^6261 := by
    have hnat : (5312442757 : ℕ)^8309*20000000000000^6261 ≤ 8639066806041^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312442757 10000000000 8639066806041 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058289583/5000000000 : ℝ)^8309 ≤ (3184099853279/25000000000000 : ℝ)^6261 := by
    have hnat : (1058289583 : ℕ)^8309*25000000000000^6261 ≤ 3184099853279^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058289583 5000000000 3184099853279 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348285017/2500000000 : ℝ)^8309 ≤ (22034133272087/50000000000000 : ℝ)^6261 := by
    have hnat : (1348285017 : ℕ)^8309*50000000000000^6261 ≤ 22034133272087^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348285017 2500000000 22034133272087 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312442757/10000000000 : ℝ), (-1058289583/5000000000 : ℝ), (1348285017/2500000000 : ℝ)] ![(8639066806041/20000000000000 : ℝ), (3184099853279/25000000000000 : ℝ), (22034133272087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312442757/10000000000 : ℝ)|^8309 ≤ (8639066806041/20000000000000 : ℝ)^6261
        have hw : |(5312442757/10000000000 : ℝ)|=(5312442757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058289583/5000000000 : ℝ)|^8309 ≤ (3184099853279/25000000000000 : ℝ)^6261
        have hw : |(-1058289583/5000000000 : ℝ)|=(1058289583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348285017/2500000000 : ℝ)|^8309 ≤ (22034133272087/50000000000000 : ℝ)^6261
        have hw : |(1348285017/2500000000 : ℝ)|=(1348285017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s8_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062488539/2000000000 : ℝ)*x 0 + (1348285053/2500000000 : ℝ)*x 1 + (-423315811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062488539/2000000000 : ℝ)^8309 ≤ (8639066672237/20000000000000 : ℝ)^6261 := by
    have hnat : (1062488539 : ℕ)^8309*20000000000000^6261 ≤ 8639066672237^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062488539 2000000000 8639066672237 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348285053/2500000000 : ℝ)^8309 ≤ (44068268105709/100000000000000 : ℝ)^6261 := by
    have hnat : (1348285053 : ℕ)^8309*100000000000000^6261 ≤ 44068268105709^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348285053 2500000000 44068268105709 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423315811/2000000000 : ℝ)^8309 ≤ (2547279705339/20000000000000 : ℝ)^6261 := by
    have hnat : (423315811 : ℕ)^8309*20000000000000^6261 ≤ 2547279705339^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423315811 2000000000 2547279705339 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062488539/2000000000 : ℝ), (1348285053/2500000000 : ℝ), (-423315811/2000000000 : ℝ)] ![(8639066672237/20000000000000 : ℝ), (44068268105709/100000000000000 : ℝ), (2547279705339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062488539/2000000000 : ℝ)|^8309 ≤ (8639066672237/20000000000000 : ℝ)^6261
        have hw : |(1062488539/2000000000 : ℝ)|=(1062488539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348285053/2500000000 : ℝ)|^8309 ≤ (44068268105709/100000000000000 : ℝ)^6261
        have hw : |(1348285053/2500000000 : ℝ)|=(1348285053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423315811/2000000000 : ℝ)|^8309 ≤ (2547279705339/20000000000000 : ℝ)^6261
        have hw : |(-423315811/2000000000 : ℝ)|=(423315811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s8_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368360679/10000000000 : ℝ)*x 0 + (4496349141/10000000000 : ℝ)*x 1 + (2122019513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368360679/10000000000 : ℝ)^8309 ≤ (8329235287469/25000000000000 : ℝ)^6261 := by
    have hnat : (4368360679 : ℕ)^8309*25000000000000^6261 ≤ 8329235287469^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368360679 10000000000 8329235287469 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496349141/10000000000 : ℝ)^8309 ≤ (17309282039137/50000000000000 : ℝ)^6261 := by
    have hnat : (4496349141 : ℕ)^8309*50000000000000^6261 ≤ 17309282039137^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496349141 10000000000 17309282039137 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122019513/5000000000 : ℝ)^8309 ≤ (16032247379053/50000000000000 : ℝ)^6261 := by
    have hnat : (2122019513 : ℕ)^8309*50000000000000^6261 ≤ 16032247379053^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122019513 5000000000 16032247379053 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368360679/10000000000 : ℝ), (4496349141/10000000000 : ℝ), (2122019513/5000000000 : ℝ)] ![(8329235287469/25000000000000 : ℝ), (17309282039137/50000000000000 : ℝ), (16032247379053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368360679/10000000000 : ℝ)|^8309 ≤ (8329235287469/25000000000000 : ℝ)^6261
        have hw : |(4368360679/10000000000 : ℝ)|=(4368360679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496349141/10000000000 : ℝ)|^8309 ≤ (17309282039137/50000000000000 : ℝ)^6261
        have hw : |(4496349141/10000000000 : ℝ)|=(4496349141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122019513/5000000000 : ℝ)|^8309 ≤ (16032247379053/50000000000000 : ℝ)^6261
        have hw : |(2122019513/5000000000 : ℝ)|=(2122019513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (283/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14033/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5659/50000 : ℝ) ^ (2077/512 : ℝ) ≤ (3625965694533191/25000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^2077 ≤ (3625965694533191/25000000000000000000 : ℝ)^512 := by
      have hnat : (5659 : ℕ)^2077*25000000000000000000^512 ≤ 3625965694533191^512*50000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 3625965694533191 25000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (3625965694533191/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2807/20000 : ℝ) ^ (2077/512 : ℝ) ≤ (17358702116498427/50000000000000000000 : ℝ) := by
    have hpowers : (2807/20000 : ℝ)^2077 ≤ (17358702116498427/50000000000000000000 : ℝ)^512 := by
      have hnat : (2807 : ℕ)^2077*50000000000000000000^512 ≤ 17358702116498427^512*20000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 20000 17358702116498427 50000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/20000 : ℝ)) (X := (17358702116498427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503625965694533191/12500000000000000000 : ℝ) ≤ (10000714989535887/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (12503625965694533191/12500000000000000000 : ℝ)^512 ≤ (10000714989535887/10000000000000000 : ℝ)^2077 := by
      have hnat : (12503625965694533191 : ℕ)^512*10000000000000000^2077 ≤ 10000714989535887^2077*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503625965694533191 12500000000000000000 10000714989535887 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000714989535887/10000000000000000 : ℝ)) (X := (12503625965694533191/12500000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024610633505564809/50000000000000000000 : ℝ) ≤ (10001213125505859/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50024610633505564809/50000000000000000000 : ℝ)^512 ≤ (10001213125505859/10000000000000000 : ℝ)^2077 := by
      have hnat : (50024610633505564809 : ℕ)^512*10000000000000000^2077 ≤ 10001213125505859^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024610633505564809 50000000000000000000 10001213125505859 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001213125505859/10000000000000000 : ℝ)) (X := (50024610633505564809/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017358702116498427/25000000000000000000 : ℝ) ≤ (10001711261475831/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (25017358702116498427/25000000000000000000 : ℝ)^512 ≤ (10001711261475831/10000000000000000 : ℝ)^2077 := by
      have hnat : (25017358702116498427 : ℕ)^512*10000000000000000^2077 ≤ 10001711261475831^2077*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017358702116498427 25000000000000000000 10001711261475831 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001711261475831/10000000000000000 : ℝ)) (X := (25017358702116498427/25000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3625965694533191/25000000000000000000 : ℝ) ≤ ((27160666820752718787/27170000000000000000 : ℝ)+2*(124533992493/67925000000000 : ℝ)*(5659/50000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (27160666820752718787/27170000000000000000 : ℝ)+2*(124533992493/67925000000000 : ℝ)*(5659/50000 : ℝ)=(10000714989535887/10000000000000000 : ℝ) by norm_num, show 1+2*(3625965694533191/25000000000000000000 : ℝ)=(12503625965694533191/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17358702116498427/50000000000000000000 : ℝ)+(3625965694533191/25000000000000000000 : ℝ) ≤ ((27160666820752718787/27170000000000000000 : ℝ)+(124533992493/67925000000000 : ℝ)*((2807/20000 : ℝ)+(5659/50000 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (27160666820752718787/27170000000000000000 : ℝ)+(124533992493/67925000000000 : ℝ)*((2807/20000 : ℝ)+(5659/50000 : ℝ))=(10001213125505859/10000000000000000 : ℝ) by norm_num, show 1+(17358702116498427/50000000000000000000 : ℝ)+(3625965694533191/25000000000000000000 : ℝ)=(50024610633505564809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17358702116498427/50000000000000000000 : ℝ) ≤ ((27160666820752718787/27170000000000000000 : ℝ)+2*(124533992493/67925000000000 : ℝ)*(2807/20000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (27160666820752718787/27170000000000000000 : ℝ)+2*(124533992493/67925000000000 : ℝ)*(2807/20000 : ℝ)=(10001711261475831/10000000000000000 : ℝ) by norm_num, show 1+2*(17358702116498427/50000000000000000000 : ℝ)=(25017358702116498427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27160666820752718787/27170000000000000000 : ℝ)*(X 1 0+X 2 0)+(124533992493/67925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (27160666820752718787/27170000000000000000 : ℝ)) (alpha := (124533992493/67925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27160666820752718787/27170000000000000000 : ℝ)*(X 0 1+X 2 1)+(124533992493/67925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (27160666820752718787/27170000000000000000 : ℝ)) (alpha := (124533992493/67925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27160666820752718787/27170000000000000000 : ℝ)*(X 0 2+X 1 2)+(124533992493/67925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (27160666820752718787/27170000000000000000 : ℝ)) (alpha := (124533992493/67925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2179383989/10000000000 : ℝ)*X 0 0+(5393462673/10000000000 : ℝ)*X 0 1+(210613857/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336209583/2500000000 : ℝ)*X 1 0+(-1122186423/5000000000 : ℝ)*X 1 1+(263267323/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672419177/5000000000 : ℝ)*X 2 0+(5265346437/10000000000 : ℝ)*X 2 1+(-1122186423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092087691/2500000000 : ℝ)*X 0 0+(1060850163/2500000000 : ℝ)*X 0 1+(56212317/125000000 : ℝ)*X 0 2+(1092087691/2500000000 : ℝ)*X 1 0+(1060850163/2500000000 : ℝ)*X 1 1+(56212317/125000000 : ℝ)*X 1 2+(1092087691/2500000000 : ℝ)*X 2 0+(1060850163/2500000000 : ℝ)*X 2 1+(56212317/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-544847309/2500000000 : ℝ)*X 0 0+(210626717/400000000 : ℝ)*X 0 1+(674142473/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312442757/10000000000 : ℝ)*X 1 0+(-1058289583/5000000000 : ℝ)*X 1 1+(1348285017/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062488539/2000000000 : ℝ)*X 2 0+(1348285053/2500000000 : ℝ)*X 2 1+(-423315811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368360679/10000000000 : ℝ)*X 0 0+(4496349141/10000000000 : ℝ)*X 0 1+(2122019513/5000000000 : ℝ)*X 0 2+(4368360679/10000000000 : ℝ)*X 1 0+(4496349141/10000000000 : ℝ)*X 1 1+(2122019513/5000000000 : ℝ)*X 1 2+(4368360679/10000000000 : ℝ)*X 2 0+(4496349141/10000000000 : ℝ)*X 2 1+(2122019513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11665666271835225381156303/6175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101578611/25000000000000 : ℝ)*(base19) + (25147447/6250000000000 : ℝ)*(base23) + (19285999/100000000000000 : ℝ)*(lower2) + (58462731/100000000000000 : ℝ)*(upper3) + (36907303/100000000000000 : ℝ)*(upper5) + (587445195864747/10000000000000 : ℝ)*(major0) + (587445195864747/10000000000000 : ℝ)*(major1) + (587445195864747/10000000000000 : ℝ)*(major2) + (3902711955657457/50000000000000 : ℝ)*(sp0) + (1951359030406789/25000000000000 : ℝ)*(sp1) + (7805436125582449/100000000000000 : ℝ)*(sp2) + (1971730483532499/50000000000000 : ℝ)*(sp3) + (6308313343/50000000000000 : ℝ)*(sp4) + (254372631/4000000000000 : ℝ)*(sp7) + (1971733663190387/50000000000000 : ℝ)*(f.failure) + (9756795659927/125000000000 : ℝ)*(f.sum) + (416525195103/247000000000000000000000000 : ℝ)*base65 + (291423938498472899/24700000000000000000000000000000 : ℝ)*base67 + (118556370108227101/24700000000000000000000000000000 : ℝ)*base70 + (338067817502272899/24700000000000000000000000000000 : ℝ)*base71 + (1170402258523/247000000000000000000000000 : ℝ)*base73 + (235574705587572899/24700000000000000000000000000000 : ℝ)*base75 + (179901240198472899/24700000000000000000000000000000 : ℝ)*base77 + (63802754735772899/24700000000000000000000000000000 : ℝ)*base79 + (113547193623/30875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2740129/500000000000000000000 : ℝ)*base89 + (2740129/500000000000000000000 : ℝ)*base91 + (2740129/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13107713107325804950909887/7718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212528621/20000000000000 : ℝ)*(base19) + (722632967/50000000000000 : ℝ)*(base23) + (193176733/50000000000000 : ℝ)*(lower1) + (168574257/100000000000000 : ℝ)*(upper2) + (325984249/100000000000000 : ℝ)*(upper3) + (65647937/100000000000000 : ℝ)*(upper5) + (369005823829313/6250000000000 : ℝ)*(major0) + (369005823829313/6250000000000 : ℝ)*(major1) + (369005823829313/6250000000000 : ℝ)*(major2) + (2572252443/10000000000000 : ℝ)*(sp2) + (7844821090566521/100000000000000 : ℝ)*(sp4) + (980602503490427/12500000000000 : ℝ)*(sp5) + (1568958784555231/20000000000000 : ℝ)*(sp6) + (3963365215365967/100000000000000 : ℝ)*(sp7) + (3963365215365967/100000000000000 : ℝ)*(f.failure) + (7844821090566521/100000000000000 : ℝ)*(f.sum) + (5127750219921/1235000000000000000000000000 : ℝ)*base65 + (69620279156682121/15437500000000000000000000000000 : ℝ)*base67 + (524502349249442879/15437500000000000000000000000000 : ℝ)*base70 + (123995997934744621/15437500000000000000000000000000 : ℝ)*base71 + (1471706502769/1235000000000000000000000000 : ℝ)*base74 + (249119900719942879/15437500000000000000000000000000 : ℝ)*base76 + (203714815175307121/15437500000000000000000000000000 : ℝ)*base77 + (337574186924494621/15437500000000000000000000000000 : ℝ)*base79 + (69715624932079/1235000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base88 + (13531989/1000000000000000000000 : ℝ)*base89 + (13531989/1000000000000000000000 : ℝ)*base91 + (13531989/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1116_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1116_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1116_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1116_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1116_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1116_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
