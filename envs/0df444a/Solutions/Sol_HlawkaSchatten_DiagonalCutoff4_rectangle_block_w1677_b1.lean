-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1677_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:55.948916+00:00
-- url     : https://prove2.me/submissions/f970b371-51d7-41e5-b421-1bc3c770b6d4

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
theorem support_rectangle_w1677_s3_0 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-77042973/500000000 : ℝ)*x 0 + (5492228883/10000000000 : ℝ)*x 1 + (1026542481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77042973/500000000 : ℝ)^5039 ≤ (1912657441461/20000000000000 : ℝ)^4015 := by
    have hnat : (77042973 : ℕ)^5039*20000000000000^4015 ≤ 1912657441461^4015*500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77042973 500000000 1912657441461 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492228883/10000000000 : ℝ)^5039 ≤ (11784555145149/25000000000000 : ℝ)^4015 := by
    have hnat : (5492228883 : ℕ)^5039*25000000000000^4015 ≤ 11784555145149^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492228883 10000000000 11784555145149 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026542481/2000000000 : ℝ)^5039 ≤ (10824623049379/25000000000000 : ℝ)^4015 := by
    have hnat : (1026542481 : ℕ)^5039*25000000000000^4015 ≤ 10824623049379^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026542481 2000000000 10824623049379 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77042973/500000000 : ℝ), (5492228883/10000000000 : ℝ), (1026542481/2000000000 : ℝ)] ![(1912657441461/20000000000000 : ℝ), (11784555145149/25000000000000 : ℝ), (10824623049379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77042973/500000000 : ℝ)|^5039 ≤ (1912657441461/20000000000000 : ℝ)^4015
        have hw : |(-77042973/500000000 : ℝ)|=(77042973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492228883/10000000000 : ℝ)|^5039 ≤ (11784555145149/25000000000000 : ℝ)^4015
        have hw : |(5492228883/10000000000 : ℝ)|=(5492228883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026542481/2000000000 : ℝ)|^5039 ≤ (10824623049379/25000000000000 : ℝ)^4015
        have hw : |(1026542481/2000000000 : ℝ)|=(1026542481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s3_1 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070907671/2000000000 : ℝ)*x 0 + (-1727843743/10000000000 : ℝ)*x 1 + (5132712509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070907671/2000000000 : ℝ)^5039 ≤ (2282991700553/5000000000000 : ℝ)^4015 := by
    have hnat : (1070907671 : ℕ)^5039*5000000000000^4015 ≤ 2282991700553^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070907671 2000000000 2282991700553 5000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1727843743/10000000000 : ℝ)^5039 ≤ (11041672675513/100000000000000 : ℝ)^4015 := by
    have hnat : (1727843743 : ℕ)^5039*100000000000000^4015 ≤ 11041672675513^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727843743 10000000000 11041672675513 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132712509/10000000000 : ℝ)^5039 ≤ (21649246649297/50000000000000 : ℝ)^4015 := by
    have hnat : (5132712509 : ℕ)^5039*50000000000000^4015 ≤ 21649246649297^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132712509 10000000000 21649246649297 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070907671/2000000000 : ℝ), (-1727843743/10000000000 : ℝ), (5132712509/10000000000 : ℝ)] ![(2282991700553/5000000000000 : ℝ), (11041672675513/100000000000000 : ℝ), (21649246649297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070907671/2000000000 : ℝ)|^5039 ≤ (2282991700553/5000000000000 : ℝ)^4015
        have hw : |(1070907671/2000000000 : ℝ)|=(1070907671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1727843743/10000000000 : ℝ)|^5039 ≤ (11041672675513/100000000000000 : ℝ)^4015
        have hw : |(-1727843743/10000000000 : ℝ)|=(1727843743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132712509/10000000000 : ℝ)|^5039 ≤ (21649246649297/50000000000000 : ℝ)^4015
        have hw : |(5132712509/10000000000 : ℝ)|=(5132712509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s3_2 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267726913/500000000 : ℝ)*x 0 + (5132712637/10000000000 : ℝ)*x 1 + (-1727843701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267726913/500000000 : ℝ)^5039 ≤ (11414958248589/25000000000000 : ℝ)^4015 := by
    have hnat : (267726913 : ℕ)^5039*25000000000000^4015 ≤ 11414958248589^4015*500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267726913 500000000 11414958248589 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132712637/10000000000 : ℝ)^5039 ≤ (21649247326883/50000000000000 : ℝ)^4015 := by
    have hnat : (5132712637 : ℕ)^5039*50000000000000^4015 ≤ 21649247326883^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132712637 10000000000 21649247326883 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727843701/10000000000 : ℝ)^5039 ≤ (5520836169331/50000000000000 : ℝ)^4015 := by
    have hnat : (1727843701 : ℕ)^5039*50000000000000^4015 ≤ 5520836169331^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727843701 10000000000 5520836169331 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267726913/500000000 : ℝ), (5132712637/10000000000 : ℝ), (-1727843701/10000000000 : ℝ)] ![(11414958248589/25000000000000 : ℝ), (21649247326883/50000000000000 : ℝ), (5520836169331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267726913/500000000 : ℝ)|^5039 ≤ (11414958248589/25000000000000 : ℝ)^4015
        have hw : |(267726913/500000000 : ℝ)|=(267726913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132712637/10000000000 : ℝ)|^5039 ≤ (21649247326883/50000000000000 : ℝ)^4015
        have hw : |(5132712637/10000000000 : ℝ)|=(5132712637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727843701/10000000000 : ℝ)|^5039 ≤ (5520836169331/50000000000000 : ℝ)^4015
        have hw : |(-1727843701/10000000000 : ℝ)|=(1727843701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s3_3 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4149457729/10000000000 : ℝ)*x 0 + (1843363533/5000000000 : ℝ)*x 1 + (2325474653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4149457729/10000000000 : ℝ)^5039 ≤ (33156027197213/100000000000000 : ℝ)^4015 := by
    have hnat : (4149457729 : ℕ)^5039*100000000000000^4015 ≤ 33156027197213^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149457729 10000000000 33156027197213 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1843363533/5000000000 : ℝ)^5039 ≤ (14291754743379/50000000000000 : ℝ)^4015 := by
    have hnat : (1843363533 : ℕ)^5039*50000000000000^4015 ≤ 14291754743379^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843363533 5000000000 14291754743379 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2325474653/5000000000 : ℝ)^5039 ≤ (38260463299149/100000000000000 : ℝ)^4015 := by
    have hnat : (2325474653 : ℕ)^5039*100000000000000^4015 ≤ 38260463299149^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325474653 5000000000 38260463299149 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4149457729/10000000000 : ℝ), (1843363533/5000000000 : ℝ), (2325474653/5000000000 : ℝ)] ![(33156027197213/100000000000000 : ℝ), (14291754743379/50000000000000 : ℝ), (38260463299149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4149457729/10000000000 : ℝ)|^5039 ≤ (33156027197213/100000000000000 : ℝ)^4015
        have hw : |(4149457729/10000000000 : ℝ)|=(4149457729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1843363533/5000000000 : ℝ)|^5039 ≤ (14291754743379/50000000000000 : ℝ)^4015
        have hw : |(1843363533/5000000000 : ℝ)|=(1843363533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2325474653/5000000000 : ℝ)|^5039 ≤ (38260463299149/100000000000000 : ℝ)^4015
        have hw : |(2325474653/5000000000 : ℝ)|=(2325474653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s3_4 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-308206047/2000000000 : ℝ)*x 0 + (2568290891/5000000000 : ℝ)*x 1 + (1372075381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (308206047/2000000000 : ℝ)^5039 ≤ (9564617457743/100000000000000 : ℝ)^4015 := by
    have hnat : (308206047 : ℕ)^5039*100000000000000^4015 ≤ 9564617457743^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308206047 2000000000 9564617457743 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568290891/5000000000 : ℝ)^5039 ≤ (8667892467309/20000000000000 : ℝ)^4015 := by
    have hnat : (2568290891 : ℕ)^5039*20000000000000^4015 ≤ 8667892467309^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568290891 5000000000 8667892467309 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372075381/2500000000 : ℝ)^5039 ≤ (47095920192091/100000000000000 : ℝ)^4015 := by
    have hnat : (1372075381 : ℕ)^5039*100000000000000^4015 ≤ 47095920192091^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372075381 2500000000 47095920192091 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-308206047/2000000000 : ℝ), (2568290891/5000000000 : ℝ), (1372075381/2500000000 : ℝ)] ![(9564617457743/100000000000000 : ℝ), (8667892467309/20000000000000 : ℝ), (47095920192091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-308206047/2000000000 : ℝ)|^5039 ≤ (9564617457743/100000000000000 : ℝ)^4015
        have hw : |(-308206047/2000000000 : ℝ)|=(308206047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568290891/5000000000 : ℝ)|^5039 ≤ (8667892467309/20000000000000 : ℝ)^4015
        have hw : |(2568290891/5000000000 : ℝ)|=(2568290891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372075381/2500000000 : ℝ)|^5039 ≤ (47095920192091/100000000000000 : ℝ)^4015
        have hw : |(1372075381/2500000000 : ℝ)|=(1372075381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s3_5 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258583771/10000000000 : ℝ)*x 0 + (-686126987/5000000000 : ℝ)*x 1 + (5488301991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258583771/10000000000 : ℝ)^5039 ≤ (5579408845051/12500000000000 : ℝ)^4015 := by
    have hnat : (5258583771 : ℕ)^5039*12500000000000^4015 ≤ 5579408845051^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258583771 10000000000 5579408845051 12500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686126987/5000000000 : ℝ)^5039 ≤ (413440199949/5000000000000 : ℝ)^4015 := by
    have hnat : (686126987 : ℕ)^5039*5000000000000^4015 ≤ 413440199949^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686126987 5000000000 413440199949 5000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488301991/10000000000 : ℝ)^5039 ≤ (47095925221547/100000000000000 : ℝ)^4015 := by
    have hnat : (5488301991 : ℕ)^5039*100000000000000^4015 ≤ 47095925221547^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488301991 10000000000 47095925221547 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258583771/10000000000 : ℝ), (-686126987/5000000000 : ℝ), (5488301991/10000000000 : ℝ)] ![(5579408845051/12500000000000 : ℝ), (413440199949/5000000000000 : ℝ), (47095925221547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258583771/10000000000 : ℝ)|^5039 ≤ (5579408845051/12500000000000 : ℝ)^4015
        have hw : |(5258583771/10000000000 : ℝ)|=(5258583771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-686126987/5000000000 : ℝ)|^5039 ≤ (413440199949/5000000000000 : ℝ)^4015
        have hw : |(-686126987/5000000000 : ℝ)|=(686126987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488301991/10000000000 : ℝ)|^5039 ≤ (47095925221547/100000000000000 : ℝ)^4015
        have hw : |(5488301991/10000000000 : ℝ)|=(5488301991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s3_6 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131464593/250000000 : ℝ)*x 0 + (5488301569/10000000000 : ℝ)*x 1 + (-171531831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131464593/250000000 : ℝ)^5039 ≤ (4463527021711/10000000000000 : ℝ)^4015 := by
    have hnat : (131464593 : ℕ)^5039*10000000000000^4015 ≤ 4463527021711^4015*250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131464593 250000000 4463527021711 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488301569/10000000000 : ℝ)^5039 ≤ (5886990084591/12500000000000 : ℝ)^4015 := by
    have hnat : (5488301569 : ℕ)^5039*12500000000000^4015 ≤ 5886990084591^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488301569 10000000000 5886990084591 12500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171531831/1250000000 : ℝ)^5039 ≤ (2067202274031/25000000000000 : ℝ)^4015 := by
    have hnat : (171531831 : ℕ)^5039*25000000000000^4015 ≤ 2067202274031^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171531831 1250000000 2067202274031 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131464593/250000000 : ℝ), (5488301569/10000000000 : ℝ), (-171531831/1250000000 : ℝ)] ![(4463527021711/10000000000000 : ℝ), (5886990084591/12500000000000 : ℝ), (2067202274031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131464593/250000000 : ℝ)|^5039 ≤ (4463527021711/10000000000000 : ℝ)^4015
        have hw : |(131464593/250000000 : ℝ)|=(131464593/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488301569/10000000000 : ℝ)|^5039 ≤ (5886990084591/12500000000000 : ℝ)^4015
        have hw : |(5488301569/10000000000 : ℝ)|=(5488301569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171531831/1250000000 : ℝ)|^5039 ≤ (2067202274031/25000000000000 : ℝ)^4015
        have hw : |(-171531831/1250000000 : ℝ)|=(171531831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s3_7 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2074957277/5000000000 : ℝ)*x 0 + (2320286291/5000000000 : ℝ)*x 1 + (1848629729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074957277/5000000000 : ℝ)^5039 ≤ (64766813413/195312500000 : ℝ)^4015 := by
    have hnat : (2074957277 : ℕ)^5039*195312500000^4015 ≤ 64766813413^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074957277 5000000000 64766813413 195312500000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320286291/5000000000 : ℝ)^5039 ≤ (3815335970519/10000000000000 : ℝ)^4015 := by
    have hnat : (2320286291 : ℕ)^5039*10000000000000^4015 ≤ 3815335970519^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320286291 5000000000 3815335970519 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1848629729/5000000000 : ℝ)^5039 ≤ (28686031815671/100000000000000 : ℝ)^4015 := by
    have hnat : (1848629729 : ℕ)^5039*100000000000000^4015 ≤ 28686031815671^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848629729 5000000000 28686031815671 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2074957277/5000000000 : ℝ), (2320286291/5000000000 : ℝ), (1848629729/5000000000 : ℝ)] ![(64766813413/195312500000 : ℝ), (3815335970519/10000000000000 : ℝ), (28686031815671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2074957277/5000000000 : ℝ)|^5039 ≤ (64766813413/195312500000 : ℝ)^4015
        have hw : |(2074957277/5000000000 : ℝ)|=(2074957277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2320286291/5000000000 : ℝ)|^5039 ≤ (3815335970519/10000000000000 : ℝ)^4015
        have hw : |(2320286291/5000000000 : ℝ)|=(2320286291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1848629729/5000000000 : ℝ)|^5039 ≤ (28686031815671/100000000000000 : ℝ)^4015
        have hw : |(1848629729/5000000000 : ℝ)|=(1848629729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1677_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17363/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9691/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1083/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17363/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17363/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17363/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17363/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17363/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17363/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9661/100000 : ℝ) ^ (5031/1024 : ℝ) ≤ (103116049124791/10000000000000000000 : ℝ) := by
    have hpowers : (9661/100000 : ℝ)^5031 ≤ (103116049124791/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9661 : ℕ)^5031*10000000000000000000^1024 ≤ 103116049124791^1024*100000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9661 100000 103116049124791 10000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9661/100000 : ℝ)) (X := (103116049124791/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17363/100000 : ℝ) ^ (5031/1024 : ℝ) ≤ (18374313708690747/100000000000000000000 : ℝ) := by
    have hpowers : (17363/100000 : ℝ)^5031 ≤ (18374313708690747/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17363 : ℕ)^5031*100000000000000000000^1024 ≤ 18374313708690747^1024*100000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17363 100000 18374313708690747 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17363/100000 : ℝ)) (X := (18374313708690747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000103116049124791/5000000000000000000 : ℝ) ≤ (10000041975737277/10000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (5000103116049124791/5000000000000000000 : ℝ)^1024 ≤ (10000041975737277/10000000000000000 : ℝ)^5031 := by
      have hnat : (5000103116049124791 : ℕ)^1024*10000000000000000^5031 ≤ 10000041975737277^5031*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000103116049124791 5000000000000000000 10000041975737277 10000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000041975737277/10000000000000000 : ℝ)) (X := (5000103116049124791/5000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019405474199938657/100000000000000000000 : ℝ) ≤ (500019747237269/500000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (100019405474199938657/100000000000000000000 : ℝ)^1024 ≤ (500019747237269/500000000000000 : ℝ)^5031 := by
      have hnat : (100019405474199938657 : ℕ)^1024*500000000000000^5031 ≤ 500019747237269^5031*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019405474199938657 100000000000000000000 500019747237269 500000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500019747237269/500000000000000 : ℝ)) (X := (100019405474199938657/100000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018374313708690747/50000000000000000000 : ℝ) ≤ (10000747913753483/10000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50018374313708690747/50000000000000000000 : ℝ)^1024 ≤ (10000747913753483/10000000000000000 : ℝ)^5031 := by
      have hnat : (50018374313708690747 : ℕ)^1024*10000000000000000^5031 ≤ 10000747913753483^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018374313708690747 50000000000000000000 10000747913753483 10000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000747913753483/10000000000000000 : ℝ)) (X := (50018374313708690747/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103116049124791/10000000000000000000 : ℝ) ≤ ((9626687903744242661/9627500000000000000 : ℝ)+2*(352969008103/770200000000000 : ℝ)*(9661/100000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (9626687903744242661/9627500000000000000 : ℝ)+2*(352969008103/770200000000000 : ℝ)*(9661/100000 : ℝ)=(10000041975737277/10000000000000000 : ℝ) by norm_num, show 1+2*(103116049124791/10000000000000000000 : ℝ)=(5000103116049124791/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18374313708690747/100000000000000000000 : ℝ)+(103116049124791/10000000000000000000 : ℝ) ≤ ((9626687903744242661/9627500000000000000 : ℝ)+(352969008103/770200000000000 : ℝ)*((17363/100000 : ℝ)+(9661/100000 : ℝ)))^(5031/1024 : ℝ) := by
    rw [show (9626687903744242661/9627500000000000000 : ℝ)+(352969008103/770200000000000 : ℝ)*((17363/100000 : ℝ)+(9661/100000 : ℝ))=(500019747237269/500000000000000 : ℝ) by norm_num, show 1+(18374313708690747/100000000000000000000 : ℝ)+(103116049124791/10000000000000000000 : ℝ)=(100019405474199938657/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18374313708690747/100000000000000000000 : ℝ) ≤ ((9626687903744242661/9627500000000000000 : ℝ)+2*(352969008103/770200000000000 : ℝ)*(17363/100000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (9626687903744242661/9627500000000000000 : ℝ)+2*(352969008103/770200000000000 : ℝ)*(17363/100000 : ℝ)=(10000747913753483/10000000000000000 : ℝ) by norm_num, show 1+2*(18374313708690747/100000000000000000000 : ℝ)=(50018374313708690747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9626687903744242661/9627500000000000000 : ℝ)*(X 1 0+X 2 0)+(352969008103/770200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (9661/100000 : ℝ)) (hi := (17363/100000 : ℝ)) (c := (9626687903744242661/9627500000000000000 : ℝ)) (alpha := (352969008103/770200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9626687903744242661/9627500000000000000 : ℝ)*(X 0 1+X 2 1)+(352969008103/770200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (9661/100000 : ℝ)) (hi := (17363/100000 : ℝ)) (c := (9626687903744242661/9627500000000000000 : ℝ)) (alpha := (352969008103/770200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9626687903744242661/9627500000000000000 : ℝ)*(X 0 2+X 1 2)+(352969008103/770200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (9661/100000 : ℝ)) (hi := (17363/100000 : ℝ)) (c := (9626687903744242661/9627500000000000000 : ℝ)) (alpha := (352969008103/770200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-77042973/500000000 : ℝ)*X 0 0+(5492228883/10000000000 : ℝ)*X 0 1+(1026542481/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070907671/2000000000 : ℝ)*X 1 0+(-1727843743/10000000000 : ℝ)*X 1 1+(5132712509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267726913/500000000 : ℝ)*X 2 0+(5132712637/10000000000 : ℝ)*X 2 1+(-1727843701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4149457729/10000000000 : ℝ)*X 0 0+(1843363533/5000000000 : ℝ)*X 0 1+(2325474653/5000000000 : ℝ)*X 0 2+(4149457729/10000000000 : ℝ)*X 1 0+(1843363533/5000000000 : ℝ)*X 1 1+(2325474653/5000000000 : ℝ)*X 1 2+(4149457729/10000000000 : ℝ)*X 2 0+(1843363533/5000000000 : ℝ)*X 2 1+(2325474653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-308206047/2000000000 : ℝ)*X 0 0+(2568290891/5000000000 : ℝ)*X 0 1+(1372075381/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258583771/10000000000 : ℝ)*X 1 0+(-686126987/5000000000 : ℝ)*X 1 1+(5488301991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((131464593/250000000 : ℝ)*X 2 0+(5488301569/10000000000 : ℝ)*X 2 1+(-171531831/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2074957277/5000000000 : ℝ)*X 0 0+(2320286291/5000000000 : ℝ)*X 0 1+(1848629729/5000000000 : ℝ)*X 0 2+(2074957277/5000000000 : ℝ)*X 1 0+(2320286291/5000000000 : ℝ)*X 1 1+(1848629729/5000000000 : ℝ)*X 1 2+(2074957277/5000000000 : ℝ)*X 2 0+(2320286291/5000000000 : ℝ)*X 2 1+(1848629729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1557027003029028324507056961/481375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (208042027/50000000000000 : ℝ)*(base19) + (317362293/100000000000000 : ℝ)*(base23) + (26436477/100000000000000 : ℝ)*(lower2) + (31457673/50000000000000 : ℝ)*(upper3) + (22219451/50000000000000 : ℝ)*(upper5) + (1909315776143767/100000000000000 : ℝ)*(major0) + (1909315776143767/100000000000000 : ℝ)*(major1) + (1909315776143767/100000000000000 : ℝ)*(major2) + (695379619900771/25000000000000 : ℝ)*(sp0) + (1390761401525027/50000000000000 : ℝ)*(sp1) + (1390761450885907/50000000000000 : ℝ)*(sp2) + (129638335040233/12500000000000 : ℝ)*(sp3) + (4739531023/100000000000000 : ℝ)*(sp4) + (772506767/50000000000000 : ℝ)*(sp7) + (518554112667699/50000000000000 : ℝ)*(f.failure) + (2781523219134107/100000000000000 : ℝ)*(f.sum) + (95277561521969/38510000000000000000000000000 : ℝ)*base66 + (2722455851846843513/962750000000000000000000000000000 : ℝ)*base68 + (6377771911563656487/962750000000000000000000000000000 : ℝ)*base69 + (1786651194869843513/962750000000000000000000000000000 : ℝ)*base72 + (31267144042101/38510000000000000000000000000 : ℝ)*base73 + (3461234071764843513/962750000000000000000000000000000 : ℝ)*base76 + (6335435517862343513/962750000000000000000000000000000 : ℝ)*base78 + (48420135313156487/962750000000000000000000000000000 : ℝ)*base79 + (231222476403581/38510000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6829291/1000000000000000000000 : ℝ)*base90 + (6829291/1000000000000000000000 : ℝ)*base92 + (6829291/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1386539979666774911085787251/120343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (453513497/25000000000000 : ℝ)*(base19) + (919045289/50000000000000 : ℝ)*(base23) + (56046457/10000000000000 : ℝ)*(lower1) + (7159469/12500000000000 : ℝ)*(upper2) + (27907941/10000000000000 : ℝ)*(upper3) + (5542579/3125000000000 : ℝ)*(upper5) + (487905247592451/25000000000000 : ℝ)*(major0) + (487905247592451/25000000000000 : ℝ)*(major1) + (487905247592451/25000000000000 : ℝ)*(major2) + (3140635197/100000000000000 : ℝ)*(sp1) + (1421576945164737/50000000000000 : ℝ)*(sp4) + (2843148935640289/100000000000000 : ℝ)*(sp5) + (177697003264931/6250000000000 : ℝ)*(sp6) + (530043853180139/50000000000000 : ℝ)*(sp7) + (530043853180139/50000000000000 : ℝ)*(f.failure) + (1421576945164737/50000000000000 : ℝ)*(f.sum) + (1890819114397/601718750000000000000000000 : ℝ)*base66 + (200389647527414611/240687500000000000000000000000000 : ℝ)*base67 + (9094294662664611/240687500000000000000000000000000 : ℝ)*base69 + (609756651339789611/240687500000000000000000000000000 : ℝ)*base71 + (52994399399539/19255000000000000000000000000 : ℝ)*base74 + (2461753762419164611/240687500000000000000000000000000 : ℝ)*base75 + (747491910623164611/240687500000000000000000000000000 : ℝ)*base77 + (19011120292664611/240687500000000000000000000000000 : ℝ)*base79 + (179100914687163/9627500000000000000000000000 : ℝ)*base81 + (641251/1000000000000000000000 : ℝ)*base90 + (641251/1000000000000000000000 : ℝ)*base92 + (641251/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1677_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17363/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9691/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1083/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1677_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1677_s4_0 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-770442189/5000000000 : ℝ)*x 0 + (2746067343/5000000000 : ℝ)*x 1 + (513278991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770442189/5000000000 : ℝ)^5039 ≤ (1912696260703/20000000000000 : ℝ)^4015 := by
    have hnat : (770442189 : ℕ)^5039*20000000000000^4015 ≤ 1912696260703^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770442189 5000000000 1912696260703 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746067343/5000000000 : ℝ)^5039 ≤ (2946075370191/6250000000000 : ℝ)^4015 := by
    have hnat : (2746067343 : ℕ)^5039*6250000000000^4015 ≤ 2946075370191^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746067343 5000000000 2946075370191 6250000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513278991/1000000000 : ℝ)^5039 ≤ (43299312766709/100000000000000 : ℝ)^4015 := by
    have hnat : (513278991 : ℕ)^5039*100000000000000^4015 ≤ 43299312766709^4015*1000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513278991 1000000000 43299312766709 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-770442189/5000000000 : ℝ), (2746067343/5000000000 : ℝ), (513278991/1000000000 : ℝ)] ![(1912696260703/20000000000000 : ℝ), (2946075370191/6250000000000 : ℝ), (43299312766709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-770442189/5000000000 : ℝ)|^5039 ≤ (1912696260703/20000000000000 : ℝ)^4015
        have hw : |(-770442189/5000000000 : ℝ)|=(770442189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746067343/5000000000 : ℝ)|^5039 ≤ (2946075370191/6250000000000 : ℝ)^4015
        have hw : |(2746067343/5000000000 : ℝ)|=(2746067343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513278991/1000000000 : ℝ)|^5039 ≤ (43299312766709/100000000000000 : ℝ)^4015
        have hw : |(513278991/1000000000 : ℝ)|=(513278991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s4_1 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354513003/10000000000 : ℝ)*x 0 + (-863888071/5000000000 : ℝ)*x 1 + (2566394673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354513003/10000000000 : ℝ)^5039 ≤ (22829781345137/50000000000000 : ℝ)^4015 := by
    have hnat : (5354513003 : ℕ)^5039*50000000000000^4015 ≤ 22829781345137^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354513003 10000000000 22829781345137 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (863888071/5000000000 : ℝ)^5039 ≤ (11041130499667/100000000000000 : ℝ)^4015 := by
    have hnat : (863888071 : ℕ)^5039*100000000000000^4015 ≤ 11041130499667^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863888071 5000000000 11041130499667 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566394673/5000000000 : ℝ)^5039 ≤ (43299306795457/100000000000000 : ℝ)^4015 := by
    have hnat : (2566394673 : ℕ)^5039*100000000000000^4015 ≤ 43299306795457^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566394673 5000000000 43299306795457 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354513003/10000000000 : ℝ), (-863888071/5000000000 : ℝ), (2566394673/5000000000 : ℝ)] ![(22829781345137/50000000000000 : ℝ), (11041130499667/100000000000000 : ℝ), (43299306795457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354513003/10000000000 : ℝ)|^5039 ≤ (22829781345137/50000000000000 : ℝ)^4015
        have hw : |(5354513003/10000000000 : ℝ)|=(5354513003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-863888071/5000000000 : ℝ)|^5039 ≤ (11041130499667/100000000000000 : ℝ)^4015
        have hw : |(-863888071/5000000000 : ℝ)|=(863888071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566394673/5000000000 : ℝ)|^5039 ≤ (43299306795457/100000000000000 : ℝ)^4015
        have hw : |(2566394673/5000000000 : ℝ)|=(2566394673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s4_2 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354512283/10000000000 : ℝ)*x 0 + (1026557977/2000000000 : ℝ)*x 1 + (-215972049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354512283/10000000000 : ℝ)^5039 ≤ (22829777492367/50000000000000 : ℝ)^4015 := by
    have hnat : (5354512283 : ℕ)^5039*50000000000000^4015 ≤ 22829777492367^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354512283 10000000000 22829777492367 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026557977/2000000000 : ℝ)^5039 ≤ (21649656251013/50000000000000 : ℝ)^4015 := by
    have hnat : (1026557977 : ℕ)^5039*50000000000000^4015 ≤ 21649656251013^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026557977 2000000000 21649656251013 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215972049/1250000000 : ℝ)^5039 ≤ (2208226500943/20000000000000 : ℝ)^4015 := by
    have hnat : (215972049 : ℕ)^5039*20000000000000^4015 ≤ 2208226500943^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215972049 1250000000 2208226500943 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354512283/10000000000 : ℝ), (1026557977/2000000000 : ℝ), (-215972049/1250000000 : ℝ)] ![(22829777492367/50000000000000 : ℝ), (21649656251013/50000000000000 : ℝ), (2208226500943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354512283/10000000000 : ℝ)|^5039 ≤ (22829777492367/50000000000000 : ℝ)^4015
        have hw : |(5354512283/10000000000 : ℝ)|=(5354512283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026557977/2000000000 : ℝ)|^5039 ≤ (21649656251013/50000000000000 : ℝ)^4015
        have hw : |(1026557977/2000000000 : ℝ)|=(1026557977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215972049/1250000000 : ℝ)|^5039 ≤ (2208226500943/20000000000000 : ℝ)^4015
        have hw : |(-215972049/1250000000 : ℝ)|=(215972049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s4_3 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2074737457/5000000000 : ℝ)*x 0 + (1843477733/5000000000 : ℝ)*x 1 + (581339669/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074737457/5000000000 : ℝ)^5039 ≤ (8289049883671/25000000000000 : ℝ)^4015 := by
    have hnat : (2074737457 : ℕ)^5039*25000000000000^4015 ≤ 8289049883671^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074737457 5000000000 8289049883671 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1843477733/5000000000 : ℝ)^5039 ≤ (28585731941381/100000000000000 : ℝ)^4015 := by
    have hnat : (1843477733 : ℕ)^5039*100000000000000^4015 ≤ 28585731941381^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843477733 5000000000 28585731941381 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (581339669/1250000000 : ℝ)^5039 ≤ (7651613702827/20000000000000 : ℝ)^4015 := by
    have hnat : (581339669 : ℕ)^5039*20000000000000^4015 ≤ 7651613702827^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581339669 1250000000 7651613702827 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2074737457/5000000000 : ℝ), (1843477733/5000000000 : ℝ), (581339669/1250000000 : ℝ)] ![(8289049883671/25000000000000 : ℝ), (28585731941381/100000000000000 : ℝ), (7651613702827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2074737457/5000000000 : ℝ)|^5039 ≤ (8289049883671/25000000000000 : ℝ)^4015
        have hw : |(2074737457/5000000000 : ℝ)|=(2074737457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1843477733/5000000000 : ℝ)|^5039 ≤ (28585731941381/100000000000000 : ℝ)^4015
        have hw : |(1843477733/5000000000 : ℝ)|=(1843477733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(581339669/1250000000 : ℝ)|^5039 ≤ (7651613702827/20000000000000 : ℝ)^4015
        have hw : |(581339669/1250000000 : ℝ)|=(581339669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s4_4 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-770527451/5000000000 : ℝ)*x 0 + (5136654979/10000000000 : ℝ)*x 1 + (21438327/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770527451/5000000000 : ℝ)^5039 ≤ (9564809604241/100000000000000 : ℝ)^4015 := by
    have hnat : (770527451 : ℕ)^5039*100000000000000^4015 ≤ 9564809604241^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770527451 5000000000 9564809604241 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136654979/10000000000 : ℝ)^5039 ≤ (2708764840281/6250000000000 : ℝ)^4015 := by
    have hnat : (5136654979 : ℕ)^5039*6250000000000^4015 ≤ 2708764840281^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136654979 10000000000 2708764840281 6250000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21438327/39062500 : ℝ)^5039 ≤ (47094952944641/100000000000000 : ℝ)^4015 := by
    have hnat : (21438327 : ℕ)^5039*100000000000000^4015 ≤ 47094952944641^4015*39062500^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21438327 39062500 47094952944641 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-770527451/5000000000 : ℝ), (5136654979/10000000000 : ℝ), (21438327/39062500 : ℝ)] ![(9564809604241/100000000000000 : ℝ), (2708764840281/6250000000000 : ℝ), (47094952944641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-770527451/5000000000 : ℝ)|^5039 ≤ (9564809604241/100000000000000 : ℝ)^4015
        have hw : |(-770527451/5000000000 : ℝ)|=(770527451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136654979/10000000000 : ℝ)|^5039 ≤ (2708764840281/6250000000000 : ℝ)^4015
        have hw : |(5136654979/10000000000 : ℝ)|=(5136654979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21438327/39062500 : ℝ)|^5039 ≤ (47094952944641/100000000000000 : ℝ)^4015
        have hw : |(21438327/39062500 : ℝ)|=(21438327/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s4_5 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258603977/10000000000 : ℝ)*x 0 + (-343088557/2500000000 : ℝ)*x 1 + (2744105803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258603977/10000000000 : ℝ)^5039 ≤ (44635486013177/100000000000000 : ℝ)^4015 := by
    have hnat : (5258603977 : ℕ)^5039*100000000000000^4015 ≤ 44635486013177^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258603977 10000000000 44635486013177 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343088557/2500000000 : ℝ)^5039 ≤ (8269562179749/100000000000000 : ℝ)^4015 := by
    have hnat : (343088557 : ℕ)^5039*100000000000000^4015 ≤ 8269562179749^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343088557 2500000000 8269562179749 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744105803/5000000000 : ℝ)^5039 ≤ (2943434487691/6250000000000 : ℝ)^4015 := by
    have hnat : (2744105803 : ℕ)^5039*6250000000000^4015 ≤ 2943434487691^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744105803 5000000000 2943434487691 6250000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258603977/10000000000 : ℝ), (-343088557/2500000000 : ℝ), (2744105803/5000000000 : ℝ)] ![(44635486013177/100000000000000 : ℝ), (8269562179749/100000000000000 : ℝ), (2943434487691/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258603977/10000000000 : ℝ)|^5039 ≤ (44635486013177/100000000000000 : ℝ)^4015
        have hw : |(5258603977/10000000000 : ℝ)|=(5258603977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343088557/2500000000 : ℝ)|^5039 ≤ (8269562179749/100000000000000 : ℝ)^4015
        have hw : |(-343088557/2500000000 : ℝ)|=(343088557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744105803/5000000000 : ℝ)|^5039 ≤ (2943434487691/6250000000000 : ℝ)^4015
        have hw : |(2744105803/5000000000 : ℝ)|=(2744105803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s4_6 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051720821/2000000000 : ℝ)*x 0 + (5488211279/10000000000 : ℝ)*x 1 + (-85772157/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051720821/2000000000 : ℝ)^5039 ≤ (44635487376751/100000000000000 : ℝ)^4015 := by
    have hnat : (1051720821 : ℕ)^5039*100000000000000^4015 ≤ 44635487376751^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051720821 2000000000 44635487376751 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488211279/10000000000 : ℝ)^5039 ≤ (23547474140687/50000000000000 : ℝ)^4015 := by
    have hnat : (5488211279 : ℕ)^5039*50000000000000^4015 ≤ 23547474140687^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488211279 10000000000 23547474140687 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85772157/625000000 : ℝ)^5039 ≤ (8269564327547/100000000000000 : ℝ)^4015 := by
    have hnat : (85772157 : ℕ)^5039*100000000000000^4015 ≤ 8269564327547^4015*625000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85772157 625000000 8269564327547 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051720821/2000000000 : ℝ), (5488211279/10000000000 : ℝ), (-85772157/625000000 : ℝ)] ![(44635487376751/100000000000000 : ℝ), (23547474140687/50000000000000 : ℝ), (8269564327547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051720821/2000000000 : ℝ)|^5039 ≤ (44635487376751/100000000000000 : ℝ)^4015
        have hw : |(1051720821/2000000000 : ℝ)|=(1051720821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488211279/10000000000 : ℝ)|^5039 ≤ (23547474140687/50000000000000 : ℝ)^4015
        have hw : |(5488211279/10000000000 : ℝ)|=(5488211279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85772157/625000000 : ℝ)|^5039 ≤ (8269564327547/100000000000000 : ℝ)^4015
        have hw : |(-85772157/625000000 : ℝ)|=(85772157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s4_7 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4149931173/10000000000 : ℝ)*x 0 + (2320175511/5000000000 : ℝ)*x 1 + (1444327/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4149931173/10000000000 : ℝ)^5039 ≤ (33160775133549/100000000000000 : ℝ)^4015 := by
    have hnat : (4149931173 : ℕ)^5039*100000000000000^4015 ≤ 33160775133549^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149931173 10000000000 33160775133549 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320175511/5000000000 : ℝ)^5039 ≤ (38151073534049/100000000000000 : ℝ)^4015 := by
    have hnat : (2320175511 : ℕ)^5039*100000000000000^4015 ≤ 38151073534049^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320175511 5000000000 38151073534049 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444327/3906250 : ℝ)^5039 ≤ (7172037831127/25000000000000 : ℝ)^4015 := by
    have hnat : (1444327 : ℕ)^5039*25000000000000^4015 ≤ 7172037831127^4015*3906250^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444327 3906250 7172037831127 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4149931173/10000000000 : ℝ), (2320175511/5000000000 : ℝ), (1444327/3906250 : ℝ)] ![(33160775133549/100000000000000 : ℝ), (38151073534049/100000000000000 : ℝ), (7172037831127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4149931173/10000000000 : ℝ)|^5039 ≤ (33160775133549/100000000000000 : ℝ)^4015
        have hw : |(4149931173/10000000000 : ℝ)|=(4149931173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2320175511/5000000000 : ℝ)|^5039 ≤ (38151073534049/100000000000000 : ℝ)^4015
        have hw : |(2320175511/5000000000 : ℝ)|=(2320175511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1444327/3906250 : ℝ)|^5039 ≤ (7172037831127/25000000000000 : ℝ)^4015
        have hw : |(1444327/3906250 : ℝ)|=(1444327/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1677_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1083/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2423/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8663/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1083/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9691/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1083/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9691/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1083/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9691/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1083/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9691/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1083/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9691/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1083/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9691/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9691/100000 : ℝ) ^ (5031/1024 : ℝ) ≤ (1046988210216641/100000000000000000000 : ℝ) := by
    have hpowers : (9691/100000 : ℝ)^5031 ≤ (1046988210216641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9691 : ℕ)^5031*100000000000000000000^1024 ≤ 1046988210216641^1024*100000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9691 100000 1046988210216641 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9691/100000 : ℝ)) (X := (1046988210216641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1083/6250 : ℝ) ^ (5031/1024 : ℝ) ≤ (727722249743319/4000000000000000000 : ℝ) := by
    have hpowers : (1083/6250 : ℝ)^5031 ≤ (727722249743319/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1083 : ℕ)^5031*4000000000000000000^1024 ≤ 727722249743319^1024*6250^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1083 6250 727722249743319 4000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1083/6250 : ℝ)) (X := (727722249743319/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001046988210216641/50000000000000000000 : ℝ) ≤ (2500010655008817/2500000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50001046988210216641/50000000000000000000 : ℝ)^1024 ≤ (2500010655008817/2500000000000000 : ℝ)^5031 := by
      have hnat : (50001046988210216641 : ℕ)^1024*2500000000000000^5031 ≤ 2500010655008817^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001046988210216641 50000000000000000000 2500010655008817 2500000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500010655008817/2500000000000000 : ℝ)) (X := (50001046988210216641/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1562800625694590619/1562500000000000000 : ℝ) ≤ (500019578906923/500000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (1562800625694590619/1562500000000000000 : ℝ)^1024 ≤ (500019578906923/500000000000000 : ℝ)^5031 := by
      have hnat : (1562800625694590619 : ℕ)^1024*500000000000000^5031 ≤ 500019578906923^5031*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562800625694590619 1562500000000000000 500019578906923 500000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500019578906923/500000000000000 : ℝ)) (X := (1562800625694590619/1562500000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000727722249743319/2000000000000000000 : ℝ) ≤ (2500185134060413/2500000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (2000727722249743319/2000000000000000000 : ℝ)^1024 ≤ (2500185134060413/2500000000000000 : ℝ)^5031 := by
      have hnat : (2000727722249743319 : ℕ)^1024*2500000000000000^5031 ≤ 2500185134060413^5031*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000727722249743319 2000000000000000000 2500185134060413 2500000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185134060413/2500000000000000 : ℝ)) (X := (2000727722249743319/2000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1046988210216641/100000000000000000000 : ℝ) ≤ ((19090890495813318593/19092500000000000000 : ℝ)+2*(43619762899/95462500000000 : ℝ)*(9691/100000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (19090890495813318593/19092500000000000000 : ℝ)+2*(43619762899/95462500000000 : ℝ)*(9691/100000 : ℝ)=(2500010655008817/2500000000000000 : ℝ) by norm_num, show 1+2*(1046988210216641/100000000000000000000 : ℝ)=(50001046988210216641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(727722249743319/4000000000000000000 : ℝ)+(1046988210216641/100000000000000000000 : ℝ) ≤ ((19090890495813318593/19092500000000000000 : ℝ)+(43619762899/95462500000000 : ℝ)*((1083/6250 : ℝ)+(9691/100000 : ℝ)))^(5031/1024 : ℝ) := by
    rw [show (19090890495813318593/19092500000000000000 : ℝ)+(43619762899/95462500000000 : ℝ)*((1083/6250 : ℝ)+(9691/100000 : ℝ))=(500019578906923/500000000000000 : ℝ) by norm_num, show 1+(727722249743319/4000000000000000000 : ℝ)+(1046988210216641/100000000000000000000 : ℝ)=(1562800625694590619/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(727722249743319/4000000000000000000 : ℝ) ≤ ((19090890495813318593/19092500000000000000 : ℝ)+2*(43619762899/95462500000000 : ℝ)*(1083/6250 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (19090890495813318593/19092500000000000000 : ℝ)+2*(43619762899/95462500000000 : ℝ)*(1083/6250 : ℝ)=(2500185134060413/2500000000000000 : ℝ) by norm_num, show 1+2*(727722249743319/4000000000000000000 : ℝ)=(2000727722249743319/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19090890495813318593/19092500000000000000 : ℝ)*(X 1 0+X 2 0)+(43619762899/95462500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (9691/100000 : ℝ)) (hi := (1083/6250 : ℝ)) (c := (19090890495813318593/19092500000000000000 : ℝ)) (alpha := (43619762899/95462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19090890495813318593/19092500000000000000 : ℝ)*(X 0 1+X 2 1)+(43619762899/95462500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (9691/100000 : ℝ)) (hi := (1083/6250 : ℝ)) (c := (19090890495813318593/19092500000000000000 : ℝ)) (alpha := (43619762899/95462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19090890495813318593/19092500000000000000 : ℝ)*(X 0 2+X 1 2)+(43619762899/95462500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (9691/100000 : ℝ)) (hi := (1083/6250 : ℝ)) (c := (19090890495813318593/19092500000000000000 : ℝ)) (alpha := (43619762899/95462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-770442189/5000000000 : ℝ)*X 0 0+(2746067343/5000000000 : ℝ)*X 0 1+(513278991/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354513003/10000000000 : ℝ)*X 1 0+(-863888071/5000000000 : ℝ)*X 1 1+(2566394673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354512283/10000000000 : ℝ)*X 2 0+(1026557977/2000000000 : ℝ)*X 2 1+(-215972049/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2074737457/5000000000 : ℝ)*X 0 0+(1843477733/5000000000 : ℝ)*X 0 1+(581339669/1250000000 : ℝ)*X 0 2+(2074737457/5000000000 : ℝ)*X 1 0+(1843477733/5000000000 : ℝ)*X 1 1+(581339669/1250000000 : ℝ)*X 1 2+(2074737457/5000000000 : ℝ)*X 2 0+(1843477733/5000000000 : ℝ)*X 2 1+(581339669/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-770527451/5000000000 : ℝ)*X 0 0+(5136654979/10000000000 : ℝ)*X 0 1+(21438327/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258603977/10000000000 : ℝ)*X 1 0+(-343088557/2500000000 : ℝ)*X 1 1+(2744105803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051720821/2000000000 : ℝ)*X 2 0+(5488211279/10000000000 : ℝ)*X 2 1+(-85772157/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4149931173/10000000000 : ℝ)*X 0 0+(2320175511/5000000000 : ℝ)*X 0 1+(1444327/3906250 : ℝ)*X 0 2+(4149931173/10000000000 : ℝ)*X 1 0+(2320175511/5000000000 : ℝ)*X 1 1+(1444327/3906250 : ℝ)*X 1 2+(4149931173/10000000000 : ℝ)*X 2 0+(2320175511/5000000000 : ℝ)*X 2 1+(1444327/3906250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (399505515410217383457962121/38185000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370903577/20000000000000 : ℝ)*(base19) + (267879561/20000000000000 : ℝ)*(base23) + (75455287/100000000000000 : ℝ)*(lower2) + (386542683/100000000000000 : ℝ)*(upper3) + (16348651/20000000000000 : ℝ)*(upper5) + (76409572630033/4000000000000 : ℝ)*(major0) + (76409572630033/4000000000000 : ℝ)*(major1) + (76409572630033/4000000000000 : ℝ)*(major2) + (347857287715113/12500000000000 : ℝ)*(sp0) + (695716637929277/25000000000000 : ℝ)*(sp1) + (695716766709297/25000000000000 : ℝ)*(sp2) + (518802233550601/50000000000000 : ℝ)*(sp3) + (10104514089/100000000000000 : ℝ)*(sp4) + (5409419857/100000000000000 : ℝ)*(sp7) + (1037609876521059/100000000000000 : ℝ)*(f.failure) + (2782868406234993/100000000000000 : ℝ)*(f.sum) + (6502128690983/7637000000000000000000000000 : ℝ)*base66 + (417483107980066431/76370000000000000000000000000000 : ℝ)*base68 + (760546976111736431/76370000000000000000000000000000 : ℝ)*base70 + (105031668864306431/76370000000000000000000000000000 : ℝ)*base72 + (401154834937/763700000000000000000000000 : ℝ)*base74 + (68806025144936431/76370000000000000000000000000000 : ℝ)*base76 + (742234300949906431/76370000000000000000000000000000 : ℝ)*base78 + (533647079158916431/76370000000000000000000000000000 : ℝ)*base80 + (566440712287/954625000000000000000000000 : ℝ)*base82 + (3690469/2000000000000000000000 : ℝ)*base89 + (3690469/2000000000000000000000 : ℝ)*base91 + (3690469/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10511365078179472845647701437/954625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (873707149/50000000000000 : ℝ)*(base19) + (459126269/25000000000000 : ℝ)*(base23) + (224126143/50000000000000 : ℝ)*(lower1) + (36517869/100000000000000 : ℝ)*(upper2) + (53338129/25000000000000 : ℝ)*(upper3) + (73168587/25000000000000 : ℝ)*(upper5) + (1952530821427903/100000000000000 : ℝ)*(major0) + (1952530821427903/100000000000000 : ℝ)*(major1) + (1952530821427903/100000000000000 : ℝ)*(major2) + (2719021407/100000000000000 : ℝ)*(sp1) + (711119841132549/25000000000000 : ℝ)*(sp4) + (284447489809449/10000000000000 : ℝ)*(sp5) + (17777984550157/625000000000 : ℝ)*(sp6) + (1060581911292647/100000000000000 : ℝ)*(sp7) + (1060581911292647/100000000000000 : ℝ)*(f.failure) + (711119841132549/25000000000000 : ℝ)*(f.sum) + (3587564518661/38185000000000000000000000000 : ℝ)*base65 + (16810221434063199521/1909250000000000000000000000000000 : ℝ)*base68 + (33532217777097699521/1909250000000000000000000000000000 : ℝ)*base70 + (4330052741019800479/1909250000000000000000000000000000 : ℝ)*base71 + (6704502476307/1193281250000000000000000000 : ℝ)*base74 + (9171356065709800479/1909250000000000000000000000000000 : ℝ)*base75 + (4304483891833449521/1909250000000000000000000000000000 : ℝ)*base78 + (7073204130476199521/1909250000000000000000000000000000 : ℝ)*base80 + (53013768306797/4773125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (906177/2000000000000000000000 : ℝ)*base89 + (906177/2000000000000000000000 : ℝ)*base91 + (906177/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1677_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1083/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2423/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8663/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1677_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1677_box_0 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-23886347/200000000 : ℝ)*x 0 + (5435404347/10000000000 : ℝ)*x 1 + (271770061/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23886347/200000000 : ℝ)^5039 ≤ (694616427887/10000000000000 : ℝ)^4015 := by
    have hnat : (23886347 : ℕ)^5039*10000000000000^4015 ≤ 694616427887^4015*200000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23886347 200000000 694616427887 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435404347/10000000000 : ℝ)^5039 ≤ (11631733661639/25000000000000 : ℝ)^4015 := by
    have hnat : (5435404347 : ℕ)^5039*25000000000000^4015 ≤ 11631733661639^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435404347 10000000000 11631733661639 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271770061/500000000 : ℝ)^5039 ≤ (46526901052747/100000000000000 : ℝ)^4015 := by
    have hnat : (271770061 : ℕ)^5039*100000000000000^4015 ≤ 46526901052747^4015*500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271770061 500000000 46526901052747 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23886347/200000000 : ℝ), (5435404347/10000000000 : ℝ), (271770061/500000000 : ℝ)] ![(694616427887/10000000000000 : ℝ), (11631733661639/25000000000000 : ℝ), (46526901052747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23886347/200000000 : ℝ)|^5039 ≤ (694616427887/10000000000000 : ℝ)^4015
        have hw : |(-23886347/200000000 : ℝ)|=(23886347/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435404347/10000000000 : ℝ)|^5039 ≤ (11631733661639/25000000000000 : ℝ)^4015
        have hw : |(5435404347/10000000000 : ℝ)|=(5435404347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271770061/500000000 : ℝ)|^5039 ≤ (46526901052747/100000000000000 : ℝ)^4015
        have hw : |(271770061/500000000 : ℝ)|=(271770061/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_1 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226057077/10000000000 : ℝ)*x 0 + (-149197103/1000000000 : ℝ)*x 1 + (5435403889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226057077/10000000000 : ℝ)^5039 ≤ (22144520305221/50000000000000 : ℝ)^4015 := by
    have hnat : (5226057077 : ℕ)^5039*50000000000000^4015 ≤ 22144520305221^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226057077 10000000000 22144520305221 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149197103/1000000000 : ℝ)^5039 ≤ (9184029647467/100000000000000 : ℝ)^4015 := by
    have hnat : (149197103 : ℕ)^5039*100000000000000^4015 ≤ 9184029647467^4015*1000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149197103 1000000000 9184029647467 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435403889/10000000000 : ℝ)^5039 ≤ (11631732431549/25000000000000 : ℝ)^4015 := by
    have hnat : (5435403889 : ℕ)^5039*25000000000000^4015 ≤ 11631732431549^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435403889 10000000000 11631732431549 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226057077/10000000000 : ℝ), (-149197103/1000000000 : ℝ), (5435403889/10000000000 : ℝ)] ![(22144520305221/50000000000000 : ℝ), (9184029647467/100000000000000 : ℝ), (11631732431549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226057077/10000000000 : ℝ)|^5039 ≤ (22144520305221/50000000000000 : ℝ)^4015
        have hw : |(5226057077/10000000000 : ℝ)|=(5226057077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149197103/1000000000 : ℝ)|^5039 ≤ (9184029647467/100000000000000 : ℝ)^4015
        have hw : |(-149197103/1000000000 : ℝ)|=(149197103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435403889/10000000000 : ℝ)|^5039 ≤ (11631732431549/25000000000000 : ℝ)^4015
        have hw : |(5435403889/10000000000 : ℝ)|=(5435403889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_2 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045211569/2000000000 : ℝ)*x 0 + (5435402783/10000000000 : ℝ)*x 1 + (-1491971511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045211569/2000000000 : ℝ)^5039 ≤ (44289048778939/100000000000000 : ℝ)^4015 := by
    have hnat : (1045211569 : ℕ)^5039*100000000000000^4015 ≤ 44289048778939^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045211569 2000000000 44289048778939 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435402783/10000000000 : ℝ)^5039 ≤ (46526917844279/100000000000000 : ℝ)^4015 := by
    have hnat : (5435402783 : ℕ)^5039*100000000000000^4015 ≤ 46526917844279^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435402783 10000000000 46526917844279 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491971511/10000000000 : ℝ)^5039 ≤ (2296008340869/25000000000000 : ℝ)^4015 := by
    have hnat : (1491971511 : ℕ)^5039*25000000000000^4015 ≤ 2296008340869^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491971511 10000000000 2296008340869 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045211569/2000000000 : ℝ), (5435402783/10000000000 : ℝ), (-1491971511/10000000000 : ℝ)] ![(44289048778939/100000000000000 : ℝ), (46526917844279/100000000000000 : ℝ), (2296008340869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045211569/2000000000 : ℝ)|^5039 ≤ (44289048778939/100000000000000 : ℝ)^4015
        have hw : |(1045211569/2000000000 : ℝ)|=(1045211569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435402783/10000000000 : ℝ)|^5039 ≤ (46526917844279/100000000000000 : ℝ)^4015
        have hw : |(5435402783/10000000000 : ℝ)|=(5435402783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1491971511/10000000000 : ℝ)|^5039 ≤ (2296008340869/25000000000000 : ℝ)^4015
        have hw : |(-1491971511/10000000000 : ℝ)|=(1491971511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_3 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2267873499/5000000000 : ℝ)*x 0 + (39796979/100000000 : ℝ)*x 1 + (3979696133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2267873499/5000000000 : ℝ)^5039 ≤ (9268710435453/25000000000000 : ℝ)^4015 := by
    have hnat : (2267873499 : ℕ)^5039*25000000000000^4015 ≤ 9268710435453^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267873499 5000000000 9268710435453 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39796979/100000000 : ℝ)^5039 ≤ (15731293945379/50000000000000 : ℝ)^4015 := by
    have hnat : (39796979 : ℕ)^5039*50000000000000^4015 ≤ 15731293945379^4015*100000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39796979 100000000 15731293945379 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3979696133/10000000000 : ℝ)^5039 ≤ (31462570358427/100000000000000 : ℝ)^4015 := by
    have hnat : (3979696133 : ℕ)^5039*100000000000000^4015 ≤ 31462570358427^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979696133 10000000000 31462570358427 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2267873499/5000000000 : ℝ), (39796979/100000000 : ℝ), (3979696133/10000000000 : ℝ)] ![(9268710435453/25000000000000 : ℝ), (15731293945379/50000000000000 : ℝ), (31462570358427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2267873499/5000000000 : ℝ)|^5039 ≤ (9268710435453/25000000000000 : ℝ)^4015
        have hw : |(2267873499/5000000000 : ℝ)|=(2267873499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39796979/100000000 : ℝ)|^5039 ≤ (15731293945379/50000000000000 : ℝ)^4015
        have hw : |(39796979/100000000 : ℝ)|=(39796979/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3979696133/10000000000 : ℝ)|^5039 ≤ (31462570358427/100000000000000 : ℝ)^4015
        have hw : |(3979696133/10000000000 : ℝ)|=(3979696133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_4 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-477154957/2500000000 : ℝ)*x 0 + (5174823/10000000 : ℝ)*x 1 + (5174823091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477154957/2500000000 : ℝ)^5039 ≤ (12510409779043/100000000000000 : ℝ)^4015 := by
    have hnat : (477154957 : ℕ)^5039*100000000000000^4015 ≤ 12510409779043^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477154957 2500000000 12510409779043 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174823/10000000 : ℝ)^5039 ≤ (5468099327431/12500000000000 : ℝ)^4015 := by
    have hnat : (5174823 : ℕ)^5039*12500000000000^4015 ≤ 5468099327431^4015*10000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174823 10000000 5468099327431 12500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174823091/10000000000 : ℝ)^5039 ≤ (43744795584901/100000000000000 : ℝ)^4015 := by
    have hnat : (5174823091 : ℕ)^5039*100000000000000^4015 ≤ 43744795584901^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174823091 10000000000 43744795584901 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-477154957/2500000000 : ℝ), (5174823/10000000 : ℝ), (5174823091/10000000000 : ℝ)] ![(12510409779043/100000000000000 : ℝ), (5468099327431/12500000000000 : ℝ), (43744795584901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-477154957/2500000000 : ℝ)|^5039 ≤ (12510409779043/100000000000000 : ℝ)^4015
        have hw : |(-477154957/2500000000 : ℝ)|=(477154957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174823/10000000 : ℝ)|^5039 ≤ (5468099327431/12500000000000 : ℝ)^4015
        have hw : |(5174823/10000000 : ℝ)|=(5174823/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174823091/10000000000 : ℝ)|^5039 ≤ (43744795584901/100000000000000 : ℝ)^4015
        have hw : |(5174823091/10000000000 : ℝ)|=(5174823091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_5 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404233871/10000000000 : ℝ)*x 0 + (-1604665729/10000000000 : ℝ)*x 1 + (646852849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404233871/10000000000 : ℝ)^5039 ≤ (11548077744411/25000000000000 : ℝ)^4015 := by
    have hnat : (5404233871 : ℕ)^5039*25000000000000^4015 ≤ 11548077744411^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404233871 10000000000 11548077744411 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1604665729/10000000000 : ℝ)^5039 ≤ (31446551873/312500000000 : ℝ)^4015 := by
    have hnat : (1604665729 : ℕ)^5039*312500000000^4015 ≤ 31446551873^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604665729 10000000000 31446551873 312500000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646852849/1250000000 : ℝ)^5039 ≤ (21872396206349/50000000000000 : ℝ)^4015 := by
    have hnat : (646852849 : ℕ)^5039*50000000000000^4015 ≤ 21872396206349^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646852849 1250000000 21872396206349 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404233871/10000000000 : ℝ), (-1604665729/10000000000 : ℝ), (646852849/1250000000 : ℝ)] ![(11548077744411/25000000000000 : ℝ), (31446551873/312500000000 : ℝ), (21872396206349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404233871/10000000000 : ℝ)|^5039 ≤ (11548077744411/25000000000000 : ℝ)^4015
        have hw : |(5404233871/10000000000 : ℝ)|=(5404233871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1604665729/10000000000 : ℝ)|^5039 ≤ (31446551873/312500000000 : ℝ)^4015
        have hw : |(-1604665729/10000000000 : ℝ)|=(1604665729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646852849/1250000000 : ℝ)|^5039 ≤ (21872396206349/50000000000000 : ℝ)^4015
        have hw : |(646852849/1250000000 : ℝ)|=(646852849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_6 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080846749/2000000000 : ℝ)*x 0 + (2587411443/5000000000 : ℝ)*x 1 + (-1604665773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080846749/2000000000 : ℝ)^5039 ≤ (5774038703249/12500000000000 : ℝ)^4015 := by
    have hnat : (1080846749 : ℕ)^5039*12500000000000^4015 ≤ 5774038703249^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080846749 2000000000 5774038703249 12500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587411443/5000000000 : ℝ)^5039 ≤ (43744793409979/100000000000000 : ℝ)^4015 := by
    have hnat : (2587411443 : ℕ)^5039*100000000000000^4015 ≤ 43744793409979^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587411443 5000000000 43744793409979 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1604665773/10000000000 : ℝ)^5039 ≤ (5031448472829/50000000000000 : ℝ)^4015 := by
    have hnat : (1604665773 : ℕ)^5039*50000000000000^4015 ≤ 5031448472829^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604665773 10000000000 5031448472829 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080846749/2000000000 : ℝ), (2587411443/5000000000 : ℝ), (-1604665773/10000000000 : ℝ)] ![(5774038703249/12500000000000 : ℝ), (43744793409979/100000000000000 : ℝ), (5031448472829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080846749/2000000000 : ℝ)|^5039 ≤ (5774038703249/12500000000000 : ℝ)^4015
        have hw : |(1080846749/2000000000 : ℝ)|=(1080846749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587411443/5000000000 : ℝ)|^5039 ≤ (43744793409979/100000000000000 : ℝ)^4015
        have hw : |(2587411443/5000000000 : ℝ)|=(2587411443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1604665773/10000000000 : ℝ)|^5039 ≤ (5031448472829/50000000000000 : ℝ)^4015
        have hw : |(-1604665773/10000000000 : ℝ)|=(1604665773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_7 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (37493647/100000000 : ℝ)*x 0 + (2186000743/5000000000 : ℝ)*x 1 + (546500189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37493647/100000000 : ℝ)^5039 ≤ (7298579369111/25000000000000 : ℝ)^4015 := by
    have hnat : (37493647 : ℕ)^5039*25000000000000^4015 ≤ 7298579369111^4015*100000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37493647 100000000 7298579369111 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186000743/5000000000 : ℝ)^5039 ≤ (3540284112319/10000000000000 : ℝ)^4015 := by
    have hnat : (2186000743 : ℕ)^5039*10000000000000^4015 ≤ 3540284112319^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186000743 5000000000 3540284112319 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546500189/1250000000 : ℝ)^5039 ≤ (1416113655497/4000000000000 : ℝ)^4015 := by
    have hnat : (546500189 : ℕ)^5039*4000000000000^4015 ≤ 1416113655497^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546500189 1250000000 1416113655497 4000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(37493647/100000000 : ℝ), (2186000743/5000000000 : ℝ), (546500189/1250000000 : ℝ)] ![(7298579369111/25000000000000 : ℝ), (3540284112319/10000000000000 : ℝ), (1416113655497/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(37493647/100000000 : ℝ)|^5039 ≤ (7298579369111/25000000000000 : ℝ)^4015
        have hw : |(37493647/100000000 : ℝ)|=(37493647/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2186000743/5000000000 : ℝ)|^5039 ≤ (3540284112319/10000000000000 : ℝ)^4015
        have hw : |(2186000743/5000000000 : ℝ)|=(2186000743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546500189/1250000000 : ℝ)|^5039 ≤ (1416113655497/4000000000000 : ℝ)^4015
        have hw : |(546500189/1250000000 : ℝ)|=(546500189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_8 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219455749/1250000000 : ℝ)*x 0 + (1246085273/2500000000 : ℝ)*x 1 + (5479524607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219455749/1250000000 : ℝ)^5039 ≤ (11265110058487/100000000000000 : ℝ)^4015 := by
    have hnat : (219455749 : ℕ)^5039*100000000000000^4015 ≤ 11265110058487^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219455749 1250000000 11265110058487 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246085273/2500000000 : ℝ)^5039 ≤ (41733475328403/100000000000000 : ℝ)^4015 := by
    have hnat : (1246085273 : ℕ)^5039*100000000000000^4015 ≤ 41733475328403^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246085273 2500000000 41733475328403 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479524607/10000000000 : ℝ)^5039 ≤ (4700141459891/10000000000000 : ℝ)^4015 := by
    have hnat : (5479524607 : ℕ)^5039*10000000000000^4015 ≤ 4700141459891^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479524607 10000000000 4700141459891 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219455749/1250000000 : ℝ), (1246085273/2500000000 : ℝ), (5479524607/10000000000 : ℝ)] ![(11265110058487/100000000000000 : ℝ), (41733475328403/100000000000000 : ℝ), (4700141459891/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219455749/1250000000 : ℝ)|^5039 ≤ (11265110058487/100000000000000 : ℝ)^4015
        have hw : |(-219455749/1250000000 : ℝ)|=(219455749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1246085273/2500000000 : ℝ)|^5039 ≤ (41733475328403/100000000000000 : ℝ)^4015
        have hw : |(1246085273/2500000000 : ℝ)|=(1246085273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479524607/10000000000 : ℝ)|^5039 ≤ (4700141459891/10000000000000 : ℝ)^4015
        have hw : |(5479524607/10000000000 : ℝ)|=(5479524607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_9 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195894611/10000000000 : ℝ)*x 0 + (-736007931/5000000000 : ℝ)*x 1 + (5479523699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195894611/10000000000 : ℝ)^5039 ≤ (43968467153361/100000000000000 : ℝ)^4015 := by
    have hnat : (5195894611 : ℕ)^5039*100000000000000^4015 ≤ 43968467153361^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195894611 10000000000 43968467153361 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736007931/5000000000 : ℝ)^5039 ≤ (2257532002909/25000000000000 : ℝ)^4015 := by
    have hnat : (736007931 : ℕ)^5039*25000000000000^4015 ≤ 2257532002909^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736007931 5000000000 2257532002909 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479523699/10000000000 : ℝ)^5039 ≤ (23500702412001/50000000000000 : ℝ)^4015 := by
    have hnat : (5479523699 : ℕ)^5039*50000000000000^4015 ≤ 23500702412001^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479523699 10000000000 23500702412001 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195894611/10000000000 : ℝ), (-736007931/5000000000 : ℝ), (5479523699/10000000000 : ℝ)] ![(43968467153361/100000000000000 : ℝ), (2257532002909/25000000000000 : ℝ), (23500702412001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195894611/10000000000 : ℝ)|^5039 ≤ (43968467153361/100000000000000 : ℝ)^4015
        have hw : |(5195894611/10000000000 : ℝ)|=(5195894611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-736007931/5000000000 : ℝ)|^5039 ≤ (2257532002909/25000000000000 : ℝ)^4015
        have hw : |(-736007931/5000000000 : ℝ)|=(736007931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479523699/10000000000 : ℝ)|^5039 ≤ (23500702412001/50000000000000 : ℝ)^4015
        have hw : |(5479523699/10000000000 : ℝ)|=(5479523699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_10 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519589449/1000000000 : ℝ)*x 0 + (5479524153/10000000000 : ℝ)*x 1 + (-294403079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519589449/1000000000 : ℝ)^5039 ≤ (5496058233537/12500000000000 : ℝ)^4015 := by
    have hnat : (519589449 : ℕ)^5039*12500000000000^4015 ≤ 5496058233537^4015*1000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519589449 1000000000 5496058233537 12500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479524153/10000000000 : ℝ)^5039 ≤ (1468794053483/3125000000000 : ℝ)^4015 := by
    have hnat : (5479524153 : ℕ)^5039*3125000000000^4015 ≤ 1468794053483^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479524153 10000000000 1468794053483 3125000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294403079/2000000000 : ℝ)^5039 ≤ (4515062208077/50000000000000 : ℝ)^4015 := by
    have hnat : (294403079 : ℕ)^5039*50000000000000^4015 ≤ 4515062208077^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294403079 2000000000 4515062208077 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519589449/1000000000 : ℝ), (5479524153/10000000000 : ℝ), (-294403079/2000000000 : ℝ)] ![(5496058233537/12500000000000 : ℝ), (1468794053483/3125000000000 : ℝ), (4515062208077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519589449/1000000000 : ℝ)|^5039 ≤ (5496058233537/12500000000000 : ℝ)^4015
        have hw : |(519589449/1000000000 : ℝ)|=(519589449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479524153/10000000000 : ℝ)|^5039 ≤ (1468794053483/3125000000000 : ℝ)^4015
        have hw : |(5479524153/10000000000 : ℝ)|=(5479524153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-294403079/2000000000 : ℝ)|^5039 ≤ (4515062208077/50000000000000 : ℝ)^4015
        have hw : |(-294403079/2000000000 : ℝ)|=(294403079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_11 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2331919947/5000000000 : ℝ)*x 0 + (48913731/125000000 : ℝ)*x 1 + (39130989/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2331919947/5000000000 : ℝ)^5039 ≤ (3839359869071/10000000000000 : ℝ)^4015 := by
    have hnat : (2331919947 : ℕ)^5039*10000000000000^4015 ≤ 3839359869071^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331919947 5000000000 3839359869071 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48913731/125000000 : ℝ)^5039 ≤ (6160639714757/20000000000000 : ℝ)^4015 := by
    have hnat : (48913731 : ℕ)^5039*20000000000000^4015 ≤ 6160639714757^4015*125000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48913731 125000000 6160639714757 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39130989/100000000 : ℝ)^5039 ≤ (7700800680791/25000000000000 : ℝ)^4015 := by
    have hnat : (39130989 : ℕ)^5039*25000000000000^4015 ≤ 7700800680791^4015*100000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39130989 100000000 7700800680791 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2331919947/5000000000 : ℝ), (48913731/125000000 : ℝ), (39130989/100000000 : ℝ)] ![(3839359869071/10000000000000 : ℝ), (6160639714757/20000000000000 : ℝ), (7700800680791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2331919947/5000000000 : ℝ)|^5039 ≤ (3839359869071/10000000000000 : ℝ)^4015
        have hw : |(2331919947/5000000000 : ℝ)|=(2331919947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48913731/125000000 : ℝ)|^5039 ≤ (6160639714757/20000000000000 : ℝ)^4015
        have hw : |(48913731/125000000 : ℝ)|=(48913731/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39130989/100000000 : ℝ)|^5039 ≤ (7700800680791/25000000000000 : ℝ)^4015
        have hw : |(39130989/100000000 : ℝ)|=(39130989/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_12 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-335743371/2500000000 : ℝ)*x 0 + (5616104941/10000000000 : ℝ)*x 1 + (5149437073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335743371/2500000000 : ℝ)^5039 ≤ (8047975212053/100000000000000 : ℝ)^4015 := by
    have hnat : (335743371 : ℕ)^5039*100000000000000^4015 ≤ 8047975212053^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335743371 2500000000 8047975212053 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5616104941/10000000000 : ℝ)^5039 ≤ (4847639021397/10000000000000 : ℝ)^4015 := by
    have hnat : (5616104941 : ℕ)^5039*10000000000000^4015 ≤ 4847639021397^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616104941 10000000000 4847639021397 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149437073/10000000000 : ℝ)^5039 ≤ (21737817280027/50000000000000 : ℝ)^4015 := by
    have hnat : (5149437073 : ℕ)^5039*50000000000000^4015 ≤ 21737817280027^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149437073 10000000000 21737817280027 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-335743371/2500000000 : ℝ), (5616104941/10000000000 : ℝ), (5149437073/10000000000 : ℝ)] ![(8047975212053/100000000000000 : ℝ), (4847639021397/10000000000000 : ℝ), (21737817280027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-335743371/2500000000 : ℝ)|^5039 ≤ (8047975212053/100000000000000 : ℝ)^4015
        have hw : |(-335743371/2500000000 : ℝ)|=(335743371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5616104941/10000000000 : ℝ)|^5039 ≤ (4847639021397/10000000000000 : ℝ)^4015
        have hw : |(5616104941/10000000000 : ℝ)|=(5616104941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149437073/10000000000 : ℝ)|^5039 ≤ (21737817280027/50000000000000 : ℝ)^4015
        have hw : |(5149437073/10000000000 : ℝ)|=(5149437073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_13 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5421616821/10000000000 : ℝ)*x 0 + (-1615153249/10000000000 : ℝ)*x 1 + (643679609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421616821/10000000000 : ℝ)^5039 ≤ (46378861214603/100000000000000 : ℝ)^4015 := by
    have hnat : (5421616821 : ℕ)^5039*100000000000000^4015 ≤ 46378861214603^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421616821 10000000000 46378861214603 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615153249/10000000000 : ℝ)^5039 ≤ (101455063411/1000000000000 : ℝ)^4015 := by
    have hnat : (1615153249 : ℕ)^5039*1000000000000^4015 ≤ 101455063411^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615153249 10000000000 101455063411 1000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643679609/1250000000 : ℝ)^5039 ≤ (43475632430243/100000000000000 : ℝ)^4015 := by
    have hnat : (643679609 : ℕ)^5039*100000000000000^4015 ≤ 43475632430243^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643679609 1250000000 43475632430243 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421616821/10000000000 : ℝ), (-1615153249/10000000000 : ℝ), (643679609/1250000000 : ℝ)] ![(46378861214603/100000000000000 : ℝ), (101455063411/1000000000000 : ℝ), (43475632430243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421616821/10000000000 : ℝ)|^5039 ≤ (46378861214603/100000000000000 : ℝ)^4015
        have hw : |(5421616821/10000000000 : ℝ)|=(5421616821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1615153249/10000000000 : ℝ)|^5039 ≤ (101455063411/1000000000000 : ℝ)^4015
        have hw : |(-1615153249/10000000000 : ℝ)|=(1615153249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643679609/1250000000 : ℝ)|^5039 ≤ (43475632430243/100000000000000 : ℝ)^4015
        have hw : |(643679609/1250000000 : ℝ)|=(643679609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_14 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542161709/1000000000 : ℝ)*x 0 + (2574718363/5000000000 : ℝ)*x 1 + (-40378827/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542161709/1000000000 : ℝ)^5039 ≤ (46378864102637/100000000000000 : ℝ)^4015 := by
    have hnat : (542161709 : ℕ)^5039*100000000000000^4015 ≤ 46378864102637^4015*1000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542161709 1000000000 46378864102637 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2574718363/5000000000 : ℝ)^5039 ≤ (2717226930201/6250000000000 : ℝ)^4015 := by
    have hnat : (2574718363 : ℕ)^5039*6250000000000^4015 ≤ 2717226930201^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574718363 5000000000 2717226930201 6250000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40378827/250000000 : ℝ)^5039 ≤ (10145505008789/100000000000000 : ℝ)^4015 := by
    have hnat : (40378827 : ℕ)^5039*100000000000000^4015 ≤ 10145505008789^4015*250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40378827 250000000 10145505008789 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542161709/1000000000 : ℝ), (2574718363/5000000000 : ℝ), (-40378827/250000000 : ℝ)] ![(46378864102637/100000000000000 : ℝ), (2717226930201/6250000000000 : ℝ), (10145505008789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542161709/1000000000 : ℝ)|^5039 ≤ (46378864102637/100000000000000 : ℝ)^4015
        have hw : |(542161709/1000000000 : ℝ)|=(542161709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2574718363/5000000000 : ℝ)|^5039 ≤ (2717226930201/6250000000000 : ℝ)^4015
        have hw : |(2574718363/5000000000 : ℝ)|=(2574718363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40378827/250000000 : ℝ)|^5039 ≤ (10145505008789/100000000000000 : ℝ)^4015
        have hw : |(-40378827/250000000 : ℝ)|=(40378827/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_box_15 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3669776659/10000000000 : ℝ)*x 0 + (4410119951/10000000000 : ℝ)*x 1 + (275632501/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3669776659/10000000000 : ℝ)^5039 ≤ (28418671042371/100000000000000 : ℝ)^4015 := by
    have hnat : (3669776659 : ℕ)^5039*100000000000000^4015 ≤ 28418671042371^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669776659 10000000000 28418671042371 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4410119951/10000000000 : ℝ)^5039 ≤ (35790664141429/100000000000000 : ℝ)^4015 := by
    have hnat : (4410119951 : ℕ)^5039*100000000000000^4015 ≤ 35790664141429^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410119951 10000000000 35790664141429 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275632501/625000000 : ℝ)^5039 ≤ (894766620087/2500000000000 : ℝ)^4015 := by
    have hnat : (275632501 : ℕ)^5039*2500000000000^4015 ≤ 894766620087^4015*625000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275632501 625000000 894766620087 2500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3669776659/10000000000 : ℝ), (4410119951/10000000000 : ℝ), (275632501/625000000 : ℝ)] ![(28418671042371/100000000000000 : ℝ), (35790664141429/100000000000000 : ℝ), (894766620087/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3669776659/10000000000 : ℝ)|^5039 ≤ (28418671042371/100000000000000 : ℝ)^4015
        have hw : |(3669776659/10000000000 : ℝ)|=(3669776659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4410119951/10000000000 : ℝ)|^5039 ≤ (35790664141429/100000000000000 : ℝ)^4015
        have hw : |(4410119951/10000000000 : ℝ)|=(4410119951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275632501/625000000 : ℝ)|^5039 ≤ (894766620087/2500000000000 : ℝ)^4015
        have hw : |(275632501/625000000 : ℝ)|=(275632501/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1677_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8663/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2423/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2659/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57619/100000 : ℝ) ∧ (80333/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17987/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8663/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2423/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8663/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2423/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8663/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2423/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8663/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2423/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8663/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2423/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8663/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2423/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2423/25000 : ℝ) ^ (5031/1024 : ℝ) ≤ (1047519113289739/100000000000000000000 : ℝ) := by
    have hpowers : (2423/25000 : ℝ)^5031 ≤ (1047519113289739/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2423 : ℕ)^5031*100000000000000000000^1024 ≤ 1047519113289739^1024*25000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2423 25000 1047519113289739 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2423/25000 : ℝ)) (X := (1047519113289739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8663/50000 : ℝ) ^ (5031/1024 : ℝ) ≤ (18182741854622949/100000000000000000000 : ℝ) := by
    have hpowers : (8663/50000 : ℝ)^5031 ≤ (18182741854622949/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8663 : ℕ)^5031*100000000000000000000^1024 ≤ 18182741854622949^1024*50000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8663 50000 18182741854622949 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8663/50000 : ℝ)) (X := (18182741854622949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001047519113289739/50000000000000000000 : ℝ) ≤ (625002665102919/625000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50001047519113289739/50000000000000000000 : ℝ)^1024 ≤ (625002665102919/625000000000000 : ℝ)^5031 := by
      have hnat : (50001047519113289739 : ℕ)^1024*625000000000000^5031 ≤ 625002665102919^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001047519113289739 50000000000000000000 625002665102919 625000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625002665102919/625000000000000 : ℝ)) (X := (50001047519113289739/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251201891310494543/6250000000000000000 : ℝ) ≤ (1250048922379723/1250000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (6251201891310494543/6250000000000000000 : ℝ)^1024 ≤ (1250048922379723/1250000000000000 : ℝ)^5031 := by
      have hnat : (6251201891310494543 : ℕ)^1024*1250000000000000^5031 ≤ 1250048922379723^5031*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251201891310494543 6250000000000000000 1250048922379723 1250000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250048922379723/1250000000000000 : ℝ)) (X := (6251201891310494543/6250000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018182741854622949/50000000000000000000 : ℝ) ≤ (156261564319201/156250000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50018182741854622949/50000000000000000000 : ℝ)^1024 ≤ (156261564319201/156250000000000 : ℝ)^5031 := by
      have hnat : (50018182741854622949 : ℕ)^1024*156250000000000^5031 ≤ 156261564319201^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018182741854622949 50000000000000000000 156261564319201 156250000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156261564319201/156250000000000 : ℝ)) (X := (50018182741854622949/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1047519113289739/100000000000000000000 : ℝ) ≤ ((2385423925023195113/2385625000000000000 : ℝ)+2*(8718434777/19085000000000 : ℝ)*(2423/25000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (2385423925023195113/2385625000000000000 : ℝ)+2*(8718434777/19085000000000 : ℝ)*(2423/25000 : ℝ)=(625002665102919/625000000000000 : ℝ) by norm_num, show 1+2*(1047519113289739/100000000000000000000 : ℝ)=(50001047519113289739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18182741854622949/100000000000000000000 : ℝ)+(1047519113289739/100000000000000000000 : ℝ) ≤ ((2385423925023195113/2385625000000000000 : ℝ)+(8718434777/19085000000000 : ℝ)*((8663/50000 : ℝ)+(2423/25000 : ℝ)))^(5031/1024 : ℝ) := by
    rw [show (2385423925023195113/2385625000000000000 : ℝ)+(8718434777/19085000000000 : ℝ)*((8663/50000 : ℝ)+(2423/25000 : ℝ))=(1250048922379723/1250000000000000 : ℝ) by norm_num, show 1+(18182741854622949/100000000000000000000 : ℝ)+(1047519113289739/100000000000000000000 : ℝ)=(6251201891310494543/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18182741854622949/100000000000000000000 : ℝ) ≤ ((2385423925023195113/2385625000000000000 : ℝ)+2*(8718434777/19085000000000 : ℝ)*(8663/50000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (2385423925023195113/2385625000000000000 : ℝ)+2*(8718434777/19085000000000 : ℝ)*(8663/50000 : ℝ)=(156261564319201/156250000000000 : ℝ) by norm_num, show 1+2*(18182741854622949/100000000000000000000 : ℝ)=(50018182741854622949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2385423925023195113/2385625000000000000 : ℝ)*(X 1 0+X 2 0)+(8718434777/19085000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (2423/25000 : ℝ)) (hi := (8663/50000 : ℝ)) (c := (2385423925023195113/2385625000000000000 : ℝ)) (alpha := (8718434777/19085000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2385423925023195113/2385625000000000000 : ℝ)*(X 0 1+X 2 1)+(8718434777/19085000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (2423/25000 : ℝ)) (hi := (8663/50000 : ℝ)) (c := (2385423925023195113/2385625000000000000 : ℝ)) (alpha := (8718434777/19085000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2385423925023195113/2385625000000000000 : ℝ)*(X 0 2+X 1 2)+(8718434777/19085000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (2423/25000 : ℝ)) (hi := (8663/50000 : ℝ)) (c := (2385423925023195113/2385625000000000000 : ℝ)) (alpha := (8718434777/19085000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-23886347/200000000 : ℝ)*X 0 0+(5435404347/10000000000 : ℝ)*X 0 1+(271770061/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5226057077/10000000000 : ℝ)*X 1 0+(-149197103/1000000000 : ℝ)*X 1 1+(5435403889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1045211569/2000000000 : ℝ)*X 2 0+(5435402783/10000000000 : ℝ)*X 2 1+(-1491971511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2267873499/5000000000 : ℝ)*X 0 0+(39796979/100000000 : ℝ)*X 0 1+(3979696133/10000000000 : ℝ)*X 0 2+(2267873499/5000000000 : ℝ)*X 1 0+(39796979/100000000 : ℝ)*X 1 1+(3979696133/10000000000 : ℝ)*X 1 2+(2267873499/5000000000 : ℝ)*X 2 0+(39796979/100000000 : ℝ)*X 2 1+(3979696133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-477154957/2500000000 : ℝ)*X 0 0+(5174823/10000000 : ℝ)*X 0 1+(5174823091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5404233871/10000000000 : ℝ)*X 1 0+(-1604665729/10000000000 : ℝ)*X 1 1+(646852849/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1080846749/2000000000 : ℝ)*X 2 0+(2587411443/5000000000 : ℝ)*X 2 1+(-1604665773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((37493647/100000000 : ℝ)*X 0 0+(2186000743/5000000000 : ℝ)*X 0 1+(546500189/1250000000 : ℝ)*X 0 2+(37493647/100000000 : ℝ)*X 1 0+(2186000743/5000000000 : ℝ)*X 1 1+(546500189/1250000000 : ℝ)*X 1 2+(37493647/100000000 : ℝ)*X 2 0+(2186000743/5000000000 : ℝ)*X 2 1+(546500189/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-219455749/1250000000 : ℝ)*X 0 0+(1246085273/2500000000 : ℝ)*X 0 1+(5479524607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5195894611/10000000000 : ℝ)*X 1 0+(-736007931/5000000000 : ℝ)*X 1 1+(5479523699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((519589449/1000000000 : ℝ)*X 2 0+(5479524153/10000000000 : ℝ)*X 2 1+(-294403079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2331919947/5000000000 : ℝ)*X 0 0+(48913731/125000000 : ℝ)*X 0 1+(39130989/100000000 : ℝ)*X 0 2+(2331919947/5000000000 : ℝ)*X 1 0+(48913731/125000000 : ℝ)*X 1 1+(39130989/100000000 : ℝ)*X 1 2+(2331919947/5000000000 : ℝ)*X 2 0+(48913731/125000000 : ℝ)*X 2 1+(39130989/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-335743371/2500000000 : ℝ)*X 0 0+(5616104941/10000000000 : ℝ)*X 0 1+(5149437073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5421616821/10000000000 : ℝ)*X 1 0+(-1615153249/10000000000 : ℝ)*X 1 1+(643679609/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((542161709/1000000000 : ℝ)*X 2 0+(2574718363/5000000000 : ℝ)*X 2 1+(-40378827/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3669776659/10000000000 : ℝ)*X 0 0+(4410119951/10000000000 : ℝ)*X 0 1+(275632501/625000000 : ℝ)*X 0 2+(3669776659/10000000000 : ℝ)*X 1 0+(4410119951/10000000000 : ℝ)*X 1 1+(275632501/625000000 : ℝ)*X 1 2+(3669776659/10000000000 : ℝ)*X 2 0+(4410119951/10000000000 : ℝ)*X 2 1+(275632501/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2659/4000 : ℝ) ≤ (-2537241003116609560786850181/3817000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5267757/25000000000000 : ℝ)*(lower0) + (17328679/100000000000000 : ℝ)*(lower3) + (1116397/4000000000000 : ℝ)*(lower4) + (254353473125789/20000000000000 : ℝ)*(major0) + (254353473125789/20000000000000 : ℝ)*(major1) + (254353473125789/20000000000000 : ℝ)*(major2) + (296196143/20000000000000 : ℝ)*(sp1) + (1721554799/100000000000000 : ℝ)*(sp2) + (58590293831939/3125000000000 : ℝ)*(sp4) + (937443988189673/50000000000000 : ℝ)*(sp5) + (937443867902631/50000000000000 : ℝ)*(sp6) + (345399969720117/50000000000000 : ℝ)*(sp7) + (54738013/100000000000000 : ℝ)*(sp12) + (541877313/20000000000000 : ℝ)*(sp15) + (690802648826799/100000000000000 : ℝ)*(f.failure) + (1874889457360061/100000000000000 : ℝ)*(f.sum) + (9408309383823/3817000000000000000000000000 : ℝ)*base66 + (62958603882105843/47712500000000000000000000000000 : ℝ)*base68 + (320071959710631657/47712500000000000000000000000000 : ℝ)*base69 + (83868715982455843/47712500000000000000000000000000 : ℝ)*base72 + (234415831361/152680000000000000000000000 : ℝ)*base73 + (234991585561256657/47712500000000000000000000000000 : ℝ)*base75 + (9247125756305843/47712500000000000000000000000000 : ℝ)*base78 + (59132649185744157/47712500000000000000000000000000 : ℝ)*base79 + (5570824125099/3817000000000000000000000000 : ℝ)*base81 + (261191/2000000000000000000000 : ℝ)*base90 + (261191/2000000000000000000000 : ℝ)*base92 + (261191/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (57619/100000 : ℝ) ≤ (6873122104068323701203505702797/11928125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13254373/100000000000000 : ℝ)*(lower1) + (46937679/50000000000000 : ℝ)*(lower2) + (202906603/100000000000000 : ℝ)*(lower5) + (136710084560023/10000000000000 : ℝ)*(major0) + (136710084560023/10000000000000 : ℝ)*(major1) + (136710084560023/10000000000000 : ℝ)*(major2) + (986198828412289/50000000000000 : ℝ)*(sp0) + (123274411561931/6250000000000 : ℝ)*(sp1) + (197239381797659/10000000000000 : ℝ)*(sp2) + (371290525046517/50000000000000 : ℝ)*(sp3) + (17865991363/100000000000000 : ℝ)*(sp5) + (14633005669/100000000000000 : ℝ)*(sp6) + (1028413117/20000000000000 : ℝ)*(sp7) + (134926971/1250000000000 : ℝ)*(sp8) + (371293096079309/50000000000000 : ℝ)*(f.failure) + (1972408450982259/100000000000000 : ℝ)*(f.sum) + (4877221056621/954250000000000000000000000 : ℝ)*base66 + (114457974945067599/23856250000000000000000000000000 : ℝ)*base67 + (129022121910430099/23856250000000000000000000000000 : ℝ)*base69 + (75785445569538651/23856250000000000000000000000000 : ℝ)*base72 + (10851286325411/3817000000000000000000000000 : ℝ)*base74 + (16270149021069901/23856250000000000000000000000000 : ℝ)*base76 + (134054856022226151/23856250000000000000000000000000 : ℝ)*base78 + (33325853662594901/23856250000000000000000000000000 : ℝ)*base80 + (289973301643/763400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (7333781/1000000000000000000000 : ℝ)*base90 + (7333781/1000000000000000000000 : ℝ)*base92 + (7333781/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80333/100000 : ℝ) ≤ (95825583580310272512916584035241/119281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (522813/25000000000000 : ℝ)*(upper1) + (96296919/100000000000000 : ℝ)*(lower3) + (4830027/20000000000000 : ℝ)*(upper4) + (1404596360460781/100000000000000 : ℝ)*(major0) + (1404596360460781/100000000000000 : ℝ)*(major1) + (1404596360460781/100000000000000 : ℝ)*(major2) + (729775531/50000000000000 : ℝ)*(sp0) + (16107496493/100000000000000 : ℝ)*(sp2) + (13195525587/100000000000000 : ℝ)*(sp3) + (252432143286963/12500000000000 : ℝ)*(sp8) + (1009730492590447/50000000000000 : ℝ)*(sp9) + (5048612194211/250000000000 : ℝ)*(sp10) + (38146996491773/5000000000000 : ℝ)*(sp11) + (148708383/6250000000000 : ℝ)*(sp12) + (762953125361047/100000000000000 : ℝ)*(f.failure) + (1009730492590447/50000000000000 : ℝ)*(f.sum) + (6749389053383/1908500000000000000000000000 : ℝ)*base65 + (604329548417386747/238562500000000000000000000000000 : ℝ)*base68 + (973062269032550753/238562500000000000000000000000000 : ℝ)*base69 + (1171646246520738253/238562500000000000000000000000000 : ℝ)*base71 + (330775940681/954250000000000000000000000 : ℝ)*base73 + (621536142361074247/238562500000000000000000000000000 : ℝ)*base76 + (1057892167347800753/238562500000000000000000000000000 : ℝ)*base77 + (1046047856988050753/238562500000000000000000000000000 : ℝ)*base79 + (193346663413/59640625000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2290577/2000000000000000000000 : ℝ)*base89 + (2290577/2000000000000000000000 : ℝ)*base91 + (2290577/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17987/20000 : ℝ) ≤ (-3432737218377951416799165789/3817000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3133773/12500000000000 : ℝ)*(lower1) + (2782239/5000000000000 : ℝ)*(lower2) + (17468299/100000000000000 : ℝ)*(upper5) + (1450336474822699/100000000000000 : ℝ)*(major0) + (1450336474822699/100000000000000 : ℝ)*(major1) + (1450336474822699/100000000000000 : ℝ)*(major2) + (1001318599/100000000000000 : ℝ)*(sp0) + (38121775471/100000000000000 : ℝ)*(sp5) + (7854050583/20000000000000 : ℝ)*(sp6) + (5222025061/50000000000000 : ℝ)*(sp7) + (2142851181525697/100000000000000 : ℝ)*(sp12) + (267851757633603/12500000000000 : ℝ)*(sp13) + (2142812912591381/100000000000000 : ℝ)*(sp14) + (787787942333351/100000000000000 : ℝ)*(sp15) + (787798386383473/100000000000000 : ℝ)*(f.failure) + (267856522855537/12500000000000 : ℝ)*(f.sum) + (458600242679/763400000000000000000000000 : ℝ)*base66 + (1611671495850792513/238562500000000000000000000000000 : ℝ)*base68 + (47743508961332487/238562500000000000000000000000000 : ℝ)*base69 + (433613411366269987/238562500000000000000000000000000 : ℝ)*base71 + (10654624412697/1908500000000000000000000000 : ℝ)*base74 + (2570456565181144987/238562500000000000000000000000000 : ℝ)*base75 + (728579882804980013/238562500000000000000000000000000 : ℝ)*base78 + (1164594054877167513/238562500000000000000000000000000 : ℝ)*base80 + (14257054296307/3817000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (18408743/2000000000000000000000 : ℝ)*base89 + (18408743/2000000000000000000000 : ℝ)*base91 + (18408743/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1677_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8663/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2423/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2659/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(57619/100000 : ℝ) else (80333/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17987/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1677_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1677_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17363/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2659/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(57619/100000 : ℝ) else (80333/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17987/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1677_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1677_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1677_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17363/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2659/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(57619/100000 : ℝ) else (80333/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17987/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1677_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
