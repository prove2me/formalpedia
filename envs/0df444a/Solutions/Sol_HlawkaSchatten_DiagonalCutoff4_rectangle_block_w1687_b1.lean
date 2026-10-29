-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:38.179761+00:00
-- url     : https://prove2.me/submissions/4674ab67-6907-494d-81c7-f1ae5ab5f9dd

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
theorem support_rectangle_w1687_s3_0 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46866099/312500000 : ℝ)*x 0 + (1371313941/2500000000 : ℝ)*x 1 + (2567373841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46866099/312500000 : ℝ)^5119 ≤ (9331697996153/100000000000000 : ℝ)^4095 := by
    have hnat : (46866099 : ℕ)^5119*100000000000000^4095 ≤ 9331697996153^4095*312500000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46866099 312500000 9331697996153 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371313941/2500000000 : ℝ)^5119 ≤ (23602074961547/50000000000000 : ℝ)^4095 := by
    have hnat : (1371313941 : ℕ)^5119*50000000000000^4095 ≤ 23602074961547^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371313941 2500000000 23602074961547 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567373841/5000000000 : ℝ)^5119 ≤ (2173207603817/5000000000000 : ℝ)^4095 := by
    have hnat : (2567373841 : ℕ)^5119*5000000000000^4095 ≤ 2173207603817^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567373841 5000000000 2173207603817 5000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46866099/312500000 : ℝ), (1371313941/2500000000 : ℝ), (2567373841/5000000000 : ℝ)] ![(9331697996153/100000000000000 : ℝ), (23602074961547/50000000000000 : ℝ), (2173207603817/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46866099/312500000 : ℝ)|^5119 ≤ (9331697996153/100000000000000 : ℝ)^4095
        have hw : |(-46866099/312500000 : ℝ)|=(46866099/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371313941/2500000000 : ℝ)|^5119 ≤ (23602074961547/50000000000000 : ℝ)^4095
        have hw : |(1371313941/2500000000 : ℝ)|=(1371313941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567373841/5000000000 : ℝ)|^5119 ≤ (2173207603817/5000000000000 : ℝ)^4095
        have hw : |(2567373841/5000000000 : ℝ)|=(2567373841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s3_1 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351220067/10000000000 : ℝ)*x 0 + (-42045877/250000000 : ℝ)*x 1 + (2567373887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351220067/10000000000 : ℝ)^5119 ≤ (45766682889411/100000000000000 : ℝ)^4095 := by
    have hnat : (5351220067 : ℕ)^5119*100000000000000^4095 ≤ 45766682889411^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351220067 10000000000 45766682889411 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42045877/250000000 : ℝ)^5119 ≤ (5384582022627/50000000000000 : ℝ)^4095 := by
    have hnat : (42045877 : ℕ)^5119*50000000000000^4095 ≤ 5384582022627^4095*250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42045877 250000000 5384582022627 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567373887/5000000000 : ℝ)^5119 ≤ (43464153049829/100000000000000 : ℝ)^4095 := by
    have hnat : (2567373887 : ℕ)^5119*100000000000000^4095 ≤ 43464153049829^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567373887 5000000000 43464153049829 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351220067/10000000000 : ℝ), (-42045877/250000000 : ℝ), (2567373887/5000000000 : ℝ)] ![(45766682889411/100000000000000 : ℝ), (5384582022627/50000000000000 : ℝ), (43464153049829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351220067/10000000000 : ℝ)|^5119 ≤ (45766682889411/100000000000000 : ℝ)^4095
        have hw : |(5351220067/10000000000 : ℝ)|=(5351220067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42045877/250000000 : ℝ)|^5119 ≤ (5384582022627/50000000000000 : ℝ)^4095
        have hw : |(-42045877/250000000 : ℝ)|=(42045877/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567373887/5000000000 : ℝ)|^5119 ≤ (43464153049829/100000000000000 : ℝ)^4095
        have hw : |(2567373887/5000000000 : ℝ)|=(2567373887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s3_2 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675610097/5000000000 : ℝ)*x 0 + (5134747679/10000000000 : ℝ)*x 1 + (-420458759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675610097/5000000000 : ℝ)^5119 ≤ (22883342123599/50000000000000 : ℝ)^4095 := by
    have hnat : (2675610097 : ℕ)^5119*50000000000000^4095 ≤ 22883342123599^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675610097 5000000000 22883342123599 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134747679/10000000000 : ℝ)^5119 ≤ (10866038011149/25000000000000 : ℝ)^4095 := by
    have hnat : (5134747679 : ℕ)^5119*25000000000000^4095 ≤ 10866038011149^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134747679 10000000000 10866038011149 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420458759/2500000000 : ℝ)^5119 ≤ (538458184653/5000000000000 : ℝ)^4095 := by
    have hnat : (420458759 : ℕ)^5119*5000000000000^4095 ≤ 538458184653^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420458759 2500000000 538458184653 5000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675610097/5000000000 : ℝ), (5134747679/10000000000 : ℝ), (-420458759/2500000000 : ℝ)] ![(22883342123599/50000000000000 : ℝ), (10866038011149/25000000000000 : ℝ), (538458184653/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675610097/5000000000 : ℝ)|^5119 ≤ (22883342123599/50000000000000 : ℝ)^4095
        have hw : |(2675610097/5000000000 : ℝ)|=(2675610097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134747679/10000000000 : ℝ)|^5119 ≤ (10866038011149/25000000000000 : ℝ)^4095
        have hw : |(5134747679/10000000000 : ℝ)|=(5134747679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420458759/2500000000 : ℝ)|^5119 ≤ (538458184653/5000000000000 : ℝ)^4095
        have hw : |(-420458759/2500000000 : ℝ)|=(420458759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s3_3 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135375337/10000000000 : ℝ)*x 0 + (3672711457/10000000000 : ℝ)*x 1 + (4635769007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135375337/10000000000 : ℝ)^5119 ≤ (16580218869293/50000000000000 : ℝ)^4095 := by
    have hnat : (4135375337 : ℕ)^5119*50000000000000^4095 ≤ 16580218869293^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135375337 10000000000 16580218869293 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3672711457/10000000000 : ℝ)^5119 ≤ (14294762986443/50000000000000 : ℝ)^4095 := by
    have hnat : (3672711457 : ℕ)^5119*50000000000000^4095 ≤ 14294762986443^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3672711457 10000000000 14294762986443 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4635769007/10000000000 : ℝ)^5119 ≤ (19125018132613/50000000000000 : ℝ)^4095 := by
    have hnat : (4635769007 : ℕ)^5119*50000000000000^4095 ≤ 19125018132613^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635769007 10000000000 19125018132613 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135375337/10000000000 : ℝ), (3672711457/10000000000 : ℝ), (4635769007/10000000000 : ℝ)] ![(16580218869293/50000000000000 : ℝ), (14294762986443/50000000000000 : ℝ), (19125018132613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135375337/10000000000 : ℝ)|^5119 ≤ (16580218869293/50000000000000 : ℝ)^4095
        have hw : |(4135375337/10000000000 : ℝ)|=(4135375337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3672711457/10000000000 : ℝ)|^5119 ≤ (14294762986443/50000000000000 : ℝ)^4095
        have hw : |(3672711457/10000000000 : ℝ)|=(3672711457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4635769007/10000000000 : ℝ)|^5119 ≤ (19125018132613/50000000000000 : ℝ)^4095
        have hw : |(4635769007/10000000000 : ℝ)|=(4635769007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s3_4 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1499879043/10000000000 : ℝ)*x 0 + (5138552443/10000000000 : ℝ)*x 1 + (5481394133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1499879043/10000000000 : ℝ)^5119 ≤ (9332972677859/100000000000000 : ℝ)^4095 := by
    have hnat : (1499879043 : ℕ)^5119*100000000000000^4095 ≤ 9332972677859^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499879043 10000000000 9332972677859 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138552443/10000000000 : ℝ)^5119 ≤ (21752207760851/50000000000000 : ℝ)^4095 := by
    have hnat : (5138552443 : ℕ)^5119*50000000000000^4095 ≤ 21752207760851^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138552443 10000000000 21752207760851 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481394133/10000000000 : ℝ)^5119 ≤ (23581305890939/50000000000000 : ℝ)^4095 := by
    have hnat : (5481394133 : ℕ)^5119*50000000000000^4095 ≤ 23581305890939^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481394133 10000000000 23581305890939 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1499879043/10000000000 : ℝ), (5138552443/10000000000 : ℝ), (5481394133/10000000000 : ℝ)] ![(9332972677859/100000000000000 : ℝ), (21752207760851/50000000000000 : ℝ), (23581305890939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1499879043/10000000000 : ℝ)|^5119 ≤ (9332972677859/100000000000000 : ℝ)^4095
        have hw : |(-1499879043/10000000000 : ℝ)|=(1499879043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138552443/10000000000 : ℝ)|^5119 ≤ (21752207760851/50000000000000 : ℝ)^4095
        have hw : |(5138552443/10000000000 : ℝ)|=(5138552443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481394133/10000000000 : ℝ)|^5119 ≤ (23581305890939/50000000000000 : ℝ)^4095
        have hw : |(5481394133/10000000000 : ℝ)|=(5481394133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s3_5 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257543003/10000000000 : ℝ)*x 0 + (-166898607/1250000000 : ℝ)*x 1 + (5481394133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257543003/10000000000 : ℝ)^5119 ≤ (4476736120029/10000000000000 : ℝ)^4095 := by
    have hnat : (5257543003 : ℕ)^5119*10000000000000^4095 ≤ 4476736120029^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257543003 10000000000 4476736120029 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166898607/1250000000 : ℝ)^5119 ≤ (807002700373/10000000000000 : ℝ)^4095 := by
    have hnat : (166898607 : ℕ)^5119*10000000000000^4095 ≤ 807002700373^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166898607 1250000000 807002700373 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481394133/10000000000 : ℝ)^5119 ≤ (23581305890939/50000000000000 : ℝ)^4095 := by
    have hnat : (5481394133 : ℕ)^5119*50000000000000^4095 ≤ 23581305890939^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481394133 10000000000 23581305890939 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257543003/10000000000 : ℝ), (-166898607/1250000000 : ℝ), (5481394133/10000000000 : ℝ)] ![(4476736120029/10000000000000 : ℝ), (807002700373/10000000000000 : ℝ), (23581305890939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257543003/10000000000 : ℝ)|^5119 ≤ (4476736120029/10000000000000 : ℝ)^4095
        have hw : |(5257543003/10000000000 : ℝ)|=(5257543003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-166898607/1250000000 : ℝ)|^5119 ≤ (807002700373/10000000000000 : ℝ)^4095
        have hw : |(-166898607/1250000000 : ℝ)|=(166898607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481394133/10000000000 : ℝ)|^5119 ≤ (23581305890939/50000000000000 : ℝ)^4095
        have hw : |(5481394133/10000000000 : ℝ)|=(5481394133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s3_6 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257543003/10000000000 : ℝ)*x 0 + (5481394133/10000000000 : ℝ)*x 1 + (-166898607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257543003/10000000000 : ℝ)^5119 ≤ (4476736120029/10000000000000 : ℝ)^4095 := by
    have hnat : (5257543003 : ℕ)^5119*10000000000000^4095 ≤ 4476736120029^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257543003 10000000000 4476736120029 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481394133/10000000000 : ℝ)^5119 ≤ (23581305890939/50000000000000 : ℝ)^4095 := by
    have hnat : (5481394133 : ℕ)^5119*50000000000000^4095 ≤ 23581305890939^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481394133 10000000000 23581305890939 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166898607/1250000000 : ℝ)^5119 ≤ (807002700373/10000000000000 : ℝ)^4095 := by
    have hnat : (166898607 : ℕ)^5119*10000000000000^4095 ≤ 807002700373^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166898607 1250000000 807002700373 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257543003/10000000000 : ℝ), (5481394133/10000000000 : ℝ), (-166898607/1250000000 : ℝ)] ![(4476736120029/10000000000000 : ℝ), (23581305890939/50000000000000 : ℝ), (807002700373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257543003/10000000000 : ℝ)|^5119 ≤ (4476736120029/10000000000000 : ℝ)^4095
        have hw : |(5257543003/10000000000 : ℝ)|=(5257543003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481394133/10000000000 : ℝ)|^5119 ≤ (23581305890939/50000000000000 : ℝ)^4095
        have hw : |(5481394133/10000000000 : ℝ)|=(5481394133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166898607/1250000000 : ℝ)|^5119 ≤ (807002700373/10000000000000 : ℝ)^4095
        have hw : |(-166898607/1250000000 : ℝ)|=(166898607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s3_7 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2067912629/5000000000 : ℝ)*x 0 + (4625314939/10000000000 : ℝ)*x 1 + (920830483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067912629/5000000000 : ℝ)^5119 ≤ (33164947761173/100000000000000 : ℝ)^4095 := by
    have hnat : (2067912629 : ℕ)^5119*100000000000000^4095 ≤ 33164947761173^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067912629 5000000000 33164947761173 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4625314939/10000000000 : ℝ)^5119 ≤ (38142239911719/100000000000000 : ℝ)^4095 := by
    have hnat : (4625314939 : ℕ)^5119*100000000000000^4095 ≤ 38142239911719^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4625314939 10000000000 38142239911719 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920830483/2500000000 : ℝ)^5119 ≤ (573856246439/2000000000000 : ℝ)^4095 := by
    have hnat : (920830483 : ℕ)^5119*2000000000000^4095 ≤ 573856246439^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920830483 2500000000 573856246439 2000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067912629/5000000000 : ℝ), (4625314939/10000000000 : ℝ), (920830483/2500000000 : ℝ)] ![(33164947761173/100000000000000 : ℝ), (38142239911719/100000000000000 : ℝ), (573856246439/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067912629/5000000000 : ℝ)|^5119 ≤ (33164947761173/100000000000000 : ℝ)^4095
        have hw : |(2067912629/5000000000 : ℝ)|=(2067912629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4625314939/10000000000 : ℝ)|^5119 ≤ (38142239911719/100000000000000 : ℝ)^4095
        have hw : |(4625314939/10000000000 : ℝ)|=(4625314939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920830483/2500000000 : ℝ)|^5119 ≤ (573856246439/2000000000000 : ℝ)^4095
        have hw : |(920830483/2500000000 : ℝ)|=(920830483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1687_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8641/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (49/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17257/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8641/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8641/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8641/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8641/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8641/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8641/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9779/100000 : ℝ) ^ (5111/1024 : ℝ) ≤ (912738975133879/100000000000000000000 : ℝ) := by
    have hpowers : (9779/100000 : ℝ)^5111 ≤ (912738975133879/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9779 : ℕ)^5111*100000000000000000000^1024 ≤ 912738975133879^1024*100000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9779 100000 912738975133879 100000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9779/100000 : ℝ)) (X := (912738975133879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8641/50000 : ℝ) ^ (5111/1024 : ℝ) ≤ (15655640424305983/100000000000000000000 : ℝ) := by
    have hpowers : (8641/50000 : ℝ)^5111 ≤ (15655640424305983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8641 : ℕ)^5111*100000000000000000000^1024 ≤ 15655640424305983^1024*50000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8641 50000 15655640424305983 100000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8641/50000 : ℝ)) (X := (15655640424305983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000912738975133879/50000000000000000000 : ℝ) ≤ (2500009143395509/2500000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (50000912738975133879/50000000000000000000 : ℝ)^1024 ≤ (2500009143395509/2500000000000000 : ℝ)^5111 := by
      have hnat : (50000912738975133879 : ℕ)^1024*2500000000000000^5111 ≤ 2500009143395509^5111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000912738975133879 50000000000000000000 2500009143395509 2500000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009143395509/2500000000000000 : ℝ)) (X := (50000912738975133879/50000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008284189699719931/50000000000000000000 : ℝ) ≤ (5000165964554039/5000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (50008284189699719931/50000000000000000000 : ℝ)^1024 ≤ (5000165964554039/5000000000000000 : ℝ)^5111 := by
      have hnat : (50008284189699719931 : ℕ)^1024*5000000000000000^5111 ≤ 5000165964554039^5111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008284189699719931 50000000000000000000 5000165964554039 5000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000165964554039/5000000000000000 : ℝ)) (X := (50008284189699719931/50000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015655640424305983/50000000000000000000 : ℝ) ≤ (250015682115853/250000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (50015655640424305983/50000000000000000000 : ℝ)^1024 ≤ (250015682115853/250000000000000 : ℝ)^5111 := by
      have hnat : (50015655640424305983 : ℕ)^1024*250000000000000^5111 ≤ 250015682115853^5111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015655640424305983 50000000000000000000 250015682115853 250000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250015682115853/250000000000000 : ℝ)) (X := (50015655640424305983/50000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(912738975133879/100000000000000000000 : ℝ) ≤ ((1563010371837660139/1563125000000000000 : ℝ)+2*(49225921007/125050000000000 : ℝ)*(9779/100000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (1563010371837660139/1563125000000000000 : ℝ)+2*(49225921007/125050000000000 : ℝ)*(9779/100000 : ℝ)=(2500009143395509/2500000000000000 : ℝ) by norm_num, show 1+2*(912738975133879/100000000000000000000 : ℝ)=(50000912738975133879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15655640424305983/100000000000000000000 : ℝ)+(912738975133879/100000000000000000000 : ℝ) ≤ ((1563010371837660139/1563125000000000000 : ℝ)+(49225921007/125050000000000 : ℝ)*((8641/50000 : ℝ)+(9779/100000 : ℝ)))^(5111/1024 : ℝ) := by
    rw [show (1563010371837660139/1563125000000000000 : ℝ)+(49225921007/125050000000000 : ℝ)*((8641/50000 : ℝ)+(9779/100000 : ℝ))=(5000165964554039/5000000000000000 : ℝ) by norm_num, show 1+(15655640424305983/100000000000000000000 : ℝ)+(912738975133879/100000000000000000000 : ℝ)=(50008284189699719931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15655640424305983/100000000000000000000 : ℝ) ≤ ((1563010371837660139/1563125000000000000 : ℝ)+2*(49225921007/125050000000000 : ℝ)*(8641/50000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (1563010371837660139/1563125000000000000 : ℝ)+2*(49225921007/125050000000000 : ℝ)*(8641/50000 : ℝ)=(250015682115853/250000000000000 : ℝ) by norm_num, show 1+2*(15655640424305983/100000000000000000000 : ℝ)=(50015655640424305983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1563010371837660139/1563125000000000000 : ℝ)*(X 1 0+X 2 0)+(49225921007/125050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (8641/50000 : ℝ)) (c := (1563010371837660139/1563125000000000000 : ℝ)) (alpha := (49225921007/125050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1563010371837660139/1563125000000000000 : ℝ)*(X 0 1+X 2 1)+(49225921007/125050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (8641/50000 : ℝ)) (c := (1563010371837660139/1563125000000000000 : ℝ)) (alpha := (49225921007/125050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1563010371837660139/1563125000000000000 : ℝ)*(X 0 2+X 1 2)+(49225921007/125050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (8641/50000 : ℝ)) (c := (1563010371837660139/1563125000000000000 : ℝ)) (alpha := (49225921007/125050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-46866099/312500000 : ℝ)*X 0 0+(1371313941/2500000000 : ℝ)*X 0 1+(2567373841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351220067/10000000000 : ℝ)*X 1 0+(-42045877/250000000 : ℝ)*X 1 1+(2567373887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675610097/5000000000 : ℝ)*X 2 0+(5134747679/10000000000 : ℝ)*X 2 1+(-420458759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4135375337/10000000000 : ℝ)*X 0 0+(3672711457/10000000000 : ℝ)*X 0 1+(4635769007/10000000000 : ℝ)*X 0 2+(4135375337/10000000000 : ℝ)*X 1 0+(3672711457/10000000000 : ℝ)*X 1 1+(4635769007/10000000000 : ℝ)*X 1 2+(4135375337/10000000000 : ℝ)*X 2 0+(3672711457/10000000000 : ℝ)*X 2 1+(4635769007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1499879043/10000000000 : ℝ)*X 0 0+(5138552443/10000000000 : ℝ)*X 0 1+(5481394133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257543003/10000000000 : ℝ)*X 1 0+(-166898607/1250000000 : ℝ)*X 1 1+(5481394133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257543003/10000000000 : ℝ)*X 2 0+(5481394133/10000000000 : ℝ)*X 2 1+(-166898607/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2067912629/5000000000 : ℝ)*X 0 0+(4625314939/10000000000 : ℝ)*X 0 1+(920830483/2500000000 : ℝ)*X 0 2+(2067912629/5000000000 : ℝ)*X 1 0+(4625314939/10000000000 : ℝ)*X 1 1+(920830483/2500000000 : ℝ)*X 1 2+(2067912629/5000000000 : ℝ)*X 2 0+(4625314939/10000000000 : ℝ)*X 2 1+(920830483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28192752903692962621066749/3907812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (327490337/25000000000000 : ℝ)*(base19) + (1243304613/100000000000000 : ℝ)*(base23) + (71902929/100000000000000 : ℝ)*(lower2) + (47677569/25000000000000 : ℝ)*(upper3) + (128861831/100000000000000 : ℝ)*(upper5) + (194569919718377/10000000000000 : ℝ)*(major0) + (194569919718377/10000000000000 : ℝ)*(major1) + (194569919718377/10000000000000 : ℝ)*(major2) + (1426507335017483/50000000000000 : ℝ)*(sp0) + (285302700125817/10000000000000 : ℝ)*(sp1) + (570605413582981/20000000000000 : ℝ)*(sp2) + (519182152749319/50000000000000 : ℝ)*(sp3) + (1705148069/12500000000000 : ℝ)*(sp4) + (553716741/10000000000000 : ℝ)*(sp7) + (16224528791657/1562500000000 : ℝ)*(f.failure) + (1426514155609759/50000000000000 : ℝ)*(f.sum) + (9018396473603/1250500000000000000000000000 : ℝ)*base66 + (4468578110693583/381250000000000000000000000000 : ℝ)*base67 + (5987404644581083/381250000000000000000000000000 : ℝ)*base69 + (2994439887818583/381250000000000000000000000000 : ℝ)*base71 + (19790883687/12505000000000000000000000 : ℝ)*base74 + (7292678316631083/381250000000000000000000000000 : ℝ)*base75 + (875492731693583/381250000000000000000000000000 : ℝ)*base77 + (6987973066724833/381250000000000000000000000000 : ℝ)*base79 + (81935526611/50020000000000000000000000 : ℝ)*base81 + (50001/39062500000000000000 : ℝ)*base89 + (50001/39062500000000000000 : ℝ)*base91 + (50001/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (431497695331302157683792603/39078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1577537593/100000000000000 : ℝ)*(base19) + (1701596133/100000000000000 : ℝ)*(base23) + (238274389/50000000000000 : ℝ)*(lower1) + (118139143/50000000000000 : ℝ)*(upper3) + (55456981/100000000000000 : ℝ)*(lower4) + (57531653/25000000000000 : ℝ)*(upper5) + (994589410373283/50000000000000 : ℝ)*(major0) + (994589410373283/50000000000000 : ℝ)*(major1) + (994589410373283/50000000000000 : ℝ)*(major2) + (521329107/50000000000000 : ℝ)*(sp2) + (1458391734473157/50000000000000 : ℝ)*(sp4) + (36459773642609/1250000000000 : ℝ)*(sp5) + (2916780724691967/100000000000000 : ℝ)*(sp6) + (1061573804482667/100000000000000 : ℝ)*(sp7) + (1061573804482667/100000000000000 : ℝ)*(f.failure) + (1458391734473157/50000000000000 : ℝ)*(f.sum) + (3180790075999/3126250000000000000000000000 : ℝ)*base66 + (6900987443922807/1906250000000000000000000000000 : ℝ)*base67 + (668771320170943/1906250000000000000000000000000 : ℝ)*base70 + (3011890828579057/1906250000000000000000000000000 : ℝ)*base71 + (7912892078541/12505000000000000000000000000 : ℝ)*base74 + (41914062933641557/1906250000000000000000000000000 : ℝ)*base75 + (4958659588672807/1906250000000000000000000000000 : ℝ)*base77 + (18276973109079057/1906250000000000000000000000000 : ℝ)*base79 + (996142936531/195390625000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (21630319/2500000000000000000000 : ℝ)*base90 + (21630319/2500000000000000000000 : ℝ)*base92 + (21630319/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1687_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8641/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (49/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17257/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1687_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1687_s4_0 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-749864729/5000000000 : ℝ)*x 0 + (5485198267/10000000000 : ℝ)*x 1 + (513479563/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749864729/5000000000 : ℝ)^5119 ≤ (933180914779/10000000000000 : ℝ)^4095 := by
    have hnat : (749864729 : ℕ)^5119*10000000000000^4095 ≤ 933180914779^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749864729 5000000000 933180914779 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485198267/10000000000 : ℝ)^5119 ≤ (47203531395417/100000000000000 : ℝ)^4095 := by
    have hnat : (5485198267 : ℕ)^5119*100000000000000^4095 ≤ 47203531395417^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485198267 10000000000 47203531395417 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513479563/1000000000 : ℝ)^5119 ≤ (2716541214633/6250000000000 : ℝ)^4095 := by
    have hnat : (513479563 : ℕ)^5119*6250000000000^4095 ≤ 2716541214633^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513479563 1000000000 2716541214633 6250000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-749864729/5000000000 : ℝ), (5485198267/10000000000 : ℝ), (513479563/1000000000 : ℝ)] ![(933180914779/10000000000000 : ℝ), (47203531395417/100000000000000 : ℝ), (2716541214633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-749864729/5000000000 : ℝ)|^5119 ≤ (933180914779/10000000000000 : ℝ)^4095
        have hw : |(-749864729/5000000000 : ℝ)|=(749864729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485198267/10000000000 : ℝ)|^5119 ≤ (47203531395417/100000000000000 : ℝ)^4095
        have hw : |(5485198267/10000000000 : ℝ)|=(5485198267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513479563/1000000000 : ℝ)|^5119 ≤ (2716541214633/6250000000000 : ℝ)^4095
        have hw : |(513479563/1000000000 : ℝ)|=(513479563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s4_1 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351202227/10000000000 : ℝ)*x 0 + (-420449053/2500000000 : ℝ)*x 1 + (5134795201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351202227/10000000000 : ℝ)^5119 ≤ (45766492157871/100000000000000 : ℝ)^4095 := by
    have hnat : (5351202227 : ℕ)^5119*100000000000000^4095 ≤ 45766492157871^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351202227 10000000000 45766492157871 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420449053/2500000000 : ℝ)^5119 ≤ (10768852930399/100000000000000 : ℝ)^4095 := by
    have hnat : (420449053 : ℕ)^5119*100000000000000^4095 ≤ 10768852930399^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420449053 2500000000 10768852930399 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134795201/10000000000 : ℝ)^5119 ≤ (8692930978939/20000000000000 : ℝ)^4095 := by
    have hnat : (5134795201 : ℕ)^5119*20000000000000^4095 ≤ 8692930978939^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134795201 10000000000 8692930978939 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351202227/10000000000 : ℝ), (-420449053/2500000000 : ℝ), (5134795201/10000000000 : ℝ)] ![(45766492157871/100000000000000 : ℝ), (10768852930399/100000000000000 : ℝ), (8692930978939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351202227/10000000000 : ℝ)|^5119 ≤ (45766492157871/100000000000000 : ℝ)^4095
        have hw : |(5351202227/10000000000 : ℝ)|=(5351202227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420449053/2500000000 : ℝ)|^5119 ≤ (10768852930399/100000000000000 : ℝ)^4095
        have hw : |(-420449053/2500000000 : ℝ)|=(420449053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134795201/10000000000 : ℝ)|^5119 ≤ (8692930978939/20000000000000 : ℝ)^4095
        have hw : |(5134795201/10000000000 : ℝ)|=(5134795201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s4_2 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351205289/10000000000 : ℝ)*x 0 + (5134794451/10000000000 : ℝ)*x 1 + (-840896557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351205289/10000000000 : ℝ)^5119 ≤ (9153304978881/20000000000000 : ℝ)^4095 := by
    have hnat : (5351205289 : ℕ)^5119*20000000000000^4095 ≤ 9153304978881^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351205289 10000000000 9153304978881 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134794451/10000000000 : ℝ)^5119 ≤ (43464646958623/100000000000000 : ℝ)^4095 := by
    have hnat : (5134794451 : ℕ)^5119*100000000000000^4095 ≤ 43464646958623^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134794451 10000000000 43464646958623 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840896557/5000000000 : ℝ)^5119 ≤ (5384414066429/50000000000000 : ℝ)^4095 := by
    have hnat : (840896557 : ℕ)^5119*50000000000000^4095 ≤ 5384414066429^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840896557 5000000000 5384414066429 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351205289/10000000000 : ℝ), (5134794451/10000000000 : ℝ), (-840896557/5000000000 : ℝ)] ![(9153304978881/20000000000000 : ℝ), (43464646958623/100000000000000 : ℝ), (5384414066429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351205289/10000000000 : ℝ)|^5119 ≤ (9153304978881/20000000000000 : ℝ)^4095
        have hw : |(5351205289/10000000000 : ℝ)|=(5351205289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134794451/10000000000 : ℝ)|^5119 ≤ (43464646958623/100000000000000 : ℝ)^4095
        have hw : |(5134794451/10000000000 : ℝ)|=(5134794451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-840896557/5000000000 : ℝ)|^5119 ≤ (5384414066429/50000000000000 : ℝ)^4095
        have hw : |(-840896557/5000000000 : ℝ)|=(840896557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s4_3 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135385193/10000000000 : ℝ)*x 0 + (734571621/2000000000 : ℝ)*x 1 + (1158905269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135385193/10000000000 : ℝ)^5119 ≤ (33160536534133/100000000000000 : ℝ)^4095 := by
    have hnat : (4135385193 : ℕ)^5119*100000000000000^4095 ≤ 33160536534133^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135385193 10000000000 33160536534133 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (734571621/2000000000 : ℝ)^5119 ≤ (28590952991641/100000000000000 : ℝ)^4095 := by
    have hnat : (734571621 : ℕ)^5119*100000000000000^4095 ≤ 28590952991641^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734571621 2000000000 28590952991641 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158905269/2500000000 : ℝ)^5119 ≤ (2390531903827/6250000000000 : ℝ)^4095 := by
    have hnat : (1158905269 : ℕ)^5119*6250000000000^4095 ≤ 2390531903827^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158905269 2500000000 2390531903827 6250000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135385193/10000000000 : ℝ), (734571621/2000000000 : ℝ), (1158905269/2500000000 : ℝ)] ![(33160536534133/100000000000000 : ℝ), (28590952991641/100000000000000 : ℝ), (2390531903827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135385193/10000000000 : ℝ)|^5119 ≤ (33160536534133/100000000000000 : ℝ)^4095
        have hw : |(4135385193/10000000000 : ℝ)|=(4135385193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(734571621/2000000000 : ℝ)|^5119 ≤ (28590952991641/100000000000000 : ℝ)^4095
        have hw : |(734571621/2000000000 : ℝ)|=(734571621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1158905269/2500000000 : ℝ)|^5119 ≤ (2390531903827/6250000000000 : ℝ)^4095
        have hw : |(1158905269/2500000000 : ℝ)|=(1158905269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s4_4 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-299978899/2000000000 : ℝ)*x 0 + (5138597789/10000000000 : ℝ)*x 1 + (5481338339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299978899/2000000000 : ℝ)^5119 ≤ (9333092871153/100000000000000 : ℝ)^4095 := by
    have hnat : (299978899 : ℕ)^5119*100000000000000^4095 ≤ 9333092871153^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299978899 2000000000 9333092871153 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138597789/10000000000 : ℝ)^5119 ≤ (8700979087099/20000000000000 : ℝ)^4095 := by
    have hnat : (5138597789 : ℕ)^5119*20000000000000^4095 ≤ 8700979087099^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138597789 10000000000 8700979087099 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481338339/10000000000 : ℝ)^5119 ≤ (294762573/625000000 : ℝ)^4095 := by
    have hnat : (5481338339 : ℕ)^5119*625000000^4095 ≤ 294762573^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481338339 10000000000 294762573 625000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-299978899/2000000000 : ℝ), (5138597789/10000000000 : ℝ), (5481338339/10000000000 : ℝ)] ![(9333092871153/100000000000000 : ℝ), (8700979087099/20000000000000 : ℝ), (294762573/625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-299978899/2000000000 : ℝ)|^5119 ≤ (9333092871153/100000000000000 : ℝ)^4095
        have hw : |(-299978899/2000000000 : ℝ)|=(299978899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138597789/10000000000 : ℝ)|^5119 ≤ (8700979087099/20000000000000 : ℝ)^4095
        have hw : |(5138597789/10000000000 : ℝ)|=(5138597789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481338339/10000000000 : ℝ)|^5119 ≤ (294762573/625000000 : ℝ)^4095
        have hw : |(5481338339/10000000000 : ℝ)|=(5481338339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s4_5 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628777707/5000000000 : ℝ)*x 0 + (-133525083/1000000000 : ℝ)*x 1 + (1370334579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628777707/5000000000 : ℝ)^5119 ≤ (2238374665227/5000000000000 : ℝ)^4095 := by
    have hnat : (2628777707 : ℕ)^5119*5000000000000^4095 ≤ 2238374665227^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628777707 5000000000 2238374665227 5000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133525083/1000000000 : ℝ)^5119 ≤ (807049525133/10000000000000 : ℝ)^4095 := by
    have hnat : (133525083 : ℕ)^5119*10000000000000^4095 ≤ 807049525133^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133525083 1000000000 807049525133 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370334579/2500000000 : ℝ)^5119 ≤ (2358100571631/5000000000000 : ℝ)^4095 := by
    have hnat : (1370334579 : ℕ)^5119*5000000000000^4095 ≤ 2358100571631^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370334579 2500000000 2358100571631 5000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628777707/5000000000 : ℝ), (-133525083/1000000000 : ℝ), (1370334579/2500000000 : ℝ)] ![(2238374665227/5000000000000 : ℝ), (807049525133/10000000000000 : ℝ), (2358100571631/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628777707/5000000000 : ℝ)|^5119 ≤ (2238374665227/5000000000000 : ℝ)^4095
        have hw : |(2628777707/5000000000 : ℝ)|=(2628777707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133525083/1000000000 : ℝ)|^5119 ≤ (807049525133/10000000000000 : ℝ)^4095
        have hw : |(-133525083/1000000000 : ℝ)|=(133525083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370334579/2500000000 : ℝ)|^5119 ≤ (2358100571631/5000000000000 : ℝ)^4095
        have hw : |(1370334579/2500000000 : ℝ)|=(1370334579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s4_6 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628777697/5000000000 : ℝ)*x 0 + (548133837/1000000000 : ℝ)*x 1 + (-1335250781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628777697/5000000000 : ℝ)^5119 ≤ (44767493091657/100000000000000 : ℝ)^4095 := by
    have hnat : (2628777697 : ℕ)^5119*100000000000000^4095 ≤ 44767493091657^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628777697 5000000000 44767493091657 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548133837/1000000000 : ℝ)^5119 ≤ (1886480480537/4000000000000 : ℝ)^4095 := by
    have hnat : (548133837 : ℕ)^5119*4000000000000^4095 ≤ 1886480480537^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548133837 1000000000 1886480480537 4000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1335250781/10000000000 : ℝ)^5119 ≤ (4035247440553/50000000000000 : ℝ)^4095 := by
    have hnat : (1335250781 : ℕ)^5119*50000000000000^4095 ≤ 4035247440553^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335250781 10000000000 4035247440553 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628777697/5000000000 : ℝ), (548133837/1000000000 : ℝ), (-1335250781/10000000000 : ℝ)] ![(44767493091657/100000000000000 : ℝ), (1886480480537/4000000000000 : ℝ), (4035247440553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628777697/5000000000 : ℝ)|^5119 ≤ (44767493091657/100000000000000 : ℝ)^4095
        have hw : |(2628777697/5000000000 : ℝ)|=(2628777697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548133837/1000000000 : ℝ)|^5119 ≤ (1886480480537/4000000000000 : ℝ)^4095
        have hw : |(548133837/1000000000 : ℝ)|=(548133837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1335250781/10000000000 : ℝ)|^5119 ≤ (4035247440553/50000000000000 : ℝ)^4095
        have hw : |(-1335250781/10000000000 : ℝ)|=(1335250781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s4_7 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135835201/10000000000 : ℝ)*x 0 + (2312587507/5000000000 : ℝ)*x 1 + (3683459819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135835201/10000000000 : ℝ)^5119 ≤ (3316504743151/10000000000000 : ℝ)^4095 := by
    have hnat : (4135835201 : ℕ)^5119*10000000000000^4095 ≤ 3316504743151^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135835201 10000000000 3316504743151 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2312587507/5000000000 : ℝ)^5119 ≤ (9535199374553/25000000000000 : ℝ)^4095 := by
    have hnat : (2312587507 : ℕ)^5119*25000000000000^4095 ≤ 9535199374553^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312587507 5000000000 9535199374553 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3683459819/10000000000 : ℝ)^5119 ≤ (28694155056047/100000000000000 : ℝ)^4095 := by
    have hnat : (3683459819 : ℕ)^5119*100000000000000^4095 ≤ 28694155056047^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683459819 10000000000 28694155056047 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135835201/10000000000 : ℝ), (2312587507/5000000000 : ℝ), (3683459819/10000000000 : ℝ)] ![(3316504743151/10000000000000 : ℝ), (9535199374553/25000000000000 : ℝ), (28694155056047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135835201/10000000000 : ℝ)|^5119 ≤ (3316504743151/10000000000000 : ℝ)^4095
        have hw : |(4135835201/10000000000 : ℝ)|=(4135835201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2312587507/5000000000 : ℝ)|^5119 ≤ (9535199374553/25000000000000 : ℝ)^4095
        have hw : |(2312587507/5000000000 : ℝ)|=(2312587507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3683459819/10000000000 : ℝ)|^5119 ≤ (28694155056047/100000000000000 : ℝ)^4095
        have hw : |(3683459819/10000000000 : ℝ)|=(3683459819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1687_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (49/500 : ℝ)*pair X i i ≤ pair X i h) :
    (9801/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2157/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (49/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (49/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (49/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (49/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (49/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (49/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (49/500 : ℝ) ^ (5111/1024 : ℝ) ≤ (36902564404089/4000000000000000000 : ℝ) := by
    have hpowers : (49/500 : ℝ)^5111 ≤ (36902564404089/4000000000000000000 : ℝ)^1024 := by
      have hnat : (49 : ℕ)^5111*4000000000000000000^1024 ≤ 36902564404089^1024*500^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49 500 36902564404089 4000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (49/500 : ℝ)) (X := (36902564404089/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17257/100000 : ℝ) ^ (5111/1024 : ℝ) ≤ (621717148595997/4000000000000000000 : ℝ) := by
    have hpowers : (17257/100000 : ℝ)^5111 ≤ (621717148595997/4000000000000000000 : ℝ)^1024 := by
      have hnat : (17257 : ℕ)^5111*4000000000000000000^1024 ≤ 621717148595997^1024*100000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17257 100000 621717148595997 4000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17257/100000 : ℝ)) (X := (621717148595997/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000036902564404089/2000000000000000000 : ℝ) ≤ (10000036967273703/10000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (2000036902564404089/2000000000000000000 : ℝ)^1024 ≤ (10000036967273703/10000000000000000 : ℝ)^5111 := by
      have hnat : (2000036902564404089 : ℕ)^1024*10000000000000000^5111 ≤ 10000036967273703^5111*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000036902564404089 2000000000000000000 10000036967273703 10000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036967273703/10000000000000000 : ℝ)) (X := (2000036902564404089/2000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000329309856500043/2000000000000000000 : ℝ) ≤ (2500082467006333/2500000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (2000329309856500043/2000000000000000000 : ℝ)^1024 ≤ (2500082467006333/2500000000000000 : ℝ)^5111 := by
      have hnat : (2000329309856500043 : ℕ)^1024*2500000000000000^5111 ≤ 2500082467006333^5111*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000329309856500043 2000000000000000000 2500082467006333 2500000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500082467006333/2500000000000000 : ℝ)) (X := (2000329309856500043/2000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000621717148595997/2000000000000000000 : ℝ) ≤ (10000622768776961/10000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (2000621717148595997/2000000000000000000 : ℝ)^1024 ≤ (10000622768776961/10000000000000000 : ℝ)^5111 := by
      have hnat : (2000621717148595997 : ℕ)^1024*10000000000000000^5111 ≤ 10000622768776961^5111*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000621717148595997 2000000000000000000 10000622768776961 10000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000622768776961/10000000000000000 : ℝ)) (X := (2000621717148595997/2000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(36902564404089/4000000000000000000 : ℝ) ≤ ((74564534810228074871/74570000000000000000 : ℝ)+2*(292900751629/745700000000000 : ℝ)*(49/500 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (74564534810228074871/74570000000000000000 : ℝ)+2*(292900751629/745700000000000 : ℝ)*(49/500 : ℝ)=(10000036967273703/10000000000000000 : ℝ) by norm_num, show 1+2*(36902564404089/4000000000000000000 : ℝ)=(2000036902564404089/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(621717148595997/4000000000000000000 : ℝ)+(36902564404089/4000000000000000000 : ℝ) ≤ ((74564534810228074871/74570000000000000000 : ℝ)+(292900751629/745700000000000 : ℝ)*((17257/100000 : ℝ)+(49/500 : ℝ)))^(5111/1024 : ℝ) := by
    rw [show (74564534810228074871/74570000000000000000 : ℝ)+(292900751629/745700000000000 : ℝ)*((17257/100000 : ℝ)+(49/500 : ℝ))=(2500082467006333/2500000000000000 : ℝ) by norm_num, show 1+(621717148595997/4000000000000000000 : ℝ)+(36902564404089/4000000000000000000 : ℝ)=(2000329309856500043/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(621717148595997/4000000000000000000 : ℝ) ≤ ((74564534810228074871/74570000000000000000 : ℝ)+2*(292900751629/745700000000000 : ℝ)*(17257/100000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (74564534810228074871/74570000000000000000 : ℝ)+2*(292900751629/745700000000000 : ℝ)*(17257/100000 : ℝ)=(10000622768776961/10000000000000000 : ℝ) by norm_num, show 1+2*(621717148595997/4000000000000000000 : ℝ)=(2000621717148595997/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74564534810228074871/74570000000000000000 : ℝ)*(X 1 0+X 2 0)+(292900751629/745700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (49/500 : ℝ)) (hi := (17257/100000 : ℝ)) (c := (74564534810228074871/74570000000000000000 : ℝ)) (alpha := (292900751629/745700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74564534810228074871/74570000000000000000 : ℝ)*(X 0 1+X 2 1)+(292900751629/745700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (49/500 : ℝ)) (hi := (17257/100000 : ℝ)) (c := (74564534810228074871/74570000000000000000 : ℝ)) (alpha := (292900751629/745700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74564534810228074871/74570000000000000000 : ℝ)*(X 0 2+X 1 2)+(292900751629/745700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (49/500 : ℝ)) (hi := (17257/100000 : ℝ)) (c := (74564534810228074871/74570000000000000000 : ℝ)) (alpha := (292900751629/745700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-749864729/5000000000 : ℝ)*X 0 0+(5485198267/10000000000 : ℝ)*X 0 1+(513479563/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351202227/10000000000 : ℝ)*X 1 0+(-420449053/2500000000 : ℝ)*X 1 1+(5134795201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351205289/10000000000 : ℝ)*X 2 0+(5134794451/10000000000 : ℝ)*X 2 1+(-840896557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4135385193/10000000000 : ℝ)*X 0 0+(734571621/2000000000 : ℝ)*X 0 1+(1158905269/2500000000 : ℝ)*X 0 2+(4135385193/10000000000 : ℝ)*X 1 0+(734571621/2000000000 : ℝ)*X 1 1+(1158905269/2500000000 : ℝ)*X 1 2+(4135385193/10000000000 : ℝ)*X 2 0+(734571621/2000000000 : ℝ)*X 2 1+(1158905269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-299978899/2000000000 : ℝ)*X 0 0+(5138597789/10000000000 : ℝ)*X 0 1+(5481338339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628777707/5000000000 : ℝ)*X 1 0+(-133525083/1000000000 : ℝ)*X 1 1+(1370334579/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628777697/5000000000 : ℝ)*X 2 0+(548133837/1000000000 : ℝ)*X 2 1+(-1335250781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4135835201/10000000000 : ℝ)*X 0 0+(2312587507/5000000000 : ℝ)*X 0 1+(3683459819/10000000000 : ℝ)*X 0 2+(4135835201/10000000000 : ℝ)*X 1 0+(2312587507/5000000000 : ℝ)*X 1 1+(3683459819/10000000000 : ℝ)*X 1 2+(4135835201/10000000000 : ℝ)*X 2 0+(2312587507/5000000000 : ℝ)*X 2 1+(3683459819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3880719998510142712346742027/372850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35988091/4000000000000 : ℝ)*(base23) + (48170527/10000000000000 : ℝ)*(lower2) + (21711907/25000000000000 : ℝ)*(upper4) + (21338081/100000000000000 : ℝ)*(upper5) + (194627818724907/10000000000000 : ℝ)*(major0) + (194627818724907/10000000000000 : ℝ)*(major1) + (194627818724907/10000000000000 : ℝ)*(major2) + (1426930958071707/50000000000000 : ℝ)*(sp0) + (2853858383229157/100000000000000 : ℝ)*(sp1) + (11415505172059/400000000000 : ℝ)*(sp2) + (519338067011001/50000000000000 : ℝ)*(sp3) + (15276573611/100000000000000 : ℝ)*(sp4) + (4702371967/25000000000000 : ℝ)*(sp5) + (67520427/2500000000000 : ℝ)*(sp7) + (1038678834839083/100000000000000 : ℝ)*(f.failure) + (114155087708681/4000000000000 : ℝ)*(f.sum) + (9172698881093/7457000000000000000000000000 : ℝ)*base65 + (5363249088920911997/745700000000000000000000000000000 : ℝ)*base67 + (7252926956319111997/745700000000000000000000000000000 : ℝ)*base69 + (5793947131813911997/745700000000000000000000000000000 : ℝ)*base71 + (3291786176383/932125000000000000000000000 : ℝ)*base73 + (8548973767771911997/745700000000000000000000000000000 : ℝ)*base75 + (2367781682427611997/745700000000000000000000000000000 : ℝ)*base77 + (10147255647492811997/745700000000000000000000000000000 : ℝ)*base79 + (16838190138701/3728500000000000000000000000 : ℝ)*base81 + (8784431/2500000000000000000000 : ℝ)*base90 + (8784431/2500000000000000000000 : ℝ)*base92 + (8784431/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24568795249192426112158641/1820556640625000000000000000000 : ℝ) := by norm_num
    linear_combination (1975466959/100000000000000 : ℝ)*(base19) + (2090248957/100000000000000 : ℝ)*(base23) + (147958859/25000000000000 : ℝ)*(lower1) + (294100677/100000000000000 : ℝ)*(upper3) + (25963837/50000000000000 : ℝ)*(lower4) + (138987629/50000000000000 : ℝ)*(upper5) + (7772513574781/390625000000 : ℝ)*(major0) + (7772513574781/390625000000 : ℝ)*(major1) + (7772513574781/390625000000 : ℝ)*(major2) + (1522145273/100000000000000 : ℝ)*(sp2) + (2917640680882819/100000000000000 : ℝ)*(sp4) + (145881935270793/5000000000000 : ℝ)*(sp5) + (2917637068488589/100000000000000 : ℝ)*(sp6) + (132735727445587/12500000000000 : ℝ)*(sp7) + (132735727445587/12500000000000 : ℝ)*(f.failure) + (2917640680882819/100000000000000 : ℝ)*(f.sum) + (36867696794809/37285000000000000000000000000 : ℝ)*base65 + (18149502253296371/116515625000000000000000000000000 : ℝ)*base68 + (512095078659047379/116515625000000000000000000000000 : ℝ)*base69 + (94249658830734249/29128906250000000000000000000000 : ℝ)*base72 + (7031710011213/4660625000000000000000000000 : ℝ)*base73 + (419866452690609501/29128906250000000000000000000000 : ℝ)*base75 + (163062190007483871/116515625000000000000000000000000 : ℝ)*base78 + (475782430252265121/116515625000000000000000000000000 : ℝ)*base80 + (35486806208761/37285000000000000000000000000 : ℝ)*base82 + (3175241/312500000000000000000 : ℝ)*base89 + (3175241/312500000000000000000 : ℝ)*base91 + (3175241/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1687_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (49/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2157/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1687_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1687_s5_0 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070240599/2000000000 : ℝ)*x 0 + (-840894977/5000000000 : ℝ)*x 1 + (5134799159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070240599/2000000000 : ℝ)^5119 ≤ (11441625092183/25000000000000 : ℝ)^4095 := by
    have hnat : (1070240599 : ℕ)^5119*25000000000000^4095 ≤ 11441625092183^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070240599 2000000000 11441625092183 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (840894977/5000000000 : ℝ)^5119 ≤ (5384401419529/50000000000000 : ℝ)^4095 := by
    have hnat : (840894977 : ℕ)^5119*50000000000000^4095 ≤ 5384401419529^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840894977 5000000000 5384401419529 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134799159/10000000000 : ℝ)^5119 ≤ (10866174193999/25000000000000 : ℝ)^4095 := by
    have hnat : (5134799159 : ℕ)^5119*25000000000000^4095 ≤ 10866174193999^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134799159 10000000000 10866174193999 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070240599/2000000000 : ℝ), (-840894977/5000000000 : ℝ), (5134799159/10000000000 : ℝ)] ![(11441625092183/25000000000000 : ℝ), (5384401419529/50000000000000 : ℝ), (10866174193999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070240599/2000000000 : ℝ)|^5119 ≤ (11441625092183/25000000000000 : ℝ)^4095
        have hw : |(1070240599/2000000000 : ℝ)|=(1070240599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-840894977/5000000000 : ℝ)|^5119 ≤ (5384401419529/50000000000000 : ℝ)^4095
        have hw : |(-840894977/5000000000 : ℝ)|=(840894977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134799159/10000000000 : ℝ)|^5119 ≤ (10866174193999/25000000000000 : ℝ)^4095
        have hw : |(5134799159/10000000000 : ℝ)|=(5134799159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s5_1 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1499895017/10000000000 : ℝ)*x 0 + (1284649933/2500000000 : ℝ)*x 1 + (5481336049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1499895017/10000000000 : ℝ)^5119 ≤ (9333096931533/100000000000000 : ℝ)^4095 := by
    have hnat : (1499895017 : ℕ)^5119*100000000000000^4095 ≤ 9333096931533^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499895017 10000000000 9333096931533 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284649933/2500000000 : ℝ)^5119 ≤ (43504915999019/100000000000000 : ℝ)^4095 := by
    have hnat : (1284649933 : ℕ)^5119*100000000000000^4095 ≤ 43504915999019^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284649933 2500000000 43504915999019 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481336049/10000000000 : ℝ)^5119 ≤ (47161987049547/100000000000000 : ℝ)^4095 := by
    have hnat : (5481336049 : ℕ)^5119*100000000000000^4095 ≤ 47161987049547^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481336049 10000000000 47161987049547 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1499895017/10000000000 : ℝ), (1284649933/2500000000 : ℝ), (5481336049/10000000000 : ℝ)] ![(9333096931533/100000000000000 : ℝ), (43504915999019/100000000000000 : ℝ), (47161987049547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1499895017/10000000000 : ℝ)|^5119 ≤ (9333096931533/100000000000000 : ℝ)^4095
        have hw : |(-1499895017/10000000000 : ℝ)|=(1499895017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284649933/2500000000 : ℝ)|^5119 ≤ (43504915999019/100000000000000 : ℝ)^4095
        have hw : |(1284649933/2500000000 : ℝ)|=(1284649933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481336049/10000000000 : ℝ)|^5119 ≤ (47161987049547/100000000000000 : ℝ)^4095
        have hw : |(5481336049/10000000000 : ℝ)|=(5481336049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s5_2 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628777971/5000000000 : ℝ)*x 0 + (-166906663/1250000000 : ℝ)*x 1 + (1096267211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628777971/5000000000 : ℝ)^5119 ≤ (279796868279/625000000000 : ℝ)^4095 := by
    have hnat : (2628777971 : ℕ)^5119*625000000000^4095 ≤ 279796868279^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628777971 5000000000 279796868279 625000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166906663/1250000000 : ℝ)^5119 ≤ (126101780373/1562500000000 : ℝ)^4095 := by
    have hnat : (166906663 : ℕ)^5119*1562500000000^4095 ≤ 126101780373^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166906663 1250000000 126101780373 1562500000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096267211/2000000000 : ℝ)^5119 ≤ (47161987114081/100000000000000 : ℝ)^4095 := by
    have hnat : (1096267211 : ℕ)^5119*100000000000000^4095 ≤ 47161987114081^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096267211 2000000000 47161987114081 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628777971/5000000000 : ℝ), (-166906663/1250000000 : ℝ), (1096267211/2000000000 : ℝ)] ![(279796868279/625000000000 : ℝ), (126101780373/1562500000000 : ℝ), (47161987114081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628777971/5000000000 : ℝ)|^5119 ≤ (279796868279/625000000000 : ℝ)^4095
        have hw : |(2628777971/5000000000 : ℝ)|=(2628777971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-166906663/1250000000 : ℝ)|^5119 ≤ (126101780373/1562500000000 : ℝ)^4095
        have hw : |(-166906663/1250000000 : ℝ)|=(166906663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096267211/2000000000 : ℝ)|^5119 ≤ (47161987114081/100000000000000 : ℝ)^4095
        have hw : |(1096267211/2000000000 : ℝ)|=(1096267211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s5_3 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628777979/5000000000 : ℝ)*x 0 + (2740668011/5000000000 : ℝ)*x 1 + (-83453333/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628777979/5000000000 : ℝ)^5119 ≤ (22383749547473/50000000000000 : ℝ)^4095 := by
    have hnat : (2628777979 : ℕ)^5119*50000000000000^4095 ≤ 22383749547473^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628777979 5000000000 22383749547473 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740668011/5000000000 : ℝ)^5119 ≤ (5895248344893/12500000000000 : ℝ)^4095 := by
    have hnat : (2740668011 : ℕ)^5119*12500000000000^4095 ≤ 5895248344893^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740668011 5000000000 5895248344893 12500000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83453333/625000000 : ℝ)^5119 ≤ (4035257062603/50000000000000 : ℝ)^4095 := by
    have hnat : (83453333 : ℕ)^5119*50000000000000^4095 ≤ 4035257062603^4095*625000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83453333 625000000 4035257062603 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628777979/5000000000 : ℝ), (2740668011/5000000000 : ℝ), (-83453333/625000000 : ℝ)] ![(22383749547473/50000000000000 : ℝ), (5895248344893/12500000000000 : ℝ), (4035257062603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628777979/5000000000 : ℝ)|^5119 ≤ (22383749547473/50000000000000 : ℝ)^4095
        have hw : |(2628777979/5000000000 : ℝ)|=(2628777979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740668011/5000000000 : ℝ)|^5119 ≤ (5895248344893/12500000000000 : ℝ)^4095
        have hw : |(2740668011/5000000000 : ℝ)|=(2740668011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83453333/625000000 : ℝ)|^5119 ≤ (4035257062603/50000000000000 : ℝ)^4095
        have hw : |(-83453333/625000000 : ℝ)|=(83453333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s5_4 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135835659/10000000000 : ℝ)*x 0 + (925033819/2000000000 : ℝ)*x 1 + (3683465613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135835659/10000000000 : ℝ)^5119 ≤ (16582526011291/50000000000000 : ℝ)^4095 := by
    have hnat : (4135835659 : ℕ)^5119*50000000000000^4095 ≤ 16582526011291^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135835659 10000000000 16582526011291 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925033819/2000000000 : ℝ)^5119 ≤ (38140736482583/100000000000000 : ℝ)^4095 := by
    have hnat : (925033819 : ℕ)^5119*100000000000000^4095 ≤ 38140736482583^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925033819 2000000000 38140736482583 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3683465613/10000000000 : ℝ)^5119 ≤ (5738842295579/20000000000000 : ℝ)^4095 := by
    have hnat : (3683465613 : ℕ)^5119*20000000000000^4095 ≤ 5738842295579^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683465613 10000000000 5738842295579 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135835659/10000000000 : ℝ), (925033819/2000000000 : ℝ), (3683465613/10000000000 : ℝ)] ![(16582526011291/50000000000000 : ℝ), (38140736482583/100000000000000 : ℝ), (5738842295579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135835659/10000000000 : ℝ)|^5119 ≤ (16582526011291/50000000000000 : ℝ)^4095
        have hw : |(4135835659/10000000000 : ℝ)|=(4135835659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925033819/2000000000 : ℝ)|^5119 ≤ (38140736482583/100000000000000 : ℝ)^4095
        have hw : |(925033819/2000000000 : ℝ)|=(925033819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3683465613/10000000000 : ℝ)|^5119 ≤ (5738842295579/20000000000000 : ℝ)^4095
        have hw : |(3683465613/10000000000 : ℝ)|=(3683465613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1687_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2157/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9801/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3451/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2157/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2157/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2157/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2157/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2157/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2157/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9801/100000 : ℝ) ^ (5111/1024 : ℝ) ≤ (461517037186041/50000000000000000000 : ℝ) := by
    have hpowers : (9801/100000 : ℝ)^5111 ≤ (461517037186041/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9801 : ℕ)^5111*50000000000000000000^1024 ≤ 461517037186041^1024*100000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9801 100000 461517037186041 50000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9801/100000 : ℝ)) (X := (461517037186041/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2157/12500 : ℝ) ^ (5111/1024 : ℝ) ≤ (15538433781529703/100000000000000000000 : ℝ) := by
    have hpowers : (2157/12500 : ℝ)^5111 ≤ (15538433781529703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2157 : ℕ)^5111*100000000000000000000^1024 ≤ 15538433781529703^1024*12500^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2157 12500 15538433781529703 100000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2157/12500 : ℝ)) (X := (15538433781529703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000461517037186041/25000000000000000000 : ℝ) ≤ (10000036986105099/10000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (25000461517037186041/25000000000000000000 : ℝ)^1024 ≤ (10000036986105099/10000000000000000 : ℝ)^5111 := by
      have hnat : (25000461517037186041 : ℕ)^1024*10000000000000000^5111 ≤ 10000036986105099^5111*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000461517037186041 25000000000000000000 10000036986105099 10000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036986105099/10000000000000000 : ℝ)) (X := (25000461517037186041/25000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003292293571180357/20000000000000000000 : ℝ) ≤ (10000329787394813/10000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (20003292293571180357/20000000000000000000 : ℝ)^1024 ≤ (10000329787394813/10000000000000000 : ℝ)^5111 := by
      have hnat : (20003292293571180357 : ℕ)^1024*10000000000000000^5111 ≤ 10000329787394813^5111*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003292293571180357 20000000000000000000 10000329787394813 10000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000329787394813/10000000000000000 : ℝ)) (X := (20003292293571180357/20000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015538433781529703/50000000000000000000 : ℝ) ≤ (10000622588684527/10000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (50015538433781529703/50000000000000000000 : ℝ)^1024 ≤ (10000622588684527/10000000000000000 : ℝ)^5111 := by
      have hnat : (50015538433781529703 : ℕ)^1024*10000000000000000^5111 ≤ 10000622588684527^5111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015538433781529703 50000000000000000000 10000622588684527 10000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000622588684527/10000000000000000 : ℝ)) (X := (50015538433781529703/50000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(461517037186041/50000000000000000000 : ℝ) ≤ ((24848178746844179739/24850000000000000000 : ℝ)+2*(146400644857/372750000000000 : ℝ)*(9801/100000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (24848178746844179739/24850000000000000000 : ℝ)+2*(146400644857/372750000000000 : ℝ)*(9801/100000 : ℝ)=(10000036986105099/10000000000000000 : ℝ) by norm_num, show 1+2*(461517037186041/50000000000000000000 : ℝ)=(25000461517037186041/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15538433781529703/100000000000000000000 : ℝ)+(461517037186041/50000000000000000000 : ℝ) ≤ ((24848178746844179739/24850000000000000000 : ℝ)+(146400644857/372750000000000 : ℝ)*((2157/12500 : ℝ)+(9801/100000 : ℝ)))^(5111/1024 : ℝ) := by
    rw [show (24848178746844179739/24850000000000000000 : ℝ)+(146400644857/372750000000000 : ℝ)*((2157/12500 : ℝ)+(9801/100000 : ℝ))=(10000329787394813/10000000000000000 : ℝ) by norm_num, show 1+(15538433781529703/100000000000000000000 : ℝ)+(461517037186041/50000000000000000000 : ℝ)=(20003292293571180357/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15538433781529703/100000000000000000000 : ℝ) ≤ ((24848178746844179739/24850000000000000000 : ℝ)+2*(146400644857/372750000000000 : ℝ)*(2157/12500 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (24848178746844179739/24850000000000000000 : ℝ)+2*(146400644857/372750000000000 : ℝ)*(2157/12500 : ℝ)=(10000622588684527/10000000000000000 : ℝ) by norm_num, show 1+2*(15538433781529703/100000000000000000000 : ℝ)=(50015538433781529703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24848178746844179739/24850000000000000000 : ℝ)*(X 1 0+X 2 0)+(146400644857/372750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (2157/12500 : ℝ)) (c := (24848178746844179739/24850000000000000000 : ℝ)) (alpha := (146400644857/372750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24848178746844179739/24850000000000000000 : ℝ)*(X 0 1+X 2 1)+(146400644857/372750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (2157/12500 : ℝ)) (c := (24848178746844179739/24850000000000000000 : ℝ)) (alpha := (146400644857/372750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24848178746844179739/24850000000000000000 : ℝ)*(X 0 2+X 1 2)+(146400644857/372750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (2157/12500 : ℝ)) (c := (24848178746844179739/24850000000000000000 : ℝ)) (alpha := (146400644857/372750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1070240599/2000000000 : ℝ)*X 1 0+(-840894977/5000000000 : ℝ)*X 1 1+(5134799159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s5_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1499895017/10000000000 : ℝ)*X 0 0+(1284649933/2500000000 : ℝ)*X 0 1+(5481336049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2628777971/5000000000 : ℝ)*X 1 0+(-166906663/1250000000 : ℝ)*X 1 1+(1096267211/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2628777979/5000000000 : ℝ)*X 2 0+(2740668011/5000000000 : ℝ)*X 2 1+(-83453333/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4135835659/10000000000 : ℝ)*X 0 0+(925033819/2000000000 : ℝ)*X 0 1+(3683465613/10000000000 : ℝ)*X 0 2+(4135835659/10000000000 : ℝ)*X 1 0+(925033819/2000000000 : ℝ)*X 1 1+(3683465613/10000000000 : ℝ)*X 1 2+(4135835659/10000000000 : ℝ)*X 2 0+(925033819/2000000000 : ℝ)*X 2 1+(3683465613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3039490546856792146195821251/1242500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73800803/20000000000000 : ℝ)*(base19) + (385074233/100000000000000 : ℝ)*(base23) + (111383429/100000000000000 : ℝ)*(lower1) + (54036639/100000000000000 : ℝ)*(upper3) + (922123/20000000000000 : ℝ)*(lower4) + (10436731/20000000000000 : ℝ)*(upper5) + (1989797924690803/100000000000000 : ℝ)*(major0) + (1989797924690803/100000000000000 : ℝ)*(major1) + (1989797924690803/100000000000000 : ℝ)*(major2) + (88621491/100000000000000 : ℝ)*(sp0) + (1458845781716737/50000000000000 : ℝ)*(sp1) + (91177847056499/3125000000000 : ℝ)*(sp2) + (72942279458981/2500000000000 : ℝ)*(sp3) + (1061904204405791/100000000000000 : ℝ)*(sp4) + (1061904204405791/100000000000000 : ℝ)*(f.failure) + (1458845781716737/50000000000000 : ℝ)*(f.sum) + (144110309385317/37275000000000000000000000000 : ℝ)*base65 + (37979672017184078749/7455000000000000000000000000000000 : ℝ)*base68 + (42299926492364078749/7455000000000000000000000000000000 : ℝ)*base70 + (48466281739619078749/7455000000000000000000000000000000 : ℝ)*base72 + (33101659916117/37275000000000000000000000000 : ℝ)*base73 + (23965271748870921251/7455000000000000000000000000000000 : ℝ)*base75 + (11200254191235921251/7455000000000000000000000000000000 : ℝ)*base77 + (27336275213144078749/7455000000000000000000000000000000 : ℝ)*base80 + (174052871374517/37275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6155987/2500000000000000000000 : ℝ)*base90 + (6155987/2500000000000000000000 : ℝ)*base92 + (6155987/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1687_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2157/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1687_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1687_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8641/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1687_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1687_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1687_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8641/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
