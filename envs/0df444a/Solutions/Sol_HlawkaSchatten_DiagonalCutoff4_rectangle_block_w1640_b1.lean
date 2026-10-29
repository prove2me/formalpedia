-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1640_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:13.335121+00:00
-- url     : https://prove2.me/submissions/16b7ee7c-96ed-4c83-a41d-70e9dd154dcb

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
theorem support_rectangle_w1640_s3_0 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-815770169/5000000000 : ℝ)*x 0 + (5450617589/10000000000 : ℝ)*x 1 + (1036624441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (815770169/5000000000 : ℝ)^4879 ≤ (10079544789187/100000000000000 : ℝ)^3855 := by
    have hnat : (815770169 : ℕ)^4879*100000000000000^3855 ≤ 10079544789187^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815770169 5000000000 10079544789187 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450617589/10000000000 : ℝ)^4879 ≤ (5798932462139/12500000000000 : ℝ)^3855 := by
    have hnat : (5450617589 : ℕ)^4879*12500000000000^3855 ≤ 5798932462139^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450617589 10000000000 5798932462139 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036624441/2000000000 : ℝ)^4879 ≤ (43528995499291/100000000000000 : ℝ)^3855 := by
    have hnat : (1036624441 : ℕ)^4879*100000000000000^3855 ≤ 43528995499291^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036624441 2000000000 43528995499291 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-815770169/5000000000 : ℝ), (5450617589/10000000000 : ℝ), (1036624441/2000000000 : ℝ)] ![(10079544789187/100000000000000 : ℝ), (5798932462139/12500000000000 : ℝ), (43528995499291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-815770169/5000000000 : ℝ)|^4879 ≤ (10079544789187/100000000000000 : ℝ)^3855
        have hw : |(-815770169/5000000000 : ℝ)|=(815770169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450617589/10000000000 : ℝ)|^4879 ≤ (5798932462139/12500000000000 : ℝ)^3855
        have hw : |(5450617589/10000000000 : ℝ)|=(5450617589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036624441/2000000000 : ℝ)|^4879 ≤ (43528995499291/100000000000000 : ℝ)^3855
        have hw : |(1036624441/2000000000 : ℝ)|=(1036624441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s3_1 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337317763/2500000000 : ℝ)*x 0 + (-884651607/5000000000 : ℝ)*x 1 + (5183122199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337317763/2500000000 : ℝ)^4879 ≤ (2831403567399/6250000000000 : ℝ)^3855 := by
    have hnat : (1337317763 : ℕ)^4879*6250000000000^3855 ≤ 2831403567399^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337317763 2500000000 2831403567399 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884651607/5000000000 : ℝ)^4879 ≤ (11168547475319/100000000000000 : ℝ)^3855 := by
    have hnat : (884651607 : ℕ)^4879*100000000000000^3855 ≤ 11168547475319^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884651607 5000000000 11168547475319 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183122199/10000000000 : ℝ)^4879 ≤ (43528995435517/100000000000000 : ℝ)^3855 := by
    have hnat : (5183122199 : ℕ)^4879*100000000000000^3855 ≤ 43528995435517^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183122199 10000000000 43528995435517 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337317763/2500000000 : ℝ), (-884651607/5000000000 : ℝ), (5183122199/10000000000 : ℝ)] ![(2831403567399/6250000000000 : ℝ), (11168547475319/100000000000000 : ℝ), (43528995435517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337317763/2500000000 : ℝ)|^4879 ≤ (2831403567399/6250000000000 : ℝ)^3855
        have hw : |(1337317763/2500000000 : ℝ)|=(1337317763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884651607/5000000000 : ℝ)|^4879 ≤ (11168547475319/100000000000000 : ℝ)^3855
        have hw : |(-884651607/5000000000 : ℝ)|=(884651607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183122199/10000000000 : ℝ)|^4879 ≤ (43528995435517/100000000000000 : ℝ)^3855
        have hw : |(5183122199/10000000000 : ℝ)|=(5183122199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s3_2 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53492711/100000000 : ℝ)*x 0 + (5183122173/10000000000 : ℝ)*x 1 + (-110581449/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53492711/100000000 : ℝ)^4879 ≤ (5662807199109/12500000000000 : ℝ)^3855 := by
    have hnat : (53492711 : ℕ)^4879*12500000000000^3855 ≤ 5662807199109^3855*100000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53492711 100000000 5662807199109 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183122173/10000000000 : ℝ)^4879 ≤ (21764497579581/50000000000000 : ℝ)^3855 := by
    have hnat : (5183122173 : ℕ)^4879*50000000000000^3855 ≤ 21764497579581^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183122173 10000000000 21764497579581 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110581449/625000000 : ℝ)^4879 ≤ (2233709447129/20000000000000 : ℝ)^3855 := by
    have hnat : (110581449 : ℕ)^4879*20000000000000^3855 ≤ 2233709447129^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110581449 625000000 2233709447129 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53492711/100000000 : ℝ), (5183122173/10000000000 : ℝ), (-110581449/625000000 : ℝ)] ![(5662807199109/12500000000000 : ℝ), (21764497579581/50000000000000 : ℝ), (2233709447129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53492711/100000000 : ℝ)|^4879 ≤ (5662807199109/12500000000000 : ℝ)^3855
        have hw : |(53492711/100000000 : ℝ)|=(53492711/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183122173/10000000000 : ℝ)|^4879 ≤ (21764497579581/50000000000000 : ℝ)^3855
        have hw : |(5183122173/10000000000 : ℝ)|=(5183122173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110581449/625000000 : ℝ)|^4879 ≤ (2233709447129/20000000000000 : ℝ)^3855
        have hw : |(-110581449/625000000 : ℝ)|=(110581449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s3_3 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4188446411/10000000000 : ℝ)*x 0 + (771404077/2000000000 : ℝ)*x 1 + (4540387093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188446411/10000000000 : ℝ)^4879 ≤ (2077491555031/6250000000000 : ℝ)^3855 := by
    have hnat : (4188446411 : ℕ)^4879*6250000000000^3855 ≤ 2077491555031^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188446411 10000000000 2077491555031 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771404077/2000000000 : ℝ)^4879 ≤ (598933248771/2000000000000 : ℝ)^3855 := by
    have hnat : (771404077 : ℕ)^4879*2000000000000^3855 ≤ 598933248771^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771404077 2000000000 598933248771 2000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540387093/10000000000 : ℝ)^4879 ≤ (36813472661923/100000000000000 : ℝ)^3855 := by
    have hnat : (4540387093 : ℕ)^4879*100000000000000^3855 ≤ 36813472661923^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540387093 10000000000 36813472661923 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188446411/10000000000 : ℝ), (771404077/2000000000 : ℝ), (4540387093/10000000000 : ℝ)] ![(2077491555031/6250000000000 : ℝ), (598933248771/2000000000000 : ℝ), (36813472661923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188446411/10000000000 : ℝ)|^4879 ≤ (2077491555031/6250000000000 : ℝ)^3855
        have hw : |(4188446411/10000000000 : ℝ)|=(4188446411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771404077/2000000000 : ℝ)|^4879 ≤ (598933248771/2000000000000 : ℝ)^3855
        have hw : |(771404077/2000000000 : ℝ)|=(771404077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540387093/10000000000 : ℝ)|^4879 ≤ (36813472661923/100000000000000 : ℝ)^3855
        have hw : |(4540387093/10000000000 : ℝ)|=(4540387093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s3_4 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1631606253/10000000000 : ℝ)*x 0 + (1296284897/2500000000 : ℝ)*x 1 + (5448578943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1631606253/10000000000 : ℝ)^4879 ≤ (10080060179351/100000000000000 : ℝ)^3855 := by
    have hnat : (1631606253 : ℕ)^4879*100000000000000^3855 ≤ 10080060179351^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631606253 10000000000 10080060179351 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296284897/2500000000 : ℝ)^4879 ≤ (21775219716033/50000000000000 : ℝ)^3855 := by
    have hnat : (1296284897 : ℕ)^4879*50000000000000^3855 ≤ 21775219716033^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296284897 2500000000 21775219716033 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448578943/10000000000 : ℝ)^4879 ≤ (46369500371259/100000000000000 : ℝ)^3855 := by
    have hnat : (5448578943 : ℕ)^4879*100000000000000^3855 ≤ 46369500371259^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448578943 10000000000 46369500371259 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1631606253/10000000000 : ℝ), (1296284897/2500000000 : ℝ), (5448578943/10000000000 : ℝ)] ![(10080060179351/100000000000000 : ℝ), (21775219716033/50000000000000 : ℝ), (46369500371259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1631606253/10000000000 : ℝ)|^4879 ≤ (10080060179351/100000000000000 : ℝ)^3855
        have hw : |(-1631606253/10000000000 : ℝ)|=(1631606253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296284897/2500000000 : ℝ)|^4879 ≤ (21775219716033/50000000000000 : ℝ)^3855
        have hw : |(1296284897/2500000000 : ℝ)|=(1296284897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448578943/10000000000 : ℝ)|^4879 ≤ (46369500371259/100000000000000 : ℝ)^3855
        have hw : |(5448578943/10000000000 : ℝ)|=(5448578943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s3_5 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638948957/5000000000 : ℝ)*x 0 + (-375961609/2500000000 : ℝ)*x 1 + (2724289479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638948957/5000000000 : ℝ)^4879 ≤ (22269402484427/50000000000000 : ℝ)^3855 := by
    have hnat : (2638948957 : ℕ)^4879*50000000000000^3855 ≤ 22269402484427^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638948957 5000000000 22269402484427 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375961609/2500000000 : ℝ)^4879 ≤ (9091694482147/100000000000000 : ℝ)^3855 := by
    have hnat : (375961609 : ℕ)^4879*100000000000000^3855 ≤ 9091694482147^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375961609 2500000000 9091694482147 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724289479/5000000000 : ℝ)^4879 ≤ (5796187566603/12500000000000 : ℝ)^3855 := by
    have hnat : (2724289479 : ℕ)^4879*12500000000000^3855 ≤ 5796187566603^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724289479 5000000000 5796187566603 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638948957/5000000000 : ℝ), (-375961609/2500000000 : ℝ), (2724289479/5000000000 : ℝ)] ![(22269402484427/50000000000000 : ℝ), (9091694482147/100000000000000 : ℝ), (5796187566603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638948957/5000000000 : ℝ)|^4879 ≤ (22269402484427/50000000000000 : ℝ)^3855
        have hw : |(2638948957/5000000000 : ℝ)|=(2638948957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375961609/2500000000 : ℝ)|^4879 ≤ (9091694482147/100000000000000 : ℝ)^3855
        have hw : |(-375961609/2500000000 : ℝ)|=(375961609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724289479/5000000000 : ℝ)|^4879 ≤ (5796187566603/12500000000000 : ℝ)^3855
        have hw : |(2724289479/5000000000 : ℝ)|=(2724289479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s3_6 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277897953/10000000000 : ℝ)*x 0 + (5448578949/10000000000 : ℝ)*x 1 + (-751923197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277897953/10000000000 : ℝ)^4879 ≤ (22269402692693/50000000000000 : ℝ)^3855 := by
    have hnat : (5277897953 : ℕ)^4879*50000000000000^3855 ≤ 22269402692693^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277897953 10000000000 22269402692693 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448578949/10000000000 : ℝ)^4879 ≤ (9273900087177/20000000000000 : ℝ)^3855 := by
    have hnat : (5448578949 : ℕ)^4879*20000000000000^3855 ≤ 9273900087177^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448578949 10000000000 9273900087177 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (751923197/5000000000 : ℝ)^4879 ≤ (9091694160783/100000000000000 : ℝ)^3855 := by
    have hnat : (751923197 : ℕ)^4879*100000000000000^3855 ≤ 9091694160783^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751923197 5000000000 9091694160783 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277897953/10000000000 : ℝ), (5448578949/10000000000 : ℝ), (-751923197/5000000000 : ℝ)] ![(22269402692693/50000000000000 : ℝ), (9273900087177/20000000000000 : ℝ), (9091694160783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277897953/10000000000 : ℝ)|^4879 ≤ (22269402692693/50000000000000 : ℝ)^3855
        have hw : |(5277897953/10000000000 : ℝ)|=(5277897953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448578949/10000000000 : ℝ)|^4879 ≤ (9273900087177/20000000000000 : ℝ)^3855
        have hw : |(5448578949/10000000000 : ℝ)|=(5448578949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-751923197/5000000000 : ℝ)|^4879 ≤ (9091694160783/100000000000000 : ℝ)^3855
        have hw : |(-751923197/5000000000 : ℝ)|=(751923197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s3_7 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167544589/400000000 : ℝ)*x 0 + (4535233353/10000000000 : ℝ)*x 1 + (3862228553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167544589/400000000 : ℝ)^4879 ≤ (33241555458761/100000000000000 : ℝ)^3855 := by
    have hnat : (167544589 : ℕ)^4879*100000000000000^3855 ≤ 33241555458761^3855*400000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167544589 400000000 33241555458761 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535233353/10000000000 : ℝ)^4879 ≤ (18380297189047/50000000000000 : ℝ)^3855 := by
    have hnat : (4535233353 : ℕ)^4879*50000000000000^3855 ≤ 18380297189047^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535233353 10000000000 18380297189047 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3862228553/10000000000 : ℝ)^4879 ≤ (29997850156411/100000000000000 : ℝ)^3855 := by
    have hnat : (3862228553 : ℕ)^4879*100000000000000^3855 ≤ 29997850156411^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3862228553 10000000000 29997850156411 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167544589/400000000 : ℝ), (4535233353/10000000000 : ℝ), (3862228553/10000000000 : ℝ)] ![(33241555458761/100000000000000 : ℝ), (18380297189047/50000000000000 : ℝ), (29997850156411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167544589/400000000 : ℝ)|^4879 ≤ (33241555458761/100000000000000 : ℝ)^3855
        have hw : |(167544589/400000000 : ℝ)|=(167544589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535233353/10000000000 : ℝ)|^4879 ≤ (18380297189047/50000000000000 : ℝ)^3855
        have hw : |(4535233353/10000000000 : ℝ)|=(4535233353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3862228553/10000000000 : ℝ)|^4879 ≤ (29997850156411/100000000000000 : ℝ)^3855
        have hw : |(3862228553/10000000000 : ℝ)|=(3862228553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1640_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10611/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16293/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16379/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5267/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16379/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5267/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16379/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5267/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16379/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5267/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16379/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5267/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16379/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5267/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5267/50000 : ℝ) ^ (4875/1024 : ℝ) ≤ (444476445893329/20000000000000000000 : ℝ) := by
    have hpowers : (5267/50000 : ℝ)^4875 ≤ (444476445893329/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5267 : ℕ)^4875*20000000000000000000^1024 ≤ 444476445893329^1024*50000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5267 50000 444476445893329 20000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5267/50000 : ℝ)) (X := (444476445893329/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16379/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (1817292342334091/10000000000000000000 : ℝ) := by
    have hpowers : (16379/100000 : ℝ)^4875 ≤ (1817292342334091/10000000000000000000 : ℝ)^1024 := by
      have hnat : (16379 : ℕ)^4875*10000000000000000000^1024 ≤ 1817292342334091^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16379 100000 1817292342334091 10000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16379/100000 : ℝ)) (X := (1817292342334091/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000444476445893329/10000000000000000000 : ℝ) ≤ (10000093361208297/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (10000444476445893329/10000000000000000000 : ℝ)^1024 ≤ (10000093361208297/10000000000000000 : ℝ)^4875 := by
      have hnat : (10000444476445893329 : ℕ)^1024*10000000000000000^4875 ≤ 10000093361208297^4875*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000444476445893329 10000000000000000000 10000093361208297 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000093361208297/10000000000000000 : ℝ)) (X := (10000444476445893329/10000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004079061130561511/20000000000000000000 : ℝ) ≤ (10000428371503447/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (20004079061130561511/20000000000000000000 : ℝ)^1024 ≤ (10000428371503447/10000000000000000 : ℝ)^4875 := by
      have hnat : (20004079061130561511 : ℕ)^1024*10000000000000000^4875 ≤ 10000428371503447^4875*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004079061130561511 20000000000000000000 10000428371503447 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000428371503447/10000000000000000 : ℝ)) (X := (20004079061130561511/20000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001817292342334091/5000000000000000000 : ℝ) ≤ (10000763381798597/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (5001817292342334091/5000000000000000000 : ℝ)^1024 ≤ (10000763381798597/10000000000000000 : ℝ)^4875 := by
      have hnat : (5001817292342334091 : ℕ)^1024*10000000000000000^4875 ≤ 10000763381798597^4875*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001817292342334091 5000000000000000000 10000763381798597 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000763381798597/10000000000000000 : ℝ)) (X := (5001817292342334091/5000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(444476445893329/20000000000000000000 : ℝ) ≤ ((11688697539872855153/11690000000000000000 : ℝ)+2*(6700205903/11690000000000 : ℝ)*(5267/50000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (11688697539872855153/11690000000000000000 : ℝ)+2*(6700205903/11690000000000 : ℝ)*(5267/50000 : ℝ)=(10000093361208297/10000000000000000 : ℝ) by norm_num, show 1+2*(444476445893329/20000000000000000000 : ℝ)=(10000444476445893329/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1817292342334091/10000000000000000000 : ℝ)+(444476445893329/20000000000000000000 : ℝ) ≤ ((11688697539872855153/11690000000000000000 : ℝ)+(6700205903/11690000000000 : ℝ)*((16379/100000 : ℝ)+(5267/50000 : ℝ)))^(4875/1024 : ℝ) := by
    rw [show (11688697539872855153/11690000000000000000 : ℝ)+(6700205903/11690000000000 : ℝ)*((16379/100000 : ℝ)+(5267/50000 : ℝ))=(10000428371503447/10000000000000000 : ℝ) by norm_num, show 1+(1817292342334091/10000000000000000000 : ℝ)+(444476445893329/20000000000000000000 : ℝ)=(20004079061130561511/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1817292342334091/10000000000000000000 : ℝ) ≤ ((11688697539872855153/11690000000000000000 : ℝ)+2*(6700205903/11690000000000 : ℝ)*(16379/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (11688697539872855153/11690000000000000000 : ℝ)+2*(6700205903/11690000000000 : ℝ)*(16379/100000 : ℝ)=(10000763381798597/10000000000000000 : ℝ) by norm_num, show 1+2*(1817292342334091/10000000000000000000 : ℝ)=(5001817292342334091/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11688697539872855153/11690000000000000000 : ℝ)*(X 1 0+X 2 0)+(6700205903/11690000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (16379/100000 : ℝ)) (c := (11688697539872855153/11690000000000000000 : ℝ)) (alpha := (6700205903/11690000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11688697539872855153/11690000000000000000 : ℝ)*(X 0 1+X 2 1)+(6700205903/11690000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (16379/100000 : ℝ)) (c := (11688697539872855153/11690000000000000000 : ℝ)) (alpha := (6700205903/11690000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11688697539872855153/11690000000000000000 : ℝ)*(X 0 2+X 1 2)+(6700205903/11690000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (16379/100000 : ℝ)) (c := (11688697539872855153/11690000000000000000 : ℝ)) (alpha := (6700205903/11690000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-815770169/5000000000 : ℝ)*X 0 0+(5450617589/10000000000 : ℝ)*X 0 1+(1036624441/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337317763/2500000000 : ℝ)*X 1 0+(-884651607/5000000000 : ℝ)*X 1 1+(5183122199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53492711/100000000 : ℝ)*X 2 0+(5183122173/10000000000 : ℝ)*X 2 1+(-110581449/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4188446411/10000000000 : ℝ)*X 0 0+(771404077/2000000000 : ℝ)*X 0 1+(4540387093/10000000000 : ℝ)*X 0 2+(4188446411/10000000000 : ℝ)*X 1 0+(771404077/2000000000 : ℝ)*X 1 1+(4540387093/10000000000 : ℝ)*X 1 2+(4188446411/10000000000 : ℝ)*X 2 0+(771404077/2000000000 : ℝ)*X 2 1+(4540387093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1631606253/10000000000 : ℝ)*X 0 0+(1296284897/2500000000 : ℝ)*X 0 1+(5448578943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638948957/5000000000 : ℝ)*X 1 0+(-375961609/2500000000 : ℝ)*X 1 1+(2724289479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277897953/10000000000 : ℝ)*X 2 0+(5448578949/10000000000 : ℝ)*X 2 1+(-751923197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((167544589/400000000 : ℝ)*X 0 0+(4535233353/10000000000 : ℝ)*X 0 1+(3862228553/10000000000 : ℝ)*X 0 2+(167544589/400000000 : ℝ)*X 1 0+(4535233353/10000000000 : ℝ)*X 1 1+(3862228553/10000000000 : ℝ)*X 1 2+(167544589/400000000 : ℝ)*X 2 0+(4535233353/10000000000 : ℝ)*X 2 1+(3862228553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1001242994330095242430976013/116900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (272360917/20000000000000 : ℝ)*(base19) + (40572409/3125000000000 : ℝ)*(base23) + (12976393/25000000000000 : ℝ)*(lower2) + (6440663/3125000000000 : ℝ)*(upper3) + (41105997/25000000000000 : ℝ)*(upper5) + (520177274514207/20000000000000 : ℝ)*(major0) + (520177274514207/20000000000000 : ℝ)*(major1) + (520177274514207/20000000000000 : ℝ)*(major2) + (3738398924850059/100000000000000 : ℝ)*(sp0) + (1869207212658543/50000000000000 : ℝ)*(sp1) + (3738414488804583/100000000000000 : ℝ)*(sp2) + (1463349559037791/100000000000000 : ℝ)*(sp3) + (16862271613/100000000000000 : ℝ)*(sp4) + (1778371043/25000000000000 : ℝ)*(sp7) + (1463356672521963/100000000000000 : ℝ)*(f.failure) + (467301973390209/12500000000000 : ℝ)*(f.sum) + (110218231673/29225000000000000000000000 : ℝ)*base66 + (105010781143163047/33400000000000000000000000000000 : ℝ)*base68 + (121327963268963047/33400000000000000000000000000000 : ℝ)*base70 + (71642359035036953/33400000000000000000000000000000 : ℝ)*base71 + (2923946217933/1169000000000000000000000000 : ℝ)*base74 + (28599107732963047/33400000000000000000000000000000 : ℝ)*base76 + (106334779020163047/33400000000000000000000000000000 : ℝ)*base78 + (246914475679236953/33400000000000000000000000000000 : ℝ)*base79 + (1078173725427/1169000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (615273/400000000000000000000 : ℝ)*base89 + (615273/400000000000000000000 : ℝ)*base91 + (615273/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2487365851623247574670742071/584500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (613158831/100000000000000 : ℝ)*(base19) + (172783171/25000000000000 : ℝ)*(base23) + (1877383/2000000000000 : ℝ)*(upper3) + (16939267/100000000000000 : ℝ)*(lower4) + (19867069/25000000000000 : ℝ)*(upper5) + (2640906685449331/100000000000000 : ℝ)*(major0) + (2640906685449331/100000000000000 : ℝ)*(major1) + (2640906685449331/100000000000000 : ℝ)*(major2) + (1797836693/25000000000000 : ℝ)*(sp1) + (8509821337/100000000000000 : ℝ)*(sp2) + (474492452570821/12500000000000 : ℝ)*(sp4) + (1897965908030483/50000000000000 : ℝ)*(sp5) + (1897965209806273/50000000000000 : ℝ)*(sp6) + (1485873608480599/100000000000000 : ℝ)*(sp7) + (1485873608480599/100000000000000 : ℝ)*(f.failure) + (474492452570821/12500000000000 : ℝ)*(f.sum) + (4017460695713/1169000000000000000000000000 : ℝ)*base66 + (816279946180321051/167000000000000000000000000000000 : ℝ)*base68 + (359899644339678949/167000000000000000000000000000000 : ℝ)*base69 + (1178732890484321051/167000000000000000000000000000000 : ℝ)*base72 + (453256484139/1169000000000000000000000000 : ℝ)*base73 + (640732283195678949/167000000000000000000000000000000 : ℝ)*base75 + (1282427944525678949/167000000000000000000000000000000 : ℝ)*base77 + (1819146140162678949/167000000000000000000000000000000 : ℝ)*base79 + (3202874075649/1169000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (593229/400000000000000000000 : ℝ)*base89 + (593229/400000000000000000000 : ℝ)*base91 + (593229/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1640_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16293/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1640_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1640_s4_0 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40789949/250000000 : ℝ)*x 0 + (2725163847/5000000000 : ℝ)*x 1 + (5183373609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40789949/250000000 : ℝ)^4879 ≤ (5039997667991/50000000000000 : ℝ)^3855 := by
    have hnat : (40789949 : ℕ)^4879*50000000000000^3855 ≤ 5039997667991^3855*250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40789949 250000000 5039997667991 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725163847/5000000000 : ℝ)^4879 ≤ (1449635529777/3125000000000 : ℝ)^3855 := by
    have hnat : (2725163847 : ℕ)^4879*3125000000000^3855 ≤ 1449635529777^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725163847 5000000000 1449635529777 3125000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183373609/10000000000 : ℝ)^4879 ≤ (43531667697161/100000000000000 : ℝ)^3855 := by
    have hnat : (5183373609 : ℕ)^4879*100000000000000^3855 ≤ 43531667697161^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183373609 10000000000 43531667697161 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40789949/250000000 : ℝ), (2725163847/5000000000 : ℝ), (5183373609/10000000000 : ℝ)] ![(5039997667991/50000000000000 : ℝ), (1449635529777/3125000000000 : ℝ), (43531667697161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40789949/250000000 : ℝ)|^4879 ≤ (5039997667991/50000000000000 : ℝ)^3855
        have hw : |(-40789949/250000000 : ℝ)|=(40789949/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725163847/5000000000 : ℝ)|^4879 ≤ (1449635529777/3125000000000 : ℝ)^3855
        have hw : |(2725163847/5000000000 : ℝ)|=(2725163847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183373609/10000000000 : ℝ)|^4879 ≤ (43531667697161/100000000000000 : ℝ)^3855
        have hw : |(5183373609/10000000000 : ℝ)|=(5183373609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s4_1 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167162271/312500000 : ℝ)*x 0 + (-353814777/2000000000 : ℝ)*x 1 + (1036674721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167162271/312500000 : ℝ)^4879 ≤ (5662702120601/12500000000000 : ℝ)^3855 := by
    have hnat : (167162271 : ℕ)^4879*12500000000000^3855 ≤ 5662702120601^3855*312500000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167162271 312500000 5662702120601 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353814777/2000000000 : ℝ)^4879 ≤ (5583357680931/50000000000000 : ℝ)^3855 := by
    have hnat : (353814777 : ℕ)^4879*50000000000000^3855 ≤ 5583357680931^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353814777 2000000000 5583357680931 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036674721/2000000000 : ℝ)^4879 ≤ (10882916913661/25000000000000 : ℝ)^3855 := by
    have hnat : (1036674721 : ℕ)^4879*25000000000000^3855 ≤ 10882916913661^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036674721 2000000000 10882916913661 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167162271/312500000 : ℝ), (-353814777/2000000000 : ℝ), (1036674721/2000000000 : ℝ)] ![(5662702120601/12500000000000 : ℝ), (5583357680931/50000000000000 : ℝ), (10882916913661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167162271/312500000 : ℝ)|^4879 ≤ (5662702120601/12500000000000 : ℝ)^3855
        have hw : |(167162271/312500000 : ℝ)|=(167162271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-353814777/2000000000 : ℝ)|^4879 ≤ (5583357680931/50000000000000 : ℝ)^3855
        have hw : |(-353814777/2000000000 : ℝ)|=(353814777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036674721/2000000000 : ℝ)|^4879 ≤ (10882916913661/25000000000000 : ℝ)^3855
        have hw : |(1036674721/2000000000 : ℝ)|=(1036674721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s4_2 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349192661/10000000000 : ℝ)*x 0 + (1036674721/2000000000 : ℝ)*x 1 + (-1769073901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349192661/10000000000 : ℝ)^4879 ≤ (9060323369381/20000000000000 : ℝ)^3855 := by
    have hnat : (5349192661 : ℕ)^4879*20000000000000^3855 ≤ 9060323369381^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349192661 10000000000 9060323369381 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036674721/2000000000 : ℝ)^4879 ≤ (10882916913661/25000000000000 : ℝ)^3855 := by
    have hnat : (1036674721 : ℕ)^4879*25000000000000^3855 ≤ 10882916913661^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036674721 2000000000 10882916913661 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769073901/10000000000 : ℝ)^4879 ≤ (2791678872421/25000000000000 : ℝ)^3855 := by
    have hnat : (1769073901 : ℕ)^4879*25000000000000^3855 ≤ 2791678872421^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769073901 10000000000 2791678872421 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349192661/10000000000 : ℝ), (1036674721/2000000000 : ℝ), (-1769073901/10000000000 : ℝ)] ![(9060323369381/20000000000000 : ℝ), (10882916913661/25000000000000 : ℝ), (2791678872421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349192661/10000000000 : ℝ)|^4879 ≤ (9060323369381/20000000000000 : ℝ)^3855
        have hw : |(5349192661/10000000000 : ℝ)|=(5349192661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036674721/2000000000 : ℝ)|^4879 ≤ (10882916913661/25000000000000 : ℝ)^3855
        have hw : |(1036674721/2000000000 : ℝ)|=(1036674721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769073901/10000000000 : ℝ)|^4879 ≤ (2791678872421/25000000000000 : ℝ)^3855
        have hw : |(-1769073901/10000000000 : ℝ)|=(1769073901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s4_3 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (837696783/2000000000 : ℝ)*x 0 + (1928854037/5000000000 : ℝ)*x 1 + (2269845913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837696783/2000000000 : ℝ)^4879 ≤ (1662012078817/5000000000000 : ℝ)^3855 := by
    have hnat : (837696783 : ℕ)^4879*5000000000000^3855 ≤ 1662012078817^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837696783 2000000000 1662012078817 5000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928854037/5000000000 : ℝ)^4879 ≤ (29953420237857/100000000000000 : ℝ)^3855 := by
    have hnat : (1928854037 : ℕ)^4879*100000000000000^3855 ≤ 29953420237857^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928854037 5000000000 29953420237857 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269845913/5000000000 : ℝ)^4879 ≤ (7361267633753/20000000000000 : ℝ)^3855 := by
    have hnat : (2269845913 : ℕ)^4879*20000000000000^3855 ≤ 7361267633753^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269845913 5000000000 7361267633753 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837696783/2000000000 : ℝ), (1928854037/5000000000 : ℝ), (2269845913/5000000000 : ℝ)] ![(1662012078817/5000000000000 : ℝ), (29953420237857/100000000000000 : ℝ), (7361267633753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837696783/2000000000 : ℝ)|^4879 ≤ (1662012078817/5000000000000 : ℝ)^3855
        have hw : |(837696783/2000000000 : ℝ)|=(837696783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1928854037/5000000000 : ℝ)|^4879 ≤ (29953420237857/100000000000000 : ℝ)^3855
        have hw : |(1928854037/5000000000 : ℝ)|=(1928854037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269845913/5000000000 : ℝ)|^4879 ≤ (7361267633753/20000000000000 : ℝ)^3855
        have hw : |(2269845913/5000000000 : ℝ)|=(2269845913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s4_4 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1631663467/10000000000 : ℝ)*x 0 + (2592691439/5000000000 : ℝ)*x 1 + (5448297297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1631663467/10000000000 : ℝ)^4879 ≤ (10080507540777/100000000000000 : ℝ)^3855 := by
    have hnat : (1631663467 : ℕ)^4879*100000000000000^3855 ≤ 10080507540777^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631663467 10000000000 10080507540777 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592691439/5000000000 : ℝ)^4879 ≤ (21776512826103/50000000000000 : ℝ)^3855 := by
    have hnat : (2592691439 : ℕ)^4879*50000000000000^3855 ≤ 21776512826103^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592691439 5000000000 21776512826103 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448297297/10000000000 : ℝ)^4879 ≤ (11591616696491/25000000000000 : ℝ)^3855 := by
    have hnat : (5448297297 : ℕ)^4879*25000000000000^3855 ≤ 11591616696491^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448297297 10000000000 11591616696491 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1631663467/10000000000 : ℝ), (2592691439/5000000000 : ℝ), (5448297297/10000000000 : ℝ)] ![(10080507540777/100000000000000 : ℝ), (21776512826103/50000000000000 : ℝ), (11591616696491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1631663467/10000000000 : ℝ)|^4879 ≤ (10080507540777/100000000000000 : ℝ)^3855
        have hw : |(-1631663467/10000000000 : ℝ)|=(1631663467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592691439/5000000000 : ℝ)|^4879 ≤ (21776512826103/50000000000000 : ℝ)^3855
        have hw : |(2592691439/5000000000 : ℝ)|=(2592691439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448297297/10000000000 : ℝ)|^4879 ≤ (11591616696491/25000000000000 : ℝ)^3855
        have hw : |(5448297297/10000000000 : ℝ)|=(5448297297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s4_5 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638982161/5000000000 : ℝ)*x 0 + (-23502347/156250000 : ℝ)*x 1 + (5448297307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638982161/5000000000 : ℝ)^4879 ≤ (44539514228313/100000000000000 : ℝ)^3855 := by
    have hnat : (2638982161 : ℕ)^4879*100000000000000^3855 ≤ 44539514228313^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638982161 5000000000 44539514228313 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23502347/156250000 : ℝ)^4879 ≤ (9094018862357/100000000000000 : ℝ)^3855 := by
    have hnat : (23502347 : ℕ)^4879*100000000000000^3855 ≤ 9094018862357^3855*156250000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23502347 156250000 9094018862357 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448297307/10000000000 : ℝ)^4879 ≤ (5795808361709/12500000000000 : ℝ)^3855 := by
    have hnat : (5448297307 : ℕ)^4879*12500000000000^3855 ≤ 5795808361709^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448297307 10000000000 5795808361709 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638982161/5000000000 : ℝ), (-23502347/156250000 : ℝ), (5448297307/10000000000 : ℝ)] ![(44539514228313/100000000000000 : ℝ), (9094018862357/100000000000000 : ℝ), (5795808361709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638982161/5000000000 : ℝ)|^4879 ≤ (44539514228313/100000000000000 : ℝ)^3855
        have hw : |(2638982161/5000000000 : ℝ)|=(2638982161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23502347/156250000 : ℝ)|^4879 ≤ (9094018862357/100000000000000 : ℝ)^3855
        have hw : |(-23502347/156250000 : ℝ)|=(23502347/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448297307/10000000000 : ℝ)|^4879 ≤ (5795808361709/12500000000000 : ℝ)^3855
        have hw : |(5448297307/10000000000 : ℝ)|=(5448297307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s4_6 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638982159/5000000000 : ℝ)*x 0 + (54482973/100000000 : ℝ)*x 1 + (-94009389/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638982159/5000000000 : ℝ)^4879 ≤ (5567439273199/12500000000000 : ℝ)^3855 := by
    have hnat : (2638982159 : ℕ)^4879*12500000000000^3855 ≤ 5567439273199^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638982159 5000000000 5567439273199 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54482973/100000000 : ℝ)^4879 ≤ (11591616704569/25000000000000 : ℝ)^3855 := by
    have hnat : (54482973 : ℕ)^4879*25000000000000^3855 ≤ 11591616704569^3855*100000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54482973 100000000 11591616704569 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94009389/625000000 : ℝ)^4879 ≤ (2273504746197/25000000000000 : ℝ)^3855 := by
    have hnat : (94009389 : ℕ)^4879*25000000000000^3855 ≤ 2273504746197^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94009389 625000000 2273504746197 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638982159/5000000000 : ℝ), (54482973/100000000 : ℝ), (-94009389/625000000 : ℝ)] ![(5567439273199/12500000000000 : ℝ), (11591616704569/25000000000000 : ℝ), (2273504746197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638982159/5000000000 : ℝ)|^4879 ≤ (5567439273199/12500000000000 : ℝ)^3855
        have hw : |(2638982159/5000000000 : ℝ)|=(2638982159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54482973/100000000 : ℝ)|^4879 ≤ (11591616704569/25000000000000 : ℝ)^3855
        have hw : |(54482973/100000000 : ℝ)|=(54482973/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94009389/625000000 : ℝ)|^4879 ≤ (2273504746197/25000000000000 : ℝ)^3855
        have hw : |(-94009389/625000000 : ℝ)|=(94009389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s4_7 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4188651343/10000000000 : ℝ)*x 0 + (1133639689/2500000000 : ℝ)*x 1 + (3862895111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188651343/10000000000 : ℝ)^4879 ≤ (33241923259403/100000000000000 : ℝ)^3855 := by
    have hnat : (4188651343 : ℕ)^4879*100000000000000^3855 ≤ 33241923259403^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188651343 10000000000 33241923259403 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133639689/2500000000 : ℝ)^4879 ≤ (36753674074489/100000000000000 : ℝ)^3855 := by
    have hnat : (1133639689 : ℕ)^4879*100000000000000^3855 ≤ 36753674074489^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133639689 2500000000 36753674074489 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3862895111/10000000000 : ℝ)^4879 ≤ (7501100662091/25000000000000 : ℝ)^3855 := by
    have hnat : (3862895111 : ℕ)^4879*25000000000000^3855 ≤ 7501100662091^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3862895111 10000000000 7501100662091 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188651343/10000000000 : ℝ), (1133639689/2500000000 : ℝ), (3862895111/10000000000 : ℝ)] ![(33241923259403/100000000000000 : ℝ), (36753674074489/100000000000000 : ℝ), (7501100662091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188651343/10000000000 : ℝ)|^4879 ≤ (33241923259403/100000000000000 : ℝ)^3855
        have hw : |(4188651343/10000000000 : ℝ)|=(4188651343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133639689/2500000000 : ℝ)|^4879 ≤ (36753674074489/100000000000000 : ℝ)^3855
        have hw : |(1133639689/2500000000 : ℝ)|=(1133639689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3862895111/10000000000 : ℝ)|^4879 ≤ (7501100662091/25000000000000 : ℝ)^3855
        have hw : |(3862895111/10000000000 : ℝ)|=(3862895111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1640_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10617/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16287/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10611/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10611/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10611/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10611/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10611/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10611/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10611/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (287598753033067/12500000000000000000 : ℝ) := by
    have hpowers : (10611/100000 : ℝ)^4875 ≤ (287598753033067/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10611 : ℕ)^4875*12500000000000000000^1024 ≤ 287598753033067^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10611 100000 287598753033067 12500000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10611/100000 : ℝ)) (X := (287598753033067/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16293/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (17723120521271711/100000000000000000000 : ℝ) := by
    have hpowers : (16293/100000 : ℝ)^4875 ≤ (17723120521271711/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16293 : ℕ)^4875*100000000000000000000^1024 ≤ 17723120521271711^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16293 100000 17723120521271711 100000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16293/100000 : ℝ)) (X := (17723120521271711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250287598753033067/6250000000000000000 : ℝ) ≤ (10000096655022171/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (6250287598753033067/6250000000000000000 : ℝ)^1024 ≤ (10000096655022171/10000000000000000 : ℝ)^4875 := by
      have hnat : (6250287598753033067 : ℕ)^1024*10000000000000000^4875 ≤ 10000096655022171^4875*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250287598753033067 6250000000000000000 10000096655022171 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000096655022171/10000000000000000 : ℝ)) (X := (6250287598753033067/6250000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020023910545536247/100000000000000000000 : ℝ) ≤ (5000210285773403/5000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (100020023910545536247/100000000000000000000 : ℝ)^1024 ≤ (5000210285773403/5000000000000000 : ℝ)^4875 := by
      have hnat : (100020023910545536247 : ℕ)^1024*5000000000000000^4875 ≤ 5000210285773403^4875*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020023910545536247 100000000000000000000 5000210285773403 5000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000210285773403/5000000000000000 : ℝ)) (X := (100020023910545536247/100000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017723120521271711/50000000000000000000 : ℝ) ≤ (10000744488071441/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (50017723120521271711/50000000000000000000 : ℝ)^1024 ≤ (10000744488071441/10000000000000000 : ℝ)^4875 := by
      have hnat : (50017723120521271711 : ℕ)^1024*10000000000000000^4875 ≤ 10000744488071441^4875*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017723120521271711 50000000000000000000 10000744488071441 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000744488071441/10000000000000000 : ℝ)) (X := (50017723120521271711/50000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(287598753033067/12500000000000000000 : ℝ) ≤ ((4734472919779180971/4735000000000000000 : ℝ)+2*(64783304927/113640000000000 : ℝ)*(10611/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (4734472919779180971/4735000000000000000 : ℝ)+2*(64783304927/113640000000000 : ℝ)*(10611/100000 : ℝ)=(10000096655022171/10000000000000000 : ℝ) by norm_num, show 1+2*(287598753033067/12500000000000000000 : ℝ)=(6250287598753033067/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17723120521271711/100000000000000000000 : ℝ)+(287598753033067/12500000000000000000 : ℝ) ≤ ((4734472919779180971/4735000000000000000 : ℝ)+(64783304927/113640000000000 : ℝ)*((16293/100000 : ℝ)+(10611/100000 : ℝ)))^(4875/1024 : ℝ) := by
    rw [show (4734472919779180971/4735000000000000000 : ℝ)+(64783304927/113640000000000 : ℝ)*((16293/100000 : ℝ)+(10611/100000 : ℝ))=(5000210285773403/5000000000000000 : ℝ) by norm_num, show 1+(17723120521271711/100000000000000000000 : ℝ)+(287598753033067/12500000000000000000 : ℝ)=(100020023910545536247/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17723120521271711/100000000000000000000 : ℝ) ≤ ((4734472919779180971/4735000000000000000 : ℝ)+2*(64783304927/113640000000000 : ℝ)*(16293/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (4734472919779180971/4735000000000000000 : ℝ)+2*(64783304927/113640000000000 : ℝ)*(16293/100000 : ℝ)=(10000744488071441/10000000000000000 : ℝ) by norm_num, show 1+2*(17723120521271711/100000000000000000000 : ℝ)=(50017723120521271711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4734472919779180971/4735000000000000000 : ℝ)*(X 1 0+X 2 0)+(64783304927/113640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (16293/100000 : ℝ)) (c := (4734472919779180971/4735000000000000000 : ℝ)) (alpha := (64783304927/113640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4734472919779180971/4735000000000000000 : ℝ)*(X 0 1+X 2 1)+(64783304927/113640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (16293/100000 : ℝ)) (c := (4734472919779180971/4735000000000000000 : ℝ)) (alpha := (64783304927/113640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4734472919779180971/4735000000000000000 : ℝ)*(X 0 2+X 1 2)+(64783304927/113640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (16293/100000 : ℝ)) (c := (4734472919779180971/4735000000000000000 : ℝ)) (alpha := (64783304927/113640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-40789949/250000000 : ℝ)*X 0 0+(2725163847/5000000000 : ℝ)*X 0 1+(5183373609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167162271/312500000 : ℝ)*X 1 0+(-353814777/2000000000 : ℝ)*X 1 1+(1036674721/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349192661/10000000000 : ℝ)*X 2 0+(1036674721/2000000000 : ℝ)*X 2 1+(-1769073901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((837696783/2000000000 : ℝ)*X 0 0+(1928854037/5000000000 : ℝ)*X 0 1+(2269845913/5000000000 : ℝ)*X 0 2+(837696783/2000000000 : ℝ)*X 1 0+(1928854037/5000000000 : ℝ)*X 1 1+(2269845913/5000000000 : ℝ)*X 1 2+(837696783/2000000000 : ℝ)*X 2 0+(1928854037/5000000000 : ℝ)*X 2 1+(2269845913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1631663467/10000000000 : ℝ)*X 0 0+(2592691439/5000000000 : ℝ)*X 0 1+(5448297297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638982161/5000000000 : ℝ)*X 1 0+(-23502347/156250000 : ℝ)*X 1 1+(5448297307/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638982159/5000000000 : ℝ)*X 2 0+(54482973/100000000 : ℝ)*X 2 1+(-94009389/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4188651343/10000000000 : ℝ)*X 0 0+(1133639689/2500000000 : ℝ)*X 0 1+(3862895111/10000000000 : ℝ)*X 0 2+(4188651343/10000000000 : ℝ)*X 1 0+(1133639689/2500000000 : ℝ)*X 1 1+(3862895111/10000000000 : ℝ)*X 1 2+(4188651343/10000000000 : ℝ)*X 2 0+(1133639689/2500000000 : ℝ)*X 2 1+(3862895111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (522184450044729195117353193/236750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18903093/5000000000000 : ℝ)*(base19) + (364568491/100000000000000 : ℝ)*(base23) + (28305327/50000000000000 : ℝ)*(upper3) + (3097293/100000000000000 : ℝ)*(upper4) + (3943737/10000000000000 : ℝ)*(upper5) + (1303071689041781/50000000000000 : ℝ)*(major0) + (1303071689041781/50000000000000 : ℝ)*(major1) + (2606143378083563/100000000000000 : ℝ)*(major2) + (1872983770278103/50000000000000 : ℝ)*(sp0) + (3745971842680973/100000000000000 : ℝ)*(sp1) + (1872985928087171/50000000000000 : ℝ)*(sp2) + (1466312447887417/100000000000000 : ℝ)*(sp3) + (2340093313/50000000000000 : ℝ)*(sp4) + (62937989/3125000000000 : ℝ)*(sp7) + (183289307737883/12500000000000 : ℝ)*(f.failure) + (3745972220742833/100000000000000 : ℝ)*(f.sum) + (8497034314371/3788000000000000000000000000 : ℝ)*base66 + (4902400281445739447/710250000000000000000000000000000 : ℝ)*base68 + (16812238208766189019/1420500000000000000000000000000000 : ℝ)*base69 + (3927628562049989447/710250000000000000000000000000000 : ℝ)*base72 + (28005794650483/3788000000000000000000000000 : ℝ)*base74 + (4551902298241689019/1420500000000000000000000000000000 : ℝ)*base75 + (11146023573419426947/710250000000000000000000000000000 : ℝ)*base78 + (2470777774863176947/710250000000000000000000000000000 : ℝ)*base80 + (13858873974761/2841000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1593/50000000000000000000 : ℝ)*base89 + (1593/50000000000000000000 : ℝ)*base91 + (498407/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1156467423833882763319031317/236750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (734078419/100000000000000 : ℝ)*(base19) + (9733547/1250000000000 : ℝ)*(base23) + (233952721/100000000000000 : ℝ)*(lower1) + (5199073/5000000000000 : ℝ)*(upper3) + (572123/2500000000000 : ℝ)*(lower4) + (51767773/50000000000000 : ℝ)*(upper5) + (2646173393562709/100000000000000 : ℝ)*(major0) + (2646173393562709/100000000000000 : ℝ)*(major1) + (2646173393562709/100000000000000 : ℝ)*(major2) + (305922259/100000000000000 : ℝ)*(sp2) + (1901754883694737/50000000000000 : ℝ)*(sp4) + (237719314581941/6250000000000 : ℝ)*(sp5) + (118859646336983/3125000000000 : ℝ)*(sp6) + (59553474276421/4000000000000 : ℝ)*(sp7) + (59553474276421/4000000000000 : ℝ)*(f.failure) + (1901754883694737/50000000000000 : ℝ)*(f.sum) + (14386539377249/5682000000000000000000000000 : ℝ)*base65 + (23311183650373406317/1420500000000000000000000000000000 : ℝ)*base67 + (2734055993637093683/1420500000000000000000000000000000 : ℝ)*base70 + (142611881782655906317/1420500000000000000000000000000000 : ℝ)*base71 + (15805513561379/5682000000000000000000000000 : ℝ)*base73 + (16594832498724093683/1420500000000000000000000000000000 : ℝ)*base76 + (1244880825931593683/1420500000000000000000000000000000 : ℝ)*base78 + (6597467036448093683/1420500000000000000000000000000000 : ℝ)*base80 + (276723928739/5682000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1191/16000000000000000000 : ℝ)*base89 + (1191/16000000000000000000 : ℝ)*base91 + (1191/16000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1640_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1640_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1640_box_0 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1369974237/10000000000 : ℝ)*x 0 + (676317029/1250000000 : ℝ)*x 1 + (2705268087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369974237/10000000000 : ℝ)^4879 ≤ (504984618149/6250000000000 : ℝ)^3855 := by
    have hnat : (1369974237 : ℕ)^4879*6250000000000^3855 ≤ 504984618149^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369974237 10000000000 504984618149 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676317029/1250000000 : ℝ)^4879 ≤ (45960123360187/100000000000000 : ℝ)^3855 := by
    have hnat : (676317029 : ℕ)^4879*100000000000000^3855 ≤ 45960123360187^3855*1250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676317029 1250000000 45960123360187 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705268087/5000000000 : ℝ)^4879 ≤ (45960122736631/100000000000000 : ℝ)^3855 := by
    have hnat : (2705268087 : ℕ)^4879*100000000000000^3855 ≤ 45960122736631^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705268087 5000000000 45960122736631 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1369974237/10000000000 : ℝ), (676317029/1250000000 : ℝ), (2705268087/5000000000 : ℝ)] ![(504984618149/6250000000000 : ℝ), (45960123360187/100000000000000 : ℝ), (45960122736631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1369974237/10000000000 : ℝ)|^4879 ≤ (504984618149/6250000000000 : ℝ)^3855
        have hw : |(-1369974237/10000000000 : ℝ)|=(1369974237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676317029/1250000000 : ℝ)|^4879 ≤ (45960123360187/100000000000000 : ℝ)^3855
        have hw : |(676317029/1250000000 : ℝ)|=(676317029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705268087/5000000000 : ℝ)|^4879 ≤ (45960122736631/100000000000000 : ℝ)^3855
        have hw : |(2705268087/5000000000 : ℝ)|=(2705268087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_1 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251195943/10000000000 : ℝ)*x 0 + (-159389009/1000000000 : ℝ)*x 1 + (2705268077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251195943/10000000000 : ℝ)^4879 ≤ (11063452851383/25000000000000 : ℝ)^3855 := by
    have hnat : (5251195943 : ℕ)^4879*25000000000000^3855 ≤ 11063452851383^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251195943 10000000000 11063452851383 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159389009/1000000000 : ℝ)^4879 ≤ (2446516511491/25000000000000 : ℝ)^3855 := by
    have hnat : (159389009 : ℕ)^4879*25000000000000^3855 ≤ 2446516511491^3855*1000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159389009 1000000000 2446516511491 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705268077/5000000000 : ℝ)^4879 ≤ (11490030630403/25000000000000 : ℝ)^3855 := by
    have hnat : (2705268077 : ℕ)^4879*25000000000000^3855 ≤ 11490030630403^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705268077 5000000000 11490030630403 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251195943/10000000000 : ℝ), (-159389009/1000000000 : ℝ), (2705268077/5000000000 : ℝ)] ![(11063452851383/25000000000000 : ℝ), (2446516511491/25000000000000 : ℝ), (11490030630403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251195943/10000000000 : ℝ)|^4879 ≤ (11063452851383/25000000000000 : ℝ)^3855
        have hw : |(5251195943/10000000000 : ℝ)|=(5251195943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159389009/1000000000 : ℝ)|^4879 ≤ (2446516511491/25000000000000 : ℝ)^3855
        have hw : |(-159389009/1000000000 : ℝ)|=(159389009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705268077/5000000000 : ℝ)|^4879 ≤ (11490030630403/25000000000000 : ℝ)^3855
        have hw : |(2705268077/5000000000 : ℝ)|=(2705268077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_2 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656399511/1250000000 : ℝ)*x 0 + (5410536193/10000000000 : ℝ)*x 1 + (-1593889839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656399511/1250000000 : ℝ)^4879 ≤ (11063453238023/25000000000000 : ℝ)^3855 := by
    have hnat : (656399511 : ℕ)^4879*25000000000000^3855 ≤ 11063453238023^3855*1250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656399511 1250000000 11063453238023 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410536193/10000000000 : ℝ)^4879 ≤ (45960122940899/100000000000000 : ℝ)^3855 := by
    have hnat : (5410536193 : ℕ)^4879*100000000000000^3855 ≤ 45960122940899^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410536193 10000000000 45960122940899 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593889839/10000000000 : ℝ)^4879 ≤ (611629005971/6250000000000 : ℝ)^3855 := by
    have hnat : (1593889839 : ℕ)^4879*6250000000000^3855 ≤ 611629005971^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593889839 10000000000 611629005971 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656399511/1250000000 : ℝ), (5410536193/10000000000 : ℝ), (-1593889839/10000000000 : ℝ)] ![(11063453238023/25000000000000 : ℝ), (45960122940899/100000000000000 : ℝ), (611629005971/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656399511/1250000000 : ℝ)|^4879 ≤ (11063453238023/25000000000000 : ℝ)^3855
        have hw : |(656399511/1250000000 : ℝ)|=(656399511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410536193/10000000000 : ℝ)|^4879 ≤ (45960122940899/100000000000000 : ℝ)^3855
        have hw : |(5410536193/10000000000 : ℝ)|=(5410536193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1593889839/10000000000 : ℝ)|^4879 ≤ (611629005971/6250000000000 : ℝ)^3855
        have hw : |(-1593889839/10000000000 : ℝ)|=(1593889839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_3 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4465971343/10000000000 : ℝ)*x 0 + (1015482307/2500000000 : ℝ)*x 1 + (812385893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4465971343/10000000000 : ℝ)^4879 ≤ (18025753871811/50000000000000 : ℝ)^3855 := by
    have hnat : (4465971343 : ℕ)^4879*50000000000000^3855 ≤ 18025753871811^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465971343 10000000000 18025753871811 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015482307/2500000000 : ℝ)^4879 ≤ (7993561234129/25000000000000 : ℝ)^3855 := by
    have hnat : (1015482307 : ℕ)^4879*25000000000000^3855 ≤ 7993561234129^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015482307 2500000000 7993561234129 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (812385893/2000000000 : ℝ)^4879 ≤ (31974247297661/100000000000000 : ℝ)^3855 := by
    have hnat : (812385893 : ℕ)^4879*100000000000000^3855 ≤ 31974247297661^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812385893 2000000000 31974247297661 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4465971343/10000000000 : ℝ), (1015482307/2500000000 : ℝ), (812385893/2000000000 : ℝ)] ![(18025753871811/50000000000000 : ℝ), (7993561234129/25000000000000 : ℝ), (31974247297661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4465971343/10000000000 : ℝ)|^4879 ≤ (18025753871811/50000000000000 : ℝ)^3855
        have hw : |(4465971343/10000000000 : ℝ)|=(4465971343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015482307/2500000000 : ℝ)|^4879 ≤ (7993561234129/25000000000000 : ℝ)^3855
        have hw : |(1015482307/2500000000 : ℝ)|=(1015482307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(812385893/2000000000 : ℝ)|^4879 ≤ (31974247297661/100000000000000 : ℝ)^3855
        have hw : |(812385893/2000000000 : ℝ)|=(812385893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_4 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1903861743/10000000000 : ℝ)*x 0 + (5215449849/10000000000 : ℝ)*x 1 + (5215449703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1903861743/10000000000 : ℝ)^4879 ≤ (1531777391847/12500000000000 : ℝ)^3855 := by
    have hnat : (1903861743 : ℕ)^4879*12500000000000^3855 ≤ 1531777391847^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903861743 10000000000 1531777391847 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215449849/10000000000 : ℝ)^4879 ≤ (10968222800857/25000000000000 : ℝ)^3855 := by
    have hnat : (5215449849 : ℕ)^4879*25000000000000^3855 ≤ 10968222800857^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215449849 10000000000 10968222800857 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215449703/10000000000 : ℝ)^4879 ≤ (1754915585961/4000000000000 : ℝ)^3855 := by
    have hnat : (5215449703 : ℕ)^4879*4000000000000^3855 ≤ 1754915585961^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215449703 10000000000 1754915585961 4000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1903861743/10000000000 : ℝ), (5215449849/10000000000 : ℝ), (5215449703/10000000000 : ℝ)] ![(1531777391847/12500000000000 : ℝ), (10968222800857/25000000000000 : ℝ), (1754915585961/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1903861743/10000000000 : ℝ)|^4879 ≤ (1531777391847/12500000000000 : ℝ)^3855
        have hw : |(-1903861743/10000000000 : ℝ)|=(1903861743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215449849/10000000000 : ℝ)|^4879 ≤ (10968222800857/25000000000000 : ℝ)^3855
        have hw : |(5215449849/10000000000 : ℝ)|=(5215449849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215449703/10000000000 : ℝ)|^4879 ≤ (1754915585961/4000000000000 : ℝ)^3855
        have hw : |(5215449703/10000000000 : ℝ)|=(5215449703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_5 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692640259/5000000000 : ℝ)*x 0 + (-1677259157/10000000000 : ℝ)*x 1 + (1043089967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692640259/5000000000 : ℝ)^4879 ≤ (2284438433743/5000000000000 : ℝ)^3855 := by
    have hnat : (2692640259 : ℕ)^4879*5000000000000^3855 ≤ 2284438433743^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692640259 5000000000 2284438433743 5000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1677259157/10000000000 : ℝ)^4879 ≤ (10438340255763/100000000000000 : ℝ)^3855 := by
    have hnat : (1677259157 : ℕ)^4879*100000000000000^3855 ≤ 10438340255763^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677259157 10000000000 10438340255763 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043089967/2000000000 : ℝ)^4879 ≤ (5484111381797/12500000000000 : ℝ)^3855 := by
    have hnat : (1043089967 : ℕ)^4879*12500000000000^3855 ≤ 5484111381797^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043089967 2000000000 5484111381797 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692640259/5000000000 : ℝ), (-1677259157/10000000000 : ℝ), (1043089967/2000000000 : ℝ)] ![(2284438433743/5000000000000 : ℝ), (10438340255763/100000000000000 : ℝ), (5484111381797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692640259/5000000000 : ℝ)|^4879 ≤ (2284438433743/5000000000000 : ℝ)^3855
        have hw : |(2692640259/5000000000 : ℝ)|=(2692640259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1677259157/10000000000 : ℝ)|^4879 ≤ (10438340255763/100000000000000 : ℝ)^3855
        have hw : |(-1677259157/10000000000 : ℝ)|=(1677259157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043089967/2000000000 : ℝ)|^4879 ≤ (5484111381797/12500000000000 : ℝ)^3855
        have hw : |(1043089967/2000000000 : ℝ)|=(1043089967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_6 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385280521/10000000000 : ℝ)*x 0 + (1303862483/2500000000 : ℝ)*x 1 + (-838629511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385280521/10000000000 : ℝ)^4879 ≤ (45688768707073/100000000000000 : ℝ)^3855 := by
    have hnat : (5385280521 : ℕ)^4879*100000000000000^3855 ≤ 45688768707073^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385280521 10000000000 45688768707073 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303862483/2500000000 : ℝ)^4879 ≤ (5484111510887/12500000000000 : ℝ)^3855 := by
    have hnat : (1303862483 : ℕ)^4879*12500000000000^3855 ≤ 5484111510887^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303862483 2500000000 5484111510887 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (838629511/5000000000 : ℝ)^4879 ≤ (417533567697/4000000000000 : ℝ)^3855 := by
    have hnat : (838629511 : ℕ)^4879*4000000000000^3855 ≤ 417533567697^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838629511 5000000000 417533567697 4000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385280521/10000000000 : ℝ), (1303862483/2500000000 : ℝ), (-838629511/5000000000 : ℝ)] ![(45688768707073/100000000000000 : ℝ), (5484111510887/12500000000000 : ℝ), (417533567697/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385280521/10000000000 : ℝ)|^4879 ≤ (45688768707073/100000000000000 : ℝ)^3855
        have hw : |(5385280521/10000000000 : ℝ)|=(5385280521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303862483/2500000000 : ℝ)|^4879 ≤ (5484111510887/12500000000000 : ℝ)^3855
        have hw : |(1303862483/2500000000 : ℝ)|=(1303862483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-838629511/5000000000 : ℝ)|^4879 ≤ (417533567697/4000000000000 : ℝ)^3855
        have hw : |(-838629511/5000000000 : ℝ)|=(838629511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_7 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (780928163/2000000000 : ℝ)*x 0 + (4342265339/10000000000 : ℝ)*x 1 + (67847897/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (780928163/2000000000 : ℝ)^4879 ≤ (30415374004617/100000000000000 : ℝ)^3855 := by
    have hnat : (780928163 : ℕ)^4879*100000000000000^3855 ≤ 30415374004617^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780928163 2000000000 30415374004617 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4342265339/10000000000 : ℝ)^4879 ≤ (34792312637719/100000000000000 : ℝ)^3855 := by
    have hnat : (4342265339 : ℕ)^4879*100000000000000^3855 ≤ 34792312637719^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342265339 10000000000 34792312637719 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67847897/156250000 : ℝ)^4879 ≤ (8698078334359/25000000000000 : ℝ)^3855 := by
    have hnat : (67847897 : ℕ)^4879*25000000000000^3855 ≤ 8698078334359^3855*156250000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67847897 156250000 8698078334359 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(780928163/2000000000 : ℝ), (4342265339/10000000000 : ℝ), (67847897/156250000 : ℝ)] ![(30415374004617/100000000000000 : ℝ), (34792312637719/100000000000000 : ℝ), (8698078334359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(780928163/2000000000 : ℝ)|^4879 ≤ (30415374004617/100000000000000 : ℝ)^3855
        have hw : |(780928163/2000000000 : ℝ)|=(780928163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4342265339/10000000000 : ℝ)|^4879 ≤ (34792312637719/100000000000000 : ℝ)^3855
        have hw : |(4342265339/10000000000 : ℝ)|=(4342265339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67847897/156250000 : ℝ)|^4879 ≤ (8698078334359/25000000000000 : ℝ)^3855
        have hw : |(67847897/156250000 : ℝ)|=(67847897/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_8 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-71602469/400000000 : ℝ)*x 0 + (1015076239/2000000000 : ℝ)*x 1 + (544011563/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71602469/400000000 : ℝ)^4879 ≤ (566732406573/5000000000000 : ℝ)^3855 := by
    have hnat : (71602469 : ℕ)^4879*5000000000000^3855 ≤ 566732406573^3855*400000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71602469 400000000 566732406573 5000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015076239/2000000000 : ℝ)^4879 ≤ (42386990928481/100000000000000 : ℝ)^3855 := by
    have hnat : (1015076239 : ℕ)^4879*100000000000000^3855 ≤ 42386990928481^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015076239 2000000000 42386990928481 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544011563/1000000000 : ℝ)^4879 ≤ (46278360928643/100000000000000 : ℝ)^3855 := by
    have hnat : (544011563 : ℕ)^4879*100000000000000^3855 ≤ 46278360928643^3855*1000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544011563 1000000000 46278360928643 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71602469/400000000 : ℝ), (1015076239/2000000000 : ℝ), (544011563/1000000000 : ℝ)] ![(566732406573/5000000000000 : ℝ), (42386990928481/100000000000000 : ℝ), (46278360928643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71602469/400000000 : ℝ)|^4879 ≤ (566732406573/5000000000000 : ℝ)^3855
        have hw : |(-71602469/400000000 : ℝ)|=(71602469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015076239/2000000000 : ℝ)|^4879 ≤ (42386990928481/100000000000000 : ℝ)^3855
        have hw : |(1015076239/2000000000 : ℝ)|=(1015076239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544011563/1000000000 : ℝ)|^4879 ≤ (46278360928643/100000000000000 : ℝ)^3855
        have hw : |(544011563/1000000000 : ℝ)|=(544011563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_9 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104617321/200000000 : ℝ)*x 0 + (-1580812993/10000000000 : ℝ)*x 1 + (2720057519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104617321/200000000 : ℝ)^4879 ≤ (5504635713671/12500000000000 : ℝ)^3855 := by
    have hnat : (104617321 : ℕ)^4879*12500000000000^3855 ≤ 5504635713671^3855*200000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104617321 200000000 5504635713671 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580812993/10000000000 : ℝ)^4879 ≤ (1210569965299/12500000000000 : ℝ)^3855 := by
    have hnat : (1580812993 : ℕ)^4879*12500000000000^3855 ≤ 1210569965299^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580812993 10000000000 1210569965299 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720057519/5000000000 : ℝ)^4879 ≤ (925567091097/2000000000000 : ℝ)^3855 := by
    have hnat : (2720057519 : ℕ)^4879*2000000000000^3855 ≤ 925567091097^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720057519 5000000000 925567091097 2000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104617321/200000000 : ℝ), (-1580812993/10000000000 : ℝ), (2720057519/5000000000 : ℝ)] ![(5504635713671/12500000000000 : ℝ), (1210569965299/12500000000000 : ℝ), (925567091097/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104617321/200000000 : ℝ)|^4879 ≤ (5504635713671/12500000000000 : ℝ)^3855
        have hw : |(104617321/200000000 : ℝ)|=(104617321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1580812993/10000000000 : ℝ)|^4879 ≤ (1210569965299/12500000000000 : ℝ)^3855
        have hw : |(-1580812993/10000000000 : ℝ)|=(1580812993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720057519/5000000000 : ℝ)|^4879 ≤ (925567091097/2000000000000 : ℝ)^3855
        have hw : |(2720057519/5000000000 : ℝ)|=(2720057519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_10 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307716679/2500000000 : ℝ)*x 0 + (5440115449/10000000000 : ℝ)*x 1 + (-395202877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307716679/2500000000 : ℝ)^4879 ≤ (8807418561113/20000000000000 : ℝ)^3855 := by
    have hnat : (1307716679 : ℕ)^4879*20000000000000^3855 ≤ 8807418561113^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307716679 2500000000 8807418561113 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440115449/10000000000 : ℝ)^4879 ≤ (46278358979899/100000000000000 : ℝ)^3855 := by
    have hnat : (5440115449 : ℕ)^4879*100000000000000^3855 ≤ 46278358979899^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440115449 10000000000 46278358979899 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395202877/2500000000 : ℝ)^4879 ≤ (9684548208233/100000000000000 : ℝ)^3855 := by
    have hnat : (395202877 : ℕ)^4879*100000000000000^3855 ≤ 9684548208233^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395202877 2500000000 9684548208233 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307716679/2500000000 : ℝ), (5440115449/10000000000 : ℝ), (-395202877/2500000000 : ℝ)] ![(8807418561113/20000000000000 : ℝ), (46278358979899/100000000000000 : ℝ), (9684548208233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307716679/2500000000 : ℝ)|^4879 ≤ (8807418561113/20000000000000 : ℝ)^3855
        have hw : |(1307716679/2500000000 : ℝ)|=(1307716679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440115449/10000000000 : ℝ)|^4879 ≤ (46278358979899/100000000000000 : ℝ)^3855
        have hw : |(5440115449/10000000000 : ℝ)|=(5440115449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395202877/2500000000 : ℝ)|^4879 ≤ (9684548208233/100000000000000 : ℝ)^3855
        have hw : |(-395202877/2500000000 : ℝ)|=(395202877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_11 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2274349979/5000000000 : ℝ)*x 0 + (4019347251/10000000000 : ℝ)*x 1 + (4019345813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2274349979/5000000000 : ℝ)^4879 ≤ (922469943113/2500000000000 : ℝ)^3855 := by
    have hnat : (2274349979 : ℕ)^4879*2500000000000^3855 ≤ 922469943113^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274349979 5000000000 922469943113 2500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4019347251/10000000000 : ℝ)^4879 ≤ (197191301683/625000000000 : ℝ)^3855 := by
    have hnat : (4019347251 : ℕ)^4879*625000000000^3855 ≤ 197191301683^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019347251 10000000000 197191301683 625000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4019345813/10000000000 : ℝ)^4879 ≤ (6310118796611/20000000000000 : ℝ)^3855 := by
    have hnat : (4019345813 : ℕ)^4879*20000000000000^3855 ≤ 6310118796611^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019345813 10000000000 6310118796611 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2274349979/5000000000 : ℝ), (4019347251/10000000000 : ℝ), (4019345813/10000000000 : ℝ)] ![(922469943113/2500000000000 : ℝ), (197191301683/625000000000 : ℝ), (6310118796611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2274349979/5000000000 : ℝ)|^4879 ≤ (922469943113/2500000000000 : ℝ)^3855
        have hw : |(2274349979/5000000000 : ℝ)|=(2274349979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4019347251/10000000000 : ℝ)|^4879 ≤ (197191301683/625000000000 : ℝ)^3855
        have hw : |(4019347251/10000000000 : ℝ)|=(4019347251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4019345813/10000000000 : ℝ)|^4879 ≤ (6310118796611/20000000000000 : ℝ)^3855
        have hw : |(4019345813/10000000000 : ℝ)|=(4019345813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_12 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1482134683/10000000000 : ℝ)*x 0 + (5545171527/10000000000 : ℝ)*x 1 + (1039122103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1482134683/10000000000 : ℝ)^4879 ≤ (446294311559/5000000000000 : ℝ)^3855 := by
    have hnat : (1482134683 : ℕ)^4879*5000000000000^3855 ≤ 446294311559^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482134683 10000000000 446294311559 5000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5545171527/10000000000 : ℝ)^4879 ≤ (47412337192561/100000000000000 : ℝ)^3855 := by
    have hnat : (5545171527 : ℕ)^4879*100000000000000^3855 ≤ 47412337192561^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5545171527 10000000000 47412337192561 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039122103/2000000000 : ℝ)^4879 ≤ (8732355314581/20000000000000 : ℝ)^3855 := by
    have hnat : (1039122103 : ℕ)^4879*20000000000000^3855 ≤ 8732355314581^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039122103 2000000000 8732355314581 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1482134683/10000000000 : ℝ), (5545171527/10000000000 : ℝ), (1039122103/2000000000 : ℝ)] ![(446294311559/5000000000000 : ℝ), (47412337192561/100000000000000 : ℝ), (8732355314581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1482134683/10000000000 : ℝ)|^4879 ≤ (446294311559/5000000000000 : ℝ)^3855
        have hw : |(-1482134683/10000000000 : ℝ)|=(1482134683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5545171527/10000000000 : ℝ)|^4879 ≤ (47412337192561/100000000000000 : ℝ)^3855
        have hw : |(5545171527/10000000000 : ℝ)|=(5545171527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039122103/2000000000 : ℝ)|^4879 ≤ (8732355314581/20000000000000 : ℝ)^3855
        have hw : |(1039122103/2000000000 : ℝ)|=(1039122103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_13 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349731377/2500000000 : ℝ)*x 0 + (-1685449237/10000000000 : ℝ)*x 1 + (207824417/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349731377/2500000000 : ℝ)^4879 ≤ (45835332507859/100000000000000 : ℝ)^3855 := by
    have hnat : (1349731377 : ℕ)^4879*100000000000000^3855 ≤ 45835332507859^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349731377 2500000000 45835332507859 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1685449237/10000000000 : ℝ)^4879 ≤ (1312861483351/12500000000000 : ℝ)^3855 := by
    have hnat : (1685449237 : ℕ)^4879*12500000000000^3855 ≤ 1312861483351^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685449237 10000000000 1312861483351 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207824417/400000000 : ℝ)^4879 ≤ (136443048799/312500000000 : ℝ)^3855 := by
    have hnat : (207824417 : ℕ)^4879*312500000000^3855 ≤ 136443048799^3855*400000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207824417 400000000 136443048799 312500000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349731377/2500000000 : ℝ), (-1685449237/10000000000 : ℝ), (207824417/400000000 : ℝ)] ![(45835332507859/100000000000000 : ℝ), (1312861483351/12500000000000 : ℝ), (136443048799/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349731377/2500000000 : ℝ)|^4879 ≤ (45835332507859/100000000000000 : ℝ)^3855
        have hw : |(1349731377/2500000000 : ℝ)|=(1349731377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1685449237/10000000000 : ℝ)|^4879 ≤ (1312861483351/12500000000000 : ℝ)^3855
        have hw : |(-1685449237/10000000000 : ℝ)|=(1685449237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207824417/400000000 : ℝ)|^4879 ≤ (136443048799/312500000000 : ℝ)^3855
        have hw : |(207824417/400000000 : ℝ)|=(207824417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_14 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699462369/5000000000 : ℝ)*x 0 + (5195610789/10000000000 : ℝ)*x 1 + (-337089959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699462369/5000000000 : ℝ)^4879 ≤ (45835324234341/100000000000000 : ℝ)^3855 := by
    have hnat : (2699462369 : ℕ)^4879*100000000000000^3855 ≤ 45835324234341^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699462369 5000000000 45835324234341 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195610789/10000000000 : ℝ)^4879 ≤ (43661779487121/100000000000000 : ℝ)^3855 := by
    have hnat : (5195610789 : ℕ)^4879*100000000000000^3855 ≤ 43661779487121^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195610789 10000000000 43661779487121 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337089959/2000000000 : ℝ)^4879 ≤ (10502896267631/100000000000000 : ℝ)^3855 := by
    have hnat : (337089959 : ℕ)^4879*100000000000000^3855 ≤ 10502896267631^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337089959 2000000000 10502896267631 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699462369/5000000000 : ℝ), (5195610789/10000000000 : ℝ), (-337089959/2000000000 : ℝ)] ![(45835324234341/100000000000000 : ℝ), (43661779487121/100000000000000 : ℝ), (10502896267631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699462369/5000000000 : ℝ)|^4879 ≤ (45835324234341/100000000000000 : ℝ)^3855
        have hw : |(2699462369/5000000000 : ℝ)|=(2699462369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195610789/10000000000 : ℝ)|^4879 ≤ (43661779487121/100000000000000 : ℝ)^3855
        have hw : |(5195610789/10000000000 : ℝ)|=(5195610789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337089959/2000000000 : ℝ)|^4879 ≤ (10502896267631/100000000000000 : ℝ)^3855
        have hw : |(-337089959/2000000000 : ℝ)|=(337089959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_box_15 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (480741031/1250000000 : ℝ)*x 0 + (2185361633/5000000000 : ℝ)*x 1 + (4370722587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480741031/1250000000 : ℝ)^4879 ≤ (29837706194103/100000000000000 : ℝ)^3855 := by
    have hnat : (480741031 : ℕ)^4879*100000000000000^3855 ≤ 29837706194103^3855*1250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480741031 1250000000 29837706194103 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185361633/5000000000 : ℝ)^4879 ≤ (35081150345001/100000000000000 : ℝ)^3855 := by
    have hnat : (2185361633 : ℕ)^4879*100000000000000^3855 ≤ 35081150345001^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185361633 5000000000 35081150345001 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4370722587/10000000000 : ℝ)^4879 ≤ (17540571723711/50000000000000 : ℝ)^3855 := by
    have hnat : (4370722587 : ℕ)^4879*50000000000000^3855 ≤ 17540571723711^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370722587 10000000000 17540571723711 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(480741031/1250000000 : ℝ), (2185361633/5000000000 : ℝ), (4370722587/10000000000 : ℝ)] ![(29837706194103/100000000000000 : ℝ), (35081150345001/100000000000000 : ℝ), (17540571723711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(480741031/1250000000 : ℝ)|^4879 ≤ (29837706194103/100000000000000 : ℝ)^3855
        have hw : |(480741031/1250000000 : ℝ)|=(480741031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2185361633/5000000000 : ℝ)|^4879 ≤ (35081150345001/100000000000000 : ℝ)^3855
        have hw : |(2185361633/5000000000 : ℝ)|=(2185361633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4370722587/10000000000 : ℝ)|^4879 ≤ (17540571723711/50000000000000 : ℝ)^3855
        have hw : |(4370722587/10000000000 : ℝ)|=(4370722587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1640_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65027/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29259/50000 : ℝ) ∧ (20253/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44063/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10617/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (576747565516693/25000000000000000000 : ℝ) := by
    have hpowers : (10617/100000 : ℝ)^4875 ≤ (576747565516693/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10617 : ℕ)^4875*25000000000000000000^1024 ≤ 576747565516693^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10617 100000 576747565516693 25000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10617/100000 : ℝ)) (X := (576747565516693/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16287/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (4423017581889861/25000000000000000000 : ℝ) := by
    have hpowers : (16287/100000 : ℝ)^4875 ≤ (4423017581889861/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16287 : ℕ)^4875*25000000000000000000^1024 ≤ 4423017581889861^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16287 100000 4423017581889861 25000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16287/100000 : ℝ)) (X := (4423017581889861/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500576747565516693/12500000000000000000 : ℝ) ≤ (10000096915486271/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (12500576747565516693/12500000000000000000 : ℝ)^1024 ≤ (10000096915486271/10000000000000000 : ℝ)^4875 := by
      have hnat : (12500576747565516693 : ℕ)^1024*10000000000000000^4875 ≤ 10000096915486271^4875*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500576747565516693 12500000000000000000 10000096915486271 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000096915486271/10000000000000000 : ℝ)) (X := (12500576747565516693/12500000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502499882573703277/12500000000000000000 : ℝ) ≤ (2500105012413199/2500000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (12502499882573703277/12500000000000000000 : ℝ)^1024 ≤ (2500105012413199/2500000000000000 : ℝ)^4875 := by
      have hnat : (12502499882573703277 : ℕ)^1024*2500000000000000^4875 ≤ 2500105012413199^4875*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502499882573703277 12500000000000000000 2500105012413199 2500000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500105012413199/2500000000000000 : ℝ)) (X := (12502499882573703277/12500000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504423017581889861/12500000000000000000 : ℝ) ≤ (10000743183819321/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (12504423017581889861/12500000000000000000 : ℝ)^1024 ≤ (10000743183819321/10000000000000000 : ℝ)^4875 := by
      have hnat : (12504423017581889861 : ℕ)^1024*10000000000000000^4875 ≤ 10000743183819321^4875*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504423017581889861 12500000000000000000 10000743183819321 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000743183819321/10000000000000000 : ℝ)) (X := (12504423017581889861/12500000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(576747565516693/25000000000000000000 : ℝ) ≤ ((236223700332979853/236250000000000000 : ℝ)+2*(12925366661/22680000000000 : ℝ)*(10617/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (236223700332979853/236250000000000000 : ℝ)+2*(12925366661/22680000000000 : ℝ)*(10617/100000 : ℝ)=(10000096915486271/10000000000000000 : ℝ) by norm_num, show 1+2*(576747565516693/25000000000000000000 : ℝ)=(12500576747565516693/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4423017581889861/25000000000000000000 : ℝ)+(576747565516693/25000000000000000000 : ℝ) ≤ ((236223700332979853/236250000000000000 : ℝ)+(12925366661/22680000000000 : ℝ)*((16287/100000 : ℝ)+(10617/100000 : ℝ)))^(4875/1024 : ℝ) := by
    rw [show (236223700332979853/236250000000000000 : ℝ)+(12925366661/22680000000000 : ℝ)*((16287/100000 : ℝ)+(10617/100000 : ℝ))=(2500105012413199/2500000000000000 : ℝ) by norm_num, show 1+(4423017581889861/25000000000000000000 : ℝ)+(576747565516693/25000000000000000000 : ℝ)=(12502499882573703277/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4423017581889861/25000000000000000000 : ℝ) ≤ ((236223700332979853/236250000000000000 : ℝ)+2*(12925366661/22680000000000 : ℝ)*(16287/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (236223700332979853/236250000000000000 : ℝ)+2*(12925366661/22680000000000 : ℝ)*(16287/100000 : ℝ)=(10000743183819321/10000000000000000 : ℝ) by norm_num, show 1+2*(4423017581889861/25000000000000000000 : ℝ)=(12504423017581889861/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (236223700332979853/236250000000000000 : ℝ)*(X 1 0+X 2 0)+(12925366661/22680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (236223700332979853/236250000000000000 : ℝ)) (alpha := (12925366661/22680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (236223700332979853/236250000000000000 : ℝ)*(X 0 1+X 2 1)+(12925366661/22680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (236223700332979853/236250000000000000 : ℝ)) (alpha := (12925366661/22680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (236223700332979853/236250000000000000 : ℝ)*(X 0 2+X 1 2)+(12925366661/22680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (236223700332979853/236250000000000000 : ℝ)) (alpha := (12925366661/22680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1369974237/10000000000 : ℝ)*X 0 0+(676317029/1250000000 : ℝ)*X 0 1+(2705268087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251195943/10000000000 : ℝ)*X 1 0+(-159389009/1000000000 : ℝ)*X 1 1+(2705268077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((656399511/1250000000 : ℝ)*X 2 0+(5410536193/10000000000 : ℝ)*X 2 1+(-1593889839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4465971343/10000000000 : ℝ)*X 0 0+(1015482307/2500000000 : ℝ)*X 0 1+(812385893/2000000000 : ℝ)*X 0 2+(4465971343/10000000000 : ℝ)*X 1 0+(1015482307/2500000000 : ℝ)*X 1 1+(812385893/2000000000 : ℝ)*X 1 2+(4465971343/10000000000 : ℝ)*X 2 0+(1015482307/2500000000 : ℝ)*X 2 1+(812385893/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1903861743/10000000000 : ℝ)*X 0 0+(5215449849/10000000000 : ℝ)*X 0 1+(5215449703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692640259/5000000000 : ℝ)*X 1 0+(-1677259157/10000000000 : ℝ)*X 1 1+(1043089967/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5385280521/10000000000 : ℝ)*X 2 0+(1303862483/2500000000 : ℝ)*X 2 1+(-838629511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((780928163/2000000000 : ℝ)*X 0 0+(4342265339/10000000000 : ℝ)*X 0 1+(67847897/156250000 : ℝ)*X 0 2+(780928163/2000000000 : ℝ)*X 1 0+(4342265339/10000000000 : ℝ)*X 1 1+(67847897/156250000 : ℝ)*X 1 2+(780928163/2000000000 : ℝ)*X 2 0+(4342265339/10000000000 : ℝ)*X 2 1+(67847897/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-71602469/400000000 : ℝ)*X 0 0+(1015076239/2000000000 : ℝ)*X 0 1+(544011563/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((104617321/200000000 : ℝ)*X 1 0+(-1580812993/10000000000 : ℝ)*X 1 1+(2720057519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307716679/2500000000 : ℝ)*X 2 0+(5440115449/10000000000 : ℝ)*X 2 1+(-395202877/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2274349979/5000000000 : ℝ)*X 0 0+(4019347251/10000000000 : ℝ)*X 0 1+(4019345813/10000000000 : ℝ)*X 0 2+(2274349979/5000000000 : ℝ)*X 1 0+(4019347251/10000000000 : ℝ)*X 1 1+(4019345813/10000000000 : ℝ)*X 1 2+(2274349979/5000000000 : ℝ)*X 2 0+(4019347251/10000000000 : ℝ)*X 2 1+(4019345813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1482134683/10000000000 : ℝ)*X 0 0+(5545171527/10000000000 : ℝ)*X 0 1+(1039122103/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1349731377/2500000000 : ℝ)*X 1 0+(-1685449237/10000000000 : ℝ)*X 1 1+(207824417/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2699462369/5000000000 : ℝ)*X 2 0+(5195610789/10000000000 : ℝ)*X 2 1+(-337089959/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((480741031/1250000000 : ℝ)*X 0 0+(2185361633/5000000000 : ℝ)*X 0 1+(4370722587/10000000000 : ℝ)*X 0 2+(480741031/1250000000 : ℝ)*X 1 0+(2185361633/5000000000 : ℝ)*X 1 1+(4370722587/10000000000 : ℝ)*X 1 2+(480741031/1250000000 : ℝ)*X 2 0+(2185361633/5000000000 : ℝ)*X 2 1+(4370722587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65027/100000 : ℝ) ≤ (-640083826290204848100793288453/984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25979221/100000000000000 : ℝ)*(lower1) + (16627879/50000000000000 : ℝ)*(lower2) + (5160561/50000000000000 : ℝ)*(lower3) + (373991/100000000000000 : ℝ)*(lower4) + (14777199/100000000000000 : ℝ)*(lower5) + (1739865477585723/100000000000000 : ℝ)*(major0) + (1739865477585723/100000000000000 : ℝ)*(major1) + (1739865477585723/100000000000000 : ℝ)*(major2) + (25224910918673/1000000000000 : ℝ)*(sp4) + (2522491876979459/100000000000000 : ℝ)*(sp5) + (2522468332191411/100000000000000 : ℝ)*(sp6) + (978913874426147/100000000000000 : ℝ)*(sp7) + (392556079/50000000000000 : ℝ)*(sp8) + (1471549253/6250000000000 : ℝ)*(sp14) + (978913874426147/100000000000000 : ℝ)*(f.failure) + (2522491876979459/100000000000000 : ℝ)*(f.sum) + (689310052111/378000000000000000000000000 : ℝ)*base65 + (28893184495469969/23625000000000000000000000000000 : ℝ)*base67 + (259557176104155031/23625000000000000000000000000000 : ℝ)*base70 + (35660810296530031/23625000000000000000000000000000 : ℝ)*base72 + (1439250933241/378000000000000000000000000 : ℝ)*base73 + (75298662219780031/23625000000000000000000000000000 : ℝ)*base76 + (105989052031155031/23625000000000000000000000000000 : ℝ)*base78 + (141818169410280031/23625000000000000000000000000000 : ℝ)*base80 + (1015235368271/378000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (876463/400000000000000000000 : ℝ)*base90 + (876463/400000000000000000000 : ℝ)*base92 + (876463/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29259/50000 : ℝ) ≤ (28803036837418514923632917921/49218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (65612379/100000000000000 : ℝ)*(upper0) + (12484231/12500000000000 : ℝ)*(upper2) + (4802187/25000000000000 : ℝ)*(upper3) + (36362991/20000000000000 : ℝ)*(upper4) + (15689579/100000000000000 : ℝ)*(upper5) + (365770971614131/20000000000000 : ℝ)*(major0) + (365770971614131/20000000000000 : ℝ)*(major1) + (365770971614131/20000000000000 : ℝ)*(major2) + (163076265287933/6250000000000 : ℝ)*(sp0) + (2609211986287113/100000000000000 : ℝ)*(sp1) + (1304609103604381/50000000000000 : ℝ)*(sp2) + (16077853952117/1562500000000 : ℝ)*(sp3) + (2037398167/100000000000000 : ℝ)*(sp6) + (1651663963/20000000000000 : ℝ)*(sp9) + (16077853952117/1562500000000 : ℝ)*(f.failure) + (163076265287933/6250000000000 : ℝ)*(f.sum) + (1219256120923/1134000000000000000000000000 : ℝ)*base65 + (102985617092723021/14175000000000000000000000000000 : ℝ)*base68 + (19890474786323021/14175000000000000000000000000000 : ℝ)*base70 + (22316774147001979/14175000000000000000000000000000 : ℝ)*base71 + (4240806857111/1134000000000000000000000000 : ℝ)*base74 + (5015908768823021/14175000000000000000000000000000 : ℝ)*base76 + (75992021240948021/14175000000000000000000000000000 : ℝ)*base78 + (461649722811173021/14175000000000000000000000000000 : ℝ)*base80 + (2700715933397/1134000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (50907/6250000000000000000 : ℝ)*base89 + (50907/6250000000000000000 : ℝ)*base91 + (50907/6250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20253/25000 : ℝ) ≤ (379757402432916505911536867/468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (99319891/50000000000000 : ℝ)*(lower3) + (21072577/5000000000000 : ℝ)*(upper4) + (20198219/20000000000000 : ℝ)*(lower5) + (19262625533067/1000000000000 : ℝ)*(major0) + (19262625533067/1000000000000 : ℝ)*(major1) + (19262625533067/1000000000000 : ℝ)*(major2) + (71602763/3125000000000 : ℝ)*(sp0) + (14573483973/100000000000000 : ℝ)*(sp1) + (132065028681/100000000000000 : ℝ)*(sp2) + (8415969647/12500000000000 : ℝ)*(sp3) + (685432487991537/25000000000000 : ℝ)*(sp8) + (274171766977059/10000000000000 : ℝ)*(sp9) + (1370800089112941/50000000000000 : ℝ)*(sp10) + (54186028238099/5000000000000 : ℝ)*(sp11) + (270946973129789/25000000000000 : ℝ)*(f.failure) + (685433060813641/25000000000000 : ℝ)*(f.sum) + (59161525591/13500000000000000000000000 : ℝ)*base66 + (215324325170657/33750000000000000000000000000 : ℝ)*base68 + (134324383355657/33750000000000000000000000000 : ℝ)*base70 + (57329193556907/33750000000000000000000000000 : ℝ)*base72 + (113515843/13500000000000000000000000 : ℝ)*base74 + (118270812388157/33750000000000000000000000000 : ℝ)*base76 + (72380087090657/33750000000000000000000000000 : ℝ)*base78 + (169685114086907/33750000000000000000000000000 : ℝ)*base80 + (3890230621/5400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1152719/100000000000000000000 : ℝ)*base89 + (1152719/100000000000000000000 : ℝ)*base91 + (1152719/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-44063/50000 : ℝ) ≤ (-847131320093052525712819879/961303710937500000000000000 : ℝ) := by norm_num
    linear_combination (3087099/10000000000000 : ℝ)*(lower0) + (90020611/100000000000000 : ℝ)*(upper1) + (60426453/50000000000000 : ℝ)*(upper3) + (208834809/100000000000000 : ℝ)*(lower4) + (984914869195743/50000000000000 : ℝ)*(major0) + (984914869195743/50000000000000 : ℝ)*(major1) + (984914869195743/50000000000000 : ℝ)*(major2) + (28518436703/100000000000000 : ℝ)*(sp5) + (5033581789/25000000000000 : ℝ)*(sp6) + (21889017521/50000000000000 : ℝ)*(sp7) + (178795839683571/6250000000000 : ℝ)*(sp12) + (178794057281277/6250000000000 : ℝ)*(sp13) + (143035665030499/5000000000000 : ℝ)*(sp14) + (554128327194711/50000000000000 : ℝ)*(sp15) + (69268777026529/6250000000000 : ℝ)*(f.failure) + (178795839683571/6250000000000 : ℝ)*(f.sum) + (433635092419/189000000000000000000000000 : ℝ)*base65 + (113853785304977971/11812500000000000000000000000000 : ℝ)*base68 + (62527985279477971/11812500000000000000000000000000 : ℝ)*base70 + (53127793937852971/11812500000000000000000000000000 : ℝ)*base72 + (89984585063/94500000000000000000000000 : ℝ)*base73 + (8702422546459529/11812500000000000000000000000000 : ℝ)*base75 + (115260857702477971/11812500000000000000000000000000 : ℝ)*base78 + (59668677658727971/11812500000000000000000000000000 : ℝ)*base80 + (2231818453939/189000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3259/25000000000000000000 : ℝ)*base89 + (3259/25000000000000000000 : ℝ)*base91 + (3259/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1640_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65027/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29259/50000 : ℝ) else (20253/25000 : ℝ) ≤ X j i ∧ X j i ≤ (44063/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1640_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1640_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65027/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29259/50000 : ℝ) else (20253/25000 : ℝ) ≤ X j i ∧ X j i ≤ (44063/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1640_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1640_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1640_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65027/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29259/50000 : ℝ) else (20253/25000 : ℝ) ≤ X j i ∧ X j i ≤ (44063/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1640_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
