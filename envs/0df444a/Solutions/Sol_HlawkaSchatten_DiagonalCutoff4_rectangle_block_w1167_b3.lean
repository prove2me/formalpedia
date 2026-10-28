-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:12.927329+00:00
-- url     : https://prove2.me/submissions/2023d31a-973c-4fb5-9a8d-547a349e213c

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
theorem support_rectangle_w1167_box_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2028910671/10000000000 : ℝ)*x 0 + (215038131/400000000 : ℝ)*x 1 + (5375951699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028910671/10000000000 : ℝ)^1045 ≤ (12091955067351/100000000000000 : ℝ)^789 := by
    have hnat : (2028910671 : ℕ)^1045*100000000000000^789 ≤ 12091955067351^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028910671 10000000000 12091955067351 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215038131/400000000 : ℝ)^1045 ≤ (21977015496073/50000000000000 : ℝ)^789 := by
    have hnat : (215038131 : ℕ)^1045*50000000000000^789 ≤ 21977015496073^789*400000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215038131 400000000 21977015496073 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375951699/10000000000 : ℝ)^1045 ≤ (43954013925873/100000000000000 : ℝ)^789 := by
    have hnat : (5375951699 : ℕ)^1045*100000000000000^789 ≤ 43954013925873^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375951699 10000000000 43954013925873 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2028910671/10000000000 : ℝ), (215038131/400000000 : ℝ), (5375951699/10000000000 : ℝ)] ![(12091955067351/100000000000000 : ℝ), (21977015496073/50000000000000 : ℝ), (43954013925873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2028910671/10000000000 : ℝ)|^1045 ≤ (12091955067351/100000000000000 : ℝ)^789
        have hw : |(-2028910671/10000000000 : ℝ)|=(2028910671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215038131/400000000 : ℝ)|^1045 ≤ (21977015496073/50000000000000 : ℝ)^789
        have hw : |(215038131/400000000 : ℝ)|=(215038131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375951699/10000000000 : ℝ)|^1045 ≤ (43954013925873/100000000000000 : ℝ)^789
        have hw : |(5375951699/10000000000 : ℝ)|=(5375951699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5296208089/10000000000 : ℝ)*x 0 + (-2137118923/10000000000 : ℝ)*x 1 + (5375952819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296208089/10000000000 : ℝ)^1045 ≤ (43092567085697/100000000000000 : ℝ)^789 := by
    have hnat : (5296208089 : ℕ)^1045*100000000000000^789 ≤ 43092567085697^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296208089 10000000000 43092567085697 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2137118923/10000000000 : ℝ)^1045 ≤ (12953406841487/100000000000000 : ℝ)^789 := by
    have hnat : (2137118923 : ℕ)^1045*100000000000000^789 ≤ 12953406841487^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137118923 10000000000 12953406841487 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375952819/10000000000 : ℝ)^1045 ≤ (43954026054189/100000000000000 : ℝ)^789 := by
    have hnat : (5375952819 : ℕ)^1045*100000000000000^789 ≤ 43954026054189^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375952819 10000000000 43954026054189 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296208089/10000000000 : ℝ), (-2137118923/10000000000 : ℝ), (5375952819/10000000000 : ℝ)] ![(43092567085697/100000000000000 : ℝ), (12953406841487/100000000000000 : ℝ), (43954026054189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296208089/10000000000 : ℝ)|^1045 ≤ (43092567085697/100000000000000 : ℝ)^789
        have hw : |(5296208089/10000000000 : ℝ)|=(5296208089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2137118923/10000000000 : ℝ)|^1045 ≤ (12953406841487/100000000000000 : ℝ)^789
        have hw : |(-2137118923/10000000000 : ℝ)|=(2137118923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375952819/10000000000 : ℝ)|^1045 ≤ (43954026054189/100000000000000 : ℝ)^789
        have hw : |(5375952819/10000000000 : ℝ)|=(5375952819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5296207679/10000000000 : ℝ)*x 0 + (671994057/1250000000 : ℝ)*x 1 + (-2137119963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296207679/10000000000 : ℝ)^1045 ≤ (43092562667343/100000000000000 : ℝ)^789 := by
    have hnat : (5296207679 : ℕ)^1045*100000000000000^789 ≤ 43092562667343^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296207679 10000000000 43092562667343 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671994057/1250000000 : ℝ)^1045 ≤ (8790804424663/20000000000000 : ℝ)^789 := by
    have hnat : (671994057 : ℕ)^1045*20000000000000^789 ≤ 8790804424663^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671994057 1250000000 8790804424663 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2137119963/10000000000 : ℝ)^1045 ≤ (6476707595181/50000000000000 : ℝ)^789 := by
    have hnat : (2137119963 : ℕ)^1045*50000000000000^789 ≤ 6476707595181^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137119963 10000000000 6476707595181 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296207679/10000000000 : ℝ), (671994057/1250000000 : ℝ), (-2137119963/10000000000 : ℝ)] ![(43092562667343/100000000000000 : ℝ), (8790804424663/20000000000000 : ℝ), (6476707595181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296207679/10000000000 : ℝ)|^1045 ≤ (43092562667343/100000000000000 : ℝ)^789
        have hw : |(5296207679/10000000000 : ℝ)|=(5296207679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671994057/1250000000 : ℝ)|^1045 ≤ (8790804424663/20000000000000 : ℝ)^789
        have hw : |(671994057/1250000000 : ℝ)|=(671994057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2137119963/10000000000 : ℝ)|^1045 ≤ (6476707595181/50000000000000 : ℝ)^789
        have hw : |(-2137119963/10000000000 : ℝ)|=(2137119963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4468452909/10000000000 : ℝ)*x 0 + (861922527/2000000000 : ℝ)*x 1 + (4309612217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4468452909/10000000000 : ℝ)^1045 ≤ (17203496371277/50000000000000 : ℝ)^789 := by
    have hnat : (4468452909 : ℕ)^1045*50000000000000^789 ≤ 17203496371277^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468452909 10000000000 17203496371277 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861922527/2000000000 : ℝ)^1045 ≤ (4099563215913/12500000000000 : ℝ)^789 := by
    have hnat : (861922527 : ℕ)^1045*12500000000000^789 ≤ 4099563215913^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861922527 2000000000 4099563215913 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4309612217/10000000000 : ℝ)^1045 ≤ (16398250757087/50000000000000 : ℝ)^789 := by
    have hnat : (4309612217 : ℕ)^1045*50000000000000^789 ≤ 16398250757087^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309612217 10000000000 16398250757087 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4468452909/10000000000 : ℝ), (861922527/2000000000 : ℝ), (4309612217/10000000000 : ℝ)] ![(17203496371277/50000000000000 : ℝ), (4099563215913/12500000000000 : ℝ), (16398250757087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4468452909/10000000000 : ℝ)|^1045 ≤ (17203496371277/50000000000000 : ℝ)^789
        have hw : |(4468452909/10000000000 : ℝ)|=(4468452909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861922527/2000000000 : ℝ)|^1045 ≤ (4099563215913/12500000000000 : ℝ)^789
        have hw : |(861922527/2000000000 : ℝ)|=(861922527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4309612217/10000000000 : ℝ)|^1045 ≤ (16398250757087/50000000000000 : ℝ)^789
        have hw : |(4309612217/10000000000 : ℝ)|=(4309612217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-285306861/1250000000 : ℝ)*x 0 + (1320362397/2500000000 : ℝ)*x 1 + (1320362423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285306861/1250000000 : ℝ)^1045 ≤ (7066404982029/50000000000000 : ℝ)^789 := by
    have hnat : (285306861 : ℕ)^1045*50000000000000^789 ≤ 7066404982029^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285306861 1250000000 7066404982029 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320362397/2500000000 : ℝ)^1045 ≤ (5366699306873/12500000000000 : ℝ)^789 := by
    have hnat : (1320362397 : ℕ)^1045*12500000000000^789 ≤ 5366699306873^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320362397 2500000000 5366699306873 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320362423/2500000000 : ℝ)^1045 ≤ (42933595574723/100000000000000 : ℝ)^789 := by
    have hnat : (1320362423 : ℕ)^1045*100000000000000^789 ≤ 42933595574723^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320362423 2500000000 42933595574723 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-285306861/1250000000 : ℝ), (1320362397/2500000000 : ℝ), (1320362423/2500000000 : ℝ)] ![(7066404982029/50000000000000 : ℝ), (5366699306873/12500000000000 : ℝ), (42933595574723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-285306861/1250000000 : ℝ)|^1045 ≤ (7066404982029/50000000000000 : ℝ)^789
        have hw : |(-285306861/1250000000 : ℝ)|=(285306861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320362397/2500000000 : ℝ)|^1045 ≤ (5366699306873/12500000000000 : ℝ)^789
        have hw : |(1320362397/2500000000 : ℝ)|=(1320362397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320362423/2500000000 : ℝ)|^1045 ≤ (42933595574723/100000000000000 : ℝ)^789
        have hw : |(1320362423/2500000000 : ℝ)|=(1320362423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5362936673/10000000000 : ℝ)*x 0 + (-2174367231/10000000000 : ℝ)*x 1 + (660181249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362936673/10000000000 : ℝ)^1045 ≤ (21906565751441/50000000000000 : ℝ)^789 := by
    have hnat : (5362936673 : ℕ)^1045*50000000000000^789 ≤ 21906565751441^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362936673 10000000000 21906565751441 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174367231/10000000000 : ℝ)^1045 ≤ (3313317418697/25000000000000 : ℝ)^789 := by
    have hnat : (2174367231 : ℕ)^1045*25000000000000^789 ≤ 3313317418697^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174367231 10000000000 3313317418697 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660181249/1250000000 : ℝ)^1045 ≤ (42933598804739/100000000000000 : ℝ)^789 := by
    have hnat : (660181249 : ℕ)^1045*100000000000000^789 ≤ 42933598804739^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660181249 1250000000 42933598804739 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362936673/10000000000 : ℝ), (-2174367231/10000000000 : ℝ), (660181249/1250000000 : ℝ)] ![(21906565751441/50000000000000 : ℝ), (3313317418697/25000000000000 : ℝ), (42933598804739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362936673/10000000000 : ℝ)|^1045 ≤ (21906565751441/50000000000000 : ℝ)^789
        have hw : |(5362936673/10000000000 : ℝ)|=(5362936673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2174367231/10000000000 : ℝ)|^1045 ≤ (3313317418697/25000000000000 : ℝ)^789
        have hw : |(-2174367231/10000000000 : ℝ)|=(2174367231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660181249/1250000000 : ℝ)|^1045 ≤ (42933598804739/100000000000000 : ℝ)^789
        have hw : |(660181249/1250000000 : ℝ)|=(660181249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1340734247/2500000000 : ℝ)*x 0 + (5281450087/10000000000 : ℝ)*x 1 + (-1087183341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340734247/2500000000 : ℝ)^1045 ≤ (4381313491129/10000000000000 : ℝ)^789 := by
    have hnat : (1340734247 : ℕ)^1045*10000000000000^789 ≤ 4381313491129^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340734247 2500000000 4381313491129 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281450087/10000000000 : ℝ)^1045 ≤ (42933599827577/100000000000000 : ℝ)^789 := by
    have hnat : (5281450087 : ℕ)^1045*100000000000000^789 ≤ 42933599827577^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281450087 10000000000 42933599827577 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087183341/5000000000 : ℝ)^1045 ≤ (13253265242767/100000000000000 : ℝ)^789 := by
    have hnat : (1087183341 : ℕ)^1045*100000000000000^789 ≤ 13253265242767^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087183341 5000000000 13253265242767 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340734247/2500000000 : ℝ), (5281450087/10000000000 : ℝ), (-1087183341/5000000000 : ℝ)] ![(4381313491129/10000000000000 : ℝ), (42933599827577/100000000000000 : ℝ), (13253265242767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340734247/2500000000 : ℝ)|^1045 ≤ (4381313491129/10000000000000 : ℝ)^789
        have hw : |(1340734247/2500000000 : ℝ)|=(1340734247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281450087/10000000000 : ℝ)|^1045 ≤ (42933599827577/100000000000000 : ℝ)^789
        have hw : |(5281450087/10000000000 : ℝ)|=(5281450087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087183341/5000000000 : ℝ)|^1045 ≤ (13253265242767/100000000000000 : ℝ)^789
        have hw : |(-1087183341/5000000000 : ℝ)|=(1087183341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212675363/500000000 : ℝ)*x 0 + (4417065061/10000000000 : ℝ)*x 1 + (2208532079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212675363/500000000 : ℝ)^1045 ≤ (32232202966449/100000000000000 : ℝ)^789 := by
    have hnat : (212675363 : ℕ)^1045*100000000000000^789 ≤ 32232202966449^789*500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212675363 500000000 32232202966449 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417065061/10000000000 : ℝ)^1045 ≤ (3388390309309/10000000000000 : ℝ)^789 := by
    have hnat : (4417065061 : ℕ)^1045*10000000000000^789 ≤ 3388390309309^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417065061 10000000000 3388390309309 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208532079/5000000000 : ℝ)^1045 ≤ (67767787837/200000000000 : ℝ)^789 := by
    have hnat : (2208532079 : ℕ)^1045*200000000000^789 ≤ 67767787837^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208532079 5000000000 67767787837 200000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212675363/500000000 : ℝ), (4417065061/10000000000 : ℝ), (2208532079/5000000000 : ℝ)] ![(32232202966449/100000000000000 : ℝ), (3388390309309/10000000000000 : ℝ), (67767787837/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212675363/500000000 : ℝ)|^1045 ≤ (32232202966449/100000000000000 : ℝ)^789
        have hw : |(212675363/500000000 : ℝ)|=(212675363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417065061/10000000000 : ℝ)|^1045 ≤ (3388390309309/10000000000000 : ℝ)^789
        have hw : |(4417065061/10000000000 : ℝ)|=(4417065061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208532079/5000000000 : ℝ)|^1045 ≤ (67767787837/200000000000 : ℝ)^789
        have hw : |(2208532079/5000000000 : ℝ)|=(2208532079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_8 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-17835251/80000000 : ℝ)*x 0 + (2608565177/5000000000 : ℝ)*x 1 + (5385563729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17835251/80000000 : ℝ)^1045 ≤ (6849704681201/50000000000000 : ℝ)^789 := by
    have hnat : (17835251 : ℕ)^1045*50000000000000^789 ≤ 6849704681201^789*80000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17835251 80000000 6849704681201 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608565177/5000000000 : ℝ)^1045 ≤ (4224245926163/10000000000000 : ℝ)^789 := by
    have hnat : (2608565177 : ℕ)^1045*10000000000000^789 ≤ 4224245926163^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608565177 5000000000 4224245926163 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385563729/10000000000 : ℝ)^1045 ≤ (5507266421059/12500000000000 : ℝ)^789 := by
    have hnat : (5385563729 : ℕ)^1045*12500000000000^789 ≤ 5507266421059^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385563729 10000000000 5507266421059 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17835251/80000000 : ℝ), (2608565177/5000000000 : ℝ), (5385563729/10000000000 : ℝ)] ![(6849704681201/50000000000000 : ℝ), (4224245926163/10000000000000 : ℝ), (5507266421059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17835251/80000000 : ℝ)|^1045 ≤ (6849704681201/50000000000000 : ℝ)^789
        have hw : |(-17835251/80000000 : ℝ)|=(17835251/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608565177/5000000000 : ℝ)|^1045 ≤ (4224245926163/10000000000000 : ℝ)^789
        have hw : |(2608565177/5000000000 : ℝ)|=(2608565177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385563729/10000000000 : ℝ)|^1045 ≤ (5507266421059/12500000000000 : ℝ)^789
        have hw : |(5385563729/10000000000 : ℝ)|=(5385563729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_9 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2644709523/5000000000 : ℝ)*x 0 + (-2133261591/10000000000 : ℝ)*x 1 + (168298861/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644709523/5000000000 : ℝ)^1045 ≤ (86038840743/200000000000 : ℝ)^789 := by
    have hnat : (2644709523 : ℕ)^1045*200000000000^789 ≤ 86038840743^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644709523 5000000000 86038840743 200000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2133261591/10000000000 : ℝ)^1045 ≤ (12922450160909/100000000000000 : ℝ)^789 := by
    have hnat : (2133261591 : ℕ)^1045*100000000000000^789 ≤ 12922450160909^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133261591 10000000000 12922450160909 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168298861/312500000 : ℝ)^1045 ≤ (44058129450653/100000000000000 : ℝ)^789 := by
    have hnat : (168298861 : ℕ)^1045*100000000000000^789 ≤ 44058129450653^789*312500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168298861 312500000 44058129450653 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644709523/5000000000 : ℝ), (-2133261591/10000000000 : ℝ), (168298861/312500000 : ℝ)] ![(86038840743/200000000000 : ℝ), (12922450160909/100000000000000 : ℝ), (44058129450653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644709523/5000000000 : ℝ)|^1045 ≤ (86038840743/200000000000 : ℝ)^789
        have hw : |(2644709523/5000000000 : ℝ)|=(2644709523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2133261591/10000000000 : ℝ)|^1045 ≤ (12922450160909/100000000000000 : ℝ)^789
        have hw : |(-2133261591/10000000000 : ℝ)|=(2133261591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168298861/312500000 : ℝ)|^1045 ≤ (44058129450653/100000000000000 : ℝ)^789
        have hw : |(168298861/312500000 : ℝ)|=(168298861/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_10 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5289418961/10000000000 : ℝ)*x 0 + (1346390877/2500000000 : ℝ)*x 1 + (-426652353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289418961/10000000000 : ℝ)^1045 ≤ (43019419455881/100000000000000 : ℝ)^789 := by
    have hnat : (5289418961 : ℕ)^1045*100000000000000^789 ≤ 43019419455881^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289418961 10000000000 43019419455881 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346390877/2500000000 : ℝ)^1045 ≤ (11014532243477/25000000000000 : ℝ)^789 := by
    have hnat : (1346390877 : ℕ)^1045*25000000000000^789 ≤ 11014532243477^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346390877 2500000000 11014532243477 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426652353/2000000000 : ℝ)^1045 ≤ (12922451556921/100000000000000 : ℝ)^789 := by
    have hnat : (426652353 : ℕ)^1045*100000000000000^789 ≤ 12922451556921^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426652353 2000000000 12922451556921 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289418961/10000000000 : ℝ), (1346390877/2500000000 : ℝ), (-426652353/2000000000 : ℝ)] ![(43019419455881/100000000000000 : ℝ), (11014532243477/25000000000000 : ℝ), (12922451556921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289418961/10000000000 : ℝ)|^1045 ≤ (43019419455881/100000000000000 : ℝ)^789
        have hw : |(5289418961/10000000000 : ℝ)|=(5289418961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346390877/2500000000 : ℝ)|^1045 ≤ (11014532243477/25000000000000 : ℝ)^789
        have hw : |(1346390877/2500000000 : ℝ)|=(1346390877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426652353/2000000000 : ℝ)|^1045 ≤ (12922451556921/100000000000000 : ℝ)^789
        have hw : |(-426652353/2000000000 : ℝ)|=(426652353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_11 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (44900373/100000000 : ℝ)*x 0 + (4298679657/10000000000 : ℝ)*x 1 + (4298679731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44900373/100000000 : ℝ)^1045 ≤ (1731364483617/5000000000000 : ℝ)^789 := by
    have hnat : (44900373 : ℕ)^1045*5000000000000^789 ≤ 1731364483617^789*100000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44900373 100000000 1731364483617 5000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4298679657/10000000000 : ℝ)^1045 ≤ (6537270956683/20000000000000 : ℝ)^789 := by
    have hnat : (4298679657 : ℕ)^1045*20000000000000^789 ≤ 6537270956683^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298679657 10000000000 6537270956683 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4298679731/10000000000 : ℝ)^1045 ≤ (6537271105733/20000000000000 : ℝ)^789 := by
    have hnat : (4298679731 : ℕ)^1045*20000000000000^789 ≤ 6537271105733^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298679731 10000000000 6537271105733 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44900373/100000000 : ℝ), (4298679657/10000000000 : ℝ), (4298679731/10000000000 : ℝ)] ![(1731364483617/5000000000000 : ℝ), (6537270956683/20000000000000 : ℝ), (6537271105733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44900373/100000000 : ℝ)|^1045 ≤ (1731364483617/5000000000000 : ℝ)^789
        have hw : |(44900373/100000000 : ℝ)|=(44900373/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4298679657/10000000000 : ℝ)|^1045 ≤ (6537270956683/20000000000000 : ℝ)^789
        have hw : |(4298679657/10000000000 : ℝ)|=(4298679657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4298679731/10000000000 : ℝ)|^1045 ≤ (6537271105733/20000000000000 : ℝ)^789
        have hw : |(4298679731/10000000000 : ℝ)|=(4298679731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_12 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041131207/5000000000 : ℝ)*x 0 + (1087802389/2000000000 : ℝ)*x 1 + (5273399567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041131207/5000000000 : ℝ)^1045 ≤ (250297525101/2000000000000 : ℝ)^789 := by
    have hnat : (1041131207 : ℕ)^1045*2000000000000^789 ≤ 250297525101^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041131207 5000000000 250297525101 2000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087802389/2000000000 : ℝ)^1045 ≤ (44638180149051/100000000000000 : ℝ)^789 := by
    have hnat : (1087802389 : ℕ)^1045*100000000000000^789 ≤ 44638180149051^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087802389 2000000000 44638180149051 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273399567/10000000000 : ℝ)^1045 ≤ (8569388715223/20000000000000 : ℝ)^789 := by
    have hnat : (5273399567 : ℕ)^1045*20000000000000^789 ≤ 8569388715223^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273399567 10000000000 8569388715223 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041131207/5000000000 : ℝ), (1087802389/2000000000 : ℝ), (5273399567/10000000000 : ℝ)] ![(250297525101/2000000000000 : ℝ), (44638180149051/100000000000000 : ℝ), (8569388715223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041131207/5000000000 : ℝ)|^1045 ≤ (250297525101/2000000000000 : ℝ)^789
        have hw : |(-1041131207/5000000000 : ℝ)|=(1041131207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087802389/2000000000 : ℝ)|^1045 ≤ (44638180149051/100000000000000 : ℝ)^789
        have hw : |(1087802389/2000000000 : ℝ)|=(1087802389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273399567/10000000000 : ℝ)|^1045 ≤ (8569388715223/20000000000000 : ℝ)^789
        have hw : |(5273399567/10000000000 : ℝ)|=(5273399567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_13 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342154883/2500000000 : ℝ)*x 0 + (-1088741277/5000000000 : ℝ)*x 1 + (5273399443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342154883/2500000000 : ℝ)^1045 ≤ (43874632538503/100000000000000 : ℝ)^789 := by
    have hnat : (1342154883 : ℕ)^1045*100000000000000^789 ≤ 43874632538503^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342154883 2500000000 43874632538503 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088741277/5000000000 : ℝ)^1045 ≤ (6639212600621/50000000000000 : ℝ)^789 := by
    have hnat : (1088741277 : ℕ)^1045*50000000000000^789 ≤ 6639212600621^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088741277 5000000000 6639212600621 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273399443/10000000000 : ℝ)^1045 ≤ (21423471120851/50000000000000 : ℝ)^789 := by
    have hnat : (5273399443 : ℕ)^1045*50000000000000^789 ≤ 21423471120851^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273399443 10000000000 21423471120851 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342154883/2500000000 : ℝ), (-1088741277/5000000000 : ℝ), (5273399443/10000000000 : ℝ)] ![(43874632538503/100000000000000 : ℝ), (6639212600621/50000000000000 : ℝ), (21423471120851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342154883/2500000000 : ℝ)|^1045 ≤ (43874632538503/100000000000000 : ℝ)^789
        have hw : |(1342154883/2500000000 : ℝ)|=(1342154883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088741277/5000000000 : ℝ)|^1045 ≤ (6639212600621/50000000000000 : ℝ)^789
        have hw : |(-1088741277/5000000000 : ℝ)|=(1088741277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273399443/10000000000 : ℝ)|^1045 ≤ (21423471120851/50000000000000 : ℝ)^789
        have hw : |(5273399443/10000000000 : ℝ)|=(5273399443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_14 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342154909/2500000000 : ℝ)*x 0 + (2636699797/5000000000 : ℝ)*x 1 + (-2177482213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342154909/2500000000 : ℝ)^1045 ≤ (8774926732841/20000000000000 : ℝ)^789 := by
    have hnat : (1342154909 : ℕ)^1045*20000000000000^789 ≤ 8774926732841^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342154909 2500000000 8774926732841 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636699797/5000000000 : ℝ)^1045 ≤ (2677933991667/6250000000000 : ℝ)^789 := by
    have hnat : (2636699797 : ℕ)^1045*6250000000000^789 ≤ 2677933991667^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636699797 5000000000 2677933991667 6250000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177482213/10000000000 : ℝ)^1045 ≤ (2655684489421/20000000000000 : ℝ)^789 := by
    have hnat : (2177482213 : ℕ)^1045*20000000000000^789 ≤ 2655684489421^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177482213 10000000000 2655684489421 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342154909/2500000000 : ℝ), (2636699797/5000000000 : ℝ), (-2177482213/10000000000 : ℝ)] ![(8774926732841/20000000000000 : ℝ), (2677933991667/6250000000000 : ℝ), (2655684489421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342154909/2500000000 : ℝ)|^1045 ≤ (8774926732841/20000000000000 : ℝ)^789
        have hw : |(1342154909/2500000000 : ℝ)|=(1342154909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636699797/5000000000 : ℝ)|^1045 ≤ (2677933991667/6250000000000 : ℝ)^789
        have hw : |(2636699797/5000000000 : ℝ)|=(2636699797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177482213/10000000000 : ℝ)|^1045 ≤ (2655684489421/20000000000000 : ℝ)^789
        have hw : |(-2177482213/10000000000 : ℝ)|=(2177482213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_box_15 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2117483609/5000000000 : ℝ)*x 0 + (885242457/2000000000 : ℝ)*x 1 + (4426212279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117483609/5000000000 : ℝ)^1045 ≤ (6409251525189/20000000000000 : ℝ)^789 := by
    have hnat : (2117483609 : ℕ)^1045*20000000000000^789 ≤ 6409251525189^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117483609 5000000000 6409251525189 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885242457/2000000000 : ℝ)^1045 ≤ (3397687121331/10000000000000 : ℝ)^789 := by
    have hnat : (885242457 : ℕ)^1045*10000000000000^789 ≤ 3397687121331^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885242457 2000000000 3397687121331 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426212279/10000000000 : ℝ)^1045 ≤ (33976871152309/100000000000000 : ℝ)^789 := by
    have hnat : (4426212279 : ℕ)^1045*100000000000000^789 ≤ 33976871152309^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426212279 10000000000 33976871152309 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117483609/5000000000 : ℝ), (885242457/2000000000 : ℝ), (4426212279/10000000000 : ℝ)] ![(6409251525189/20000000000000 : ℝ), (3397687121331/10000000000000 : ℝ), (33976871152309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117483609/5000000000 : ℝ)|^1045 ≤ (6409251525189/20000000000000 : ℝ)^789
        have hw : |(2117483609/5000000000 : ℝ)|=(2117483609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(885242457/2000000000 : ℝ)|^1045 ≤ (3397687121331/10000000000000 : ℝ)^789
        have hw : |(885242457/2000000000 : ℝ)|=(885242457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426212279/10000000000 : ℝ)|^1045 ≤ (33976871152309/100000000000000 : ℝ)^789
        have hw : |(4426212279/10000000000 : ℝ)|=(4426212279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31117/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29659/50000 : ℝ) ∧ (19971/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4159/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5693/50000 : ℝ) ^ (8359/2048 : ℝ) ≤ (2815583543271331/20000000000000000000 : ℝ) := by
    have hpowers : (5693/50000 : ℝ)^8359 ≤ (2815583543271331/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5693 : ℕ)^8359*20000000000000000000^2048 ≤ 2815583543271331^2048*50000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5693 50000 2815583543271331 20000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5693/50000 : ℝ)) (X := (2815583543271331/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14063/100000 : ℝ) ^ (8359/2048 : ℝ) ≤ (1666532012522307/5000000000000000000 : ℝ) := by
    have hpowers : (14063/100000 : ℝ)^8359 ≤ (1666532012522307/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14063 : ℕ)^8359*5000000000000000000^2048 ≤ 1666532012522307^2048*100000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14063 100000 1666532012522307 5000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14063/100000 : ℝ)) (X := (1666532012522307/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002815583543271331/10000000000000000000 : ℝ) ≤ (1000068975981699/1000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (10002815583543271331/10000000000000000000 : ℝ)^2048 ≤ (1000068975981699/1000000000000000 : ℝ)^8359 := by
      have hnat : (10002815583543271331 : ℕ)^2048*1000000000000000^8359 ≤ 1000068975981699^8359*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002815583543271331 10000000000000000000 1000068975981699 1000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000068975981699/1000000000000000 : ℝ)) (X := (10002815583543271331/10000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009481711593360559/20000000000000000000 : ℝ) ≤ (2500290331843623/2500000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (20009481711593360559/20000000000000000000 : ℝ)^2048 ≤ (2500290331843623/2500000000000000 : ℝ)^8359 := by
      have hnat : (20009481711593360559 : ℕ)^2048*2500000000000000^8359 ≤ 2500290331843623^8359*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009481711593360559 20000000000000000000 2500290331843623 2500000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500290331843623/2500000000000000 : ℝ)) (X := (20009481711593360559/20000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501666532012522307/2500000000000000000 : ℝ) ≤ (5000816447465997/5000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (2501666532012522307/2500000000000000000 : ℝ)^2048 ≤ (5000816447465997/5000000000000000 : ℝ)^8359 := by
      have hnat : (2501666532012522307 : ℕ)^2048*5000000000000000^8359 ≤ 5000816447465997^8359*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501666532012522307 2500000000000000000 5000816447465997 5000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000816447465997/5000000000000000 : ℝ)) (X := (2501666532012522307/2500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2815583543271331/20000000000000000000 : ℝ) ≤ ((13380553975305323343/13385000000000000000 : ℝ)+2*(235783778751/133850000000000 : ℝ)*(5693/50000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (13380553975305323343/13385000000000000000 : ℝ)+2*(235783778751/133850000000000 : ℝ)*(5693/50000 : ℝ)=(1000068975981699/1000000000000000 : ℝ) by norm_num, show 1+2*(2815583543271331/20000000000000000000 : ℝ)=(10002815583543271331/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1666532012522307/5000000000000000000 : ℝ)+(2815583543271331/20000000000000000000 : ℝ) ≤ ((13380553975305323343/13385000000000000000 : ℝ)+(235783778751/133850000000000 : ℝ)*((14063/100000 : ℝ)+(5693/50000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (13380553975305323343/13385000000000000000 : ℝ)+(235783778751/133850000000000 : ℝ)*((14063/100000 : ℝ)+(5693/50000 : ℝ))=(2500290331843623/2500000000000000 : ℝ) by norm_num, show 1+(1666532012522307/5000000000000000000 : ℝ)+(2815583543271331/20000000000000000000 : ℝ)=(20009481711593360559/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1666532012522307/5000000000000000000 : ℝ) ≤ ((13380553975305323343/13385000000000000000 : ℝ)+2*(235783778751/133850000000000 : ℝ)*(14063/100000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (13380553975305323343/13385000000000000000 : ℝ)+2*(235783778751/133850000000000 : ℝ)*(14063/100000 : ℝ)=(5000816447465997/5000000000000000 : ℝ) by norm_num, show 1+2*(1666532012522307/5000000000000000000 : ℝ)=(2501666532012522307/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13380553975305323343/13385000000000000000 : ℝ)*(X 1 0+X 2 0)+(235783778751/133850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (13380553975305323343/13385000000000000000 : ℝ)) (alpha := (235783778751/133850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13380553975305323343/13385000000000000000 : ℝ)*(X 0 1+X 2 1)+(235783778751/133850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (13380553975305323343/13385000000000000000 : ℝ)) (alpha := (235783778751/133850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13380553975305323343/13385000000000000000 : ℝ)*(X 0 2+X 1 2)+(235783778751/133850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (13380553975305323343/13385000000000000000 : ℝ)) (alpha := (235783778751/133850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2028910671/10000000000 : ℝ)*X 0 0+(215038131/400000000 : ℝ)*X 0 1+(5375951699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296208089/10000000000 : ℝ)*X 1 0+(-2137118923/10000000000 : ℝ)*X 1 1+(5375952819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296207679/10000000000 : ℝ)*X 2 0+(671994057/1250000000 : ℝ)*X 2 1+(-2137119963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4468452909/10000000000 : ℝ)*X 0 0+(861922527/2000000000 : ℝ)*X 0 1+(4309612217/10000000000 : ℝ)*X 0 2+(4468452909/10000000000 : ℝ)*X 1 0+(861922527/2000000000 : ℝ)*X 1 1+(4309612217/10000000000 : ℝ)*X 1 2+(4468452909/10000000000 : ℝ)*X 2 0+(861922527/2000000000 : ℝ)*X 2 1+(4309612217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-285306861/1250000000 : ℝ)*X 0 0+(1320362397/2500000000 : ℝ)*X 0 1+(1320362423/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362936673/10000000000 : ℝ)*X 1 0+(-2174367231/10000000000 : ℝ)*X 1 1+(660181249/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340734247/2500000000 : ℝ)*X 2 0+(5281450087/10000000000 : ℝ)*X 2 1+(-1087183341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((212675363/500000000 : ℝ)*X 0 0+(4417065061/10000000000 : ℝ)*X 0 1+(2208532079/5000000000 : ℝ)*X 0 2+(212675363/500000000 : ℝ)*X 1 0+(4417065061/10000000000 : ℝ)*X 1 1+(2208532079/5000000000 : ℝ)*X 1 2+(212675363/500000000 : ℝ)*X 2 0+(4417065061/10000000000 : ℝ)*X 2 1+(2208532079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-17835251/80000000 : ℝ)*X 0 0+(2608565177/5000000000 : ℝ)*X 0 1+(5385563729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644709523/5000000000 : ℝ)*X 1 0+(-2133261591/10000000000 : ℝ)*X 1 1+(168298861/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289418961/10000000000 : ℝ)*X 2 0+(1346390877/2500000000 : ℝ)*X 2 1+(-426652353/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((44900373/100000000 : ℝ)*X 0 0+(4298679657/10000000000 : ℝ)*X 0 1+(4298679731/10000000000 : ℝ)*X 0 2+(44900373/100000000 : ℝ)*X 1 0+(4298679657/10000000000 : ℝ)*X 1 1+(4298679731/10000000000 : ℝ)*X 1 2+(44900373/100000000 : ℝ)*X 2 0+(4298679657/10000000000 : ℝ)*X 2 1+(4298679731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1041131207/5000000000 : ℝ)*X 0 0+(1087802389/2000000000 : ℝ)*X 0 1+(5273399567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1342154883/2500000000 : ℝ)*X 1 0+(-1088741277/5000000000 : ℝ)*X 1 1+(5273399443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342154909/2500000000 : ℝ)*X 2 0+(2636699797/5000000000 : ℝ)*X 2 1+(-2177482213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2117483609/5000000000 : ℝ)*X 0 0+(885242457/2000000000 : ℝ)*X 0 1+(4426212279/10000000000 : ℝ)*X 0 2+(2117483609/5000000000 : ℝ)*X 1 0+(885242457/2000000000 : ℝ)*X 1 1+(4426212279/10000000000 : ℝ)*X 1 2+(2117483609/5000000000 : ℝ)*X 2 0+(885242457/2000000000 : ℝ)*X 2 1+(4426212279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31117/50000 : ℝ) ≤ (-1041216441634226658389012559/1673125000000000000000000000 : ℝ) := by norm_num
    linear_combination (305595297/100000000000000 : ℝ)*(upper1) + (103598043/50000000000000 : ℝ)*(upper4) + (335371537/100000000000000 : ℝ)*(upper5) + (985291796003153/25000000000000 : ℝ)*(major0) + (985291796003153/25000000000000 : ℝ)*(major1) + (985291796003153/25000000000000 : ℝ)*(major2) + (9611127159/50000000000000 : ℝ)*(sp3) + (527492759072891/10000000000000 : ℝ)*(sp4) + (5274842882094961/100000000000000 : ℝ)*(sp5) + (5274770667014391/100000000000000 : ℝ)*(sp6) + (1314048113554281/50000000000000 : ℝ)*(sp7) + (44092469/125000000000 : ℝ)*(sp8) + (119982609149/100000000000000 : ℝ)*(sp13) + (96098844859/50000000000000 : ℝ)*(sp14) + (8212860779259/312500000000 : ℝ)*(f.failure) + (527496286470411/10000000000000 : ℝ)*(f.sum) + (28956833817477/6692500000000000000000000000 : ℝ)*base65 + (292630892367300479/334625000000000000000000000000000 : ℝ)*base67 + (5005108683346449521/334625000000000000000000000000000 : ℝ)*base70 + (1575916391723925479/334625000000000000000000000000000 : ℝ)*base71 + (36128354430349/13385000000000000000000000000 : ℝ)*base73 + (3733358941836824521/334625000000000000000000000000000 : ℝ)*base76 + (286407521224550479/334625000000000000000000000000000 : ℝ)*base77 + (883230190861824521/334625000000000000000000000000000 : ℝ)*base80 + (37836043543543/6692500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (136999/15625000000000000000 : ℝ)*base89 + (136999/15625000000000000000 : ℝ)*base91 + (136999/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29659/50000 : ℝ) ≤ (992502227130270175667425923/1673125000000000000000000000 : ℝ) := by norm_num
    linear_combination (162773377/100000000000000 : ℝ)*(upper0) + (266663317/100000000000000 : ℝ)*(upper2) + (24685031/2500000000000 : ℝ)*(upper3) + (37453277/20000000000000 : ℝ)*(upper5) + (500711062776407/12500000000000 : ℝ)*(major0) + (500711062776407/12500000000000 : ℝ)*(major1) + (500711062776407/12500000000000 : ℝ)*(major2) + (1330115735235417/25000000000000 : ℝ)*(sp0) + (665006946763101/12500000000000 : ℝ)*(sp1) + (1329996019173421/25000000000000 : ℝ)*(sp2) + (166946231735241/6250000000000 : ℝ)*(sp3) + (933186677/100000000000000 : ℝ)*(sp7) + (407366836859/100000000000000 : ℝ)*(sp9) + (29929015499/6250000000000 : ℝ)*(sp10) + (2671140640950533/100000000000000 : ℝ)*(f.failure) + (1330115735235417/25000000000000 : ℝ)*(f.sum) + (1997702889347/836562500000000000000000000 : ℝ)*base65 + (1915659637168093899/167312500000000000000000000000000 : ℝ)*base68 + (786994372896843601/167312500000000000000000000000000 : ℝ)*base69 + (8291280059406399/167312500000000000000000000000000 : ℝ)*base72 + (73034698688743/3346250000000000000000000000 : ℝ)*base73 + (2362220982967093601/167312500000000000000000000000000 : ℝ)*base75 + (321904445823031399/167312500000000000000000000000000 : ℝ)*base78 + (4829729002553656101/167312500000000000000000000000000 : ℝ)*base79 + (35023347363949/6692500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (22748913/5000000000000000000000 : ℝ)*base89 + (22748913/5000000000000000000000 : ℝ)*base91 + (22748913/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (19971/25000 : ℝ) ≤ (1336606073929782451273183143/1673125000000000000000000000 : ℝ) := by norm_num
    linear_combination (126932537/100000000000000 : ℝ)*(upper0) + (60336099/100000000000000 : ℝ)*(upper1) + (87347/160000000000 : ℝ)*(upper2) + (145482971/100000000000000 : ℝ)*(lower5) + (2236668466803903/50000000000000 : ℝ)*(major0) + (2236668466803903/50000000000000 : ℝ)*(major1) + (2236668466803903/50000000000000 : ℝ)*(major2) + (3039362179/50000000000000 : ℝ)*(sp1) + (2864912187/25000000000000 : ℝ)*(sp3) + (4859281977/100000000000000 : ℝ)*(sp4) + (1484263558239271/25000000000000 : ℝ)*(sp8) + (2968526506757351/50000000000000 : ℝ)*(sp9) + (296852954611953/5000000000000 : ℝ)*(sp10) + (1491487190484919/50000000000000 : ℝ)*(sp11) + (1491492920309293/50000000000000 : ℝ)*(f.failure) + (296852954611953/5000000000000 : ℝ)*(f.sum) + (2419295937737/3346250000000000000000000000 : ℝ)*base66 + (5486140819336792271/669250000000000000000000000000000 : ℝ)*base68 + (68759803264792271/669250000000000000000000000000000 : ℝ)*base70 + (792701291699207729/669250000000000000000000000000000 : ℝ)*base71 + (138769889783531/6692500000000000000000000000 : ℝ)*base73 + (5252045807654707729/669250000000000000000000000000000 : ℝ)*base75 + (3295124894441292271/669250000000000000000000000000000 : ℝ)*base78 + (6540268785554207729/669250000000000000000000000000000 : ℝ)*base79 + (4958118922961/6692500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (25441273/2500000000000000000000 : ℝ)*base89 + (25441273/2500000000000000000000 : ℝ)*base91 + (25441273/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-4159/5000 : ℝ) ≤ (-278334002478483229386864337926363/334625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1913777/6250000000000 : ℝ)*(lower1) + (35047591/20000000000000 : ℝ)*(lower2) + (55917251/50000000000000 : ℝ)*(upper5) + (4508427876984953/100000000000000 : ℝ)*(major0) + (4508427876984953/100000000000000 : ℝ)*(major1) + (4508427876984953/100000000000000 : ℝ)*(major2) + (4474362389/50000000000000 : ℝ)*(sp0) + (7657286113/3125000000000 : ℝ)*(sp5) + (47175491243/100000000000000 : ℝ)*(sp6) + (15734093809/25000000000000 : ℝ)*(sp7) + (6038186993168587/100000000000000 : ℝ)*(sp12) + (6037950908737749/100000000000000 : ℝ)*(sp13) + (3019074383201061/50000000000000 : ℝ)*(sp14) + (1503161418922919/50000000000000 : ℝ)*(sp15) + (3006385774221073/100000000000000 : ℝ)*(f.failure) + (1207639188378673/20000000000000 : ℝ)*(f.sum) + (21696403258487/6692500000000000000000000000 : ℝ)*base66 + (10065558183622542121/1338500000000000000000000000000000 : ℝ)*base68 + (779402362347542121/1338500000000000000000000000000000 : ℝ)*base70 + (12250126963599042121/1338500000000000000000000000000000 : ℝ)*base72 + (67032348566717/6692500000000000000000000000 : ℝ)*base74 + (6737506534025542121/1338500000000000000000000000000000 : ℝ)*base76 + (215799185760957879/1338500000000000000000000000000000 : ℝ)*base77 + (16960314828166542121/1338500000000000000000000000000000 : ℝ)*base80 + (8089708204469/3346250000000000000000000000 : ℝ)*base81 + (7883853/5000000000000000000000 : ℝ)*base89 + (7883853/5000000000000000000000 : ℝ)*base91 + (7883853/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1167_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29659/50000 : ℝ) else (19971/25000 : ℝ) ≤ X j i ∧ X j i ≤ (4159/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1167_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1167_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29659/50000 : ℝ) else (19971/25000 : ℝ) ≤ X j i ∧ X j i ≤ (4159/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1167_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29659/50000 : ℝ) else (19971/25000 : ℝ) ≤ X j i ∧ X j i ≤ (4159/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
