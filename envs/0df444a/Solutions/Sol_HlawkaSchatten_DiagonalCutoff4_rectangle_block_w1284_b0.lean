-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:17.185065+00:00
-- url     : https://prove2.me/submissions/00c55e95-5d0c-444d-b32e-f6fe865b81dd

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
theorem support_rectangle_w1284_s0_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-921968383/5000000000 : ℝ)*x 0 + (602234581/1000000000 : ℝ)*x 1 + (4796883619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921968383/5000000000 : ℝ)^1061 ≤ (10770705173821/100000000000000 : ℝ)^805 := by
    have hnat : (921968383 : ℕ)^1061*100000000000000^805 ≤ 10770705173821^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921968383 5000000000 10770705173821 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602234581/1000000000 : ℝ)^1061 ≤ (12813520017901/25000000000000 : ℝ)^805 := by
    have hnat : (602234581 : ℕ)^1061*25000000000000^805 ≤ 12813520017901^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602234581 1000000000 12813520017901 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796883619/10000000000 : ℝ)^1061 ≤ (37975214744223/100000000000000 : ℝ)^805 := by
    have hnat : (4796883619 : ℕ)^1061*100000000000000^805 ≤ 37975214744223^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796883619 10000000000 37975214744223 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-921968383/5000000000 : ℝ), (602234581/1000000000 : ℝ), (4796883619/10000000000 : ℝ)] ![(10770705173821/100000000000000 : ℝ), (12813520017901/25000000000000 : ℝ), (37975214744223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-921968383/5000000000 : ℝ)|^1061 ≤ (10770705173821/100000000000000 : ℝ)^805
        have hw : |(-921968383/5000000000 : ℝ)|=(921968383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(602234581/1000000000 : ℝ)|^1061 ≤ (12813520017901/25000000000000 : ℝ)^805
        have hw : |(602234581/1000000000 : ℝ)|=(602234581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796883619/10000000000 : ℝ)|^1061 ≤ (37975214744223/100000000000000 : ℝ)^805
        have hw : |(4796883619/10000000000 : ℝ)|=(4796883619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s0_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1377079117/2500000000 : ℝ)*x 0 + (-2543474149/10000000000 : ℝ)*x 1 + (239844179/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377079117/2500000000 : ℝ)^1061 ≤ (45567968938769/100000000000000 : ℝ)^805 := by
    have hnat : (1377079117 : ℕ)^1061*100000000000000^805 ≤ 45567968938769^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377079117 2500000000 45567968938769 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543474149/10000000000 : ℝ)^1061 ≤ (2057102089293/12500000000000 : ℝ)^805 := by
    have hnat : (2543474149 : ℕ)^1061*12500000000000^805 ≤ 2057102089293^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543474149 10000000000 2057102089293 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239844179/500000000 : ℝ)^1061 ≤ (4746901792161/12500000000000 : ℝ)^805 := by
    have hnat : (239844179 : ℕ)^1061*12500000000000^805 ≤ 4746901792161^805*500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239844179 500000000 4746901792161 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377079117/2500000000 : ℝ), (-2543474149/10000000000 : ℝ), (239844179/500000000 : ℝ)] ![(45567968938769/100000000000000 : ℝ), (2057102089293/12500000000000 : ℝ), (4746901792161/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377079117/2500000000 : ℝ)|^1061 ≤ (45567968938769/100000000000000 : ℝ)^805
        have hw : |(1377079117/2500000000 : ℝ)|=(1377079117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2543474149/10000000000 : ℝ)|^1061 ≤ (2057102089293/12500000000000 : ℝ)^805
        have hw : |(-2543474149/10000000000 : ℝ)|=(2543474149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239844179/500000000 : ℝ)|^1061 ≤ (4746901792161/12500000000000 : ℝ)^805
        have hw : |(239844179/500000000 : ℝ)|=(239844179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s0_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1101663297/2000000000 : ℝ)*x 0 + (2398441797/5000000000 : ℝ)*x 1 + (-254347411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101663297/2000000000 : ℝ)^1061 ≤ (22783984562063/50000000000000 : ℝ)^805 := by
    have hnat : (1101663297 : ℕ)^1061*50000000000000^805 ≤ 22783984562063^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101663297 2000000000 22783984562063 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2398441797/5000000000 : ℝ)^1061 ≤ (4746901810421/12500000000000 : ℝ)^805 := by
    have hnat : (2398441797 : ℕ)^1061*12500000000000^805 ≤ 4746901810421^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398441797 5000000000 4746901810421 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254347411/1000000000 : ℝ)^1061 ≤ (16456816381759/100000000000000 : ℝ)^805 := by
    have hnat : (254347411 : ℕ)^1061*100000000000000^805 ≤ 16456816381759^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254347411 1000000000 16456816381759 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1101663297/2000000000 : ℝ), (2398441797/5000000000 : ℝ), (-254347411/1000000000 : ℝ)] ![(22783984562063/50000000000000 : ℝ), (4746901810421/12500000000000 : ℝ), (16456816381759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1101663297/2000000000 : ℝ)|^1061 ≤ (22783984562063/50000000000000 : ℝ)^805
        have hw : |(1101663297/2000000000 : ℝ)|=(1101663297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2398441797/5000000000 : ℝ)|^1061 ≤ (4746901810421/12500000000000 : ℝ)^805
        have hw : |(2398441797/5000000000 : ℝ)|=(2398441797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254347411/1000000000 : ℝ)|^1061 ≤ (16456816381759/100000000000000 : ℝ)^805
        have hw : |(-254347411/1000000000 : ℝ)|=(254347411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s0_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4187564181/10000000000 : ℝ)*x 0 + (1554983521/5000000000 : ℝ)*x 1 + (2810442719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187564181/10000000000 : ℝ)^1061 ≤ (7937441515631/25000000000000 : ℝ)^805 := by
    have hnat : (4187564181 : ℕ)^1061*25000000000000^805 ≤ 7937441515631^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187564181 10000000000 7937441515631 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1554983521/5000000000 : ℝ)^1061 ≤ (335170549647/1562500000000 : ℝ)^805 := by
    have hnat : (1554983521 : ℕ)^1061*1562500000000^805 ≤ 335170549647^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554983521 5000000000 335170549647 1562500000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2810442719/5000000000 : ℝ)^1061 ≤ (2339965937431/5000000000000 : ℝ)^805 := by
    have hnat : (2810442719 : ℕ)^1061*5000000000000^805 ≤ 2339965937431^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2810442719 5000000000 2339965937431 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187564181/10000000000 : ℝ), (1554983521/5000000000 : ℝ), (2810442719/5000000000 : ℝ)] ![(7937441515631/25000000000000 : ℝ), (335170549647/1562500000000 : ℝ), (2339965937431/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187564181/10000000000 : ℝ)|^1061 ≤ (7937441515631/25000000000000 : ℝ)^805
        have hw : |(4187564181/10000000000 : ℝ)|=(4187564181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1554983521/5000000000 : ℝ)|^1061 ≤ (335170549647/1562500000000 : ℝ)^805
        have hw : |(1554983521/5000000000 : ℝ)|=(1554983521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2810442719/5000000000 : ℝ)|^1061 ≤ (2339965937431/5000000000000 : ℝ)^805
        have hw : |(2810442719/5000000000 : ℝ)|=(2810442719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s0_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1848704743/10000000000 : ℝ)*x 0 + (965704797/2000000000 : ℝ)*x 1 + (5989580837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1848704743/10000000000 : ℝ)^1061 ≤ (216148550009/2000000000000 : ℝ)^805 := by
    have hnat : (1848704743 : ℕ)^1061*2000000000000^805 ≤ 216148550009^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848704743 10000000000 216148550009 2000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965704797/2000000000 : ℝ)^1061 ≤ (9576425864247/25000000000000 : ℝ)^805 := by
    have hnat : (965704797 : ℕ)^1061*25000000000000^805 ≤ 9576425864247^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965704797 2000000000 9576425864247 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5989580837/10000000000 : ℝ)^1061 ≤ (50886869021491/100000000000000 : ℝ)^805 := by
    have hnat : (5989580837 : ℕ)^1061*100000000000000^805 ≤ 50886869021491^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5989580837 10000000000 50886869021491 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1848704743/10000000000 : ℝ), (965704797/2000000000 : ℝ), (5989580837/10000000000 : ℝ)] ![(216148550009/2000000000000 : ℝ), (9576425864247/25000000000000 : ℝ), (50886869021491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1848704743/10000000000 : ℝ)|^1061 ≤ (216148550009/2000000000000 : ℝ)^805
        have hw : |(-1848704743/10000000000 : ℝ)|=(1848704743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965704797/2000000000 : ℝ)|^1061 ≤ (9576425864247/25000000000000 : ℝ)^805
        have hw : |(965704797/2000000000 : ℝ)|=(965704797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5989580837/10000000000 : ℝ)|^1061 ≤ (50886869021491/100000000000000 : ℝ)^805
        have hw : |(5989580837/10000000000 : ℝ)|=(5989580837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s0_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1293688621/2500000000 : ℝ)*x 0 + (-1350774403/10000000000 : ℝ)*x 1 + (1497395847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293688621/2500000000 : ℝ)^1061 ≤ (41966537212541/100000000000000 : ℝ)^805 := by
    have hnat : (1293688621 : ℕ)^1061*100000000000000^805 ≤ 41966537212541^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293688621 2500000000 41966537212541 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350774403/10000000000 : ℝ)^1061 ≤ (357328259359/5000000000000 : ℝ)^805 := by
    have hnat : (1350774403 : ℕ)^1061*5000000000000^805 ≤ 357328259359^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350774403 10000000000 357328259359 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1497395847/2500000000 : ℝ)^1061 ≤ (6360862198353/12500000000000 : ℝ)^805 := by
    have hnat : (1497395847 : ℕ)^1061*12500000000000^805 ≤ 6360862198353^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497395847 2500000000 6360862198353 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293688621/2500000000 : ℝ), (-1350774403/10000000000 : ℝ), (1497395847/2500000000 : ℝ)] ![(41966537212541/100000000000000 : ℝ), (357328259359/5000000000000 : ℝ), (6360862198353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293688621/2500000000 : ℝ)|^1061 ≤ (41966537212541/100000000000000 : ℝ)^805
        have hw : |(1293688621/2500000000 : ℝ)|=(1293688621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1350774403/10000000000 : ℝ)|^1061 ≤ (357328259359/5000000000000 : ℝ)^805
        have hw : |(-1350774403/10000000000 : ℝ)|=(1350774403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1497395847/2500000000 : ℝ)|^1061 ≤ (6360862198353/12500000000000 : ℝ)^805
        have hw : |(1497395847/2500000000 : ℝ)|=(1497395847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s0_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5174755721/10000000000 : ℝ)*x 0 + (5989581253/10000000000 : ℝ)*x 1 + (-270155187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174755721/10000000000 : ℝ)^1061 ≤ (41966550434707/100000000000000 : ℝ)^805 := by
    have hnat : (5174755721 : ℕ)^1061*100000000000000^805 ≤ 41966550434707^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174755721 10000000000 41966550434707 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5989581253/10000000000 : ℝ)^1061 ≤ (25443436839867/50000000000000 : ℝ)^805 := by
    have hnat : (5989581253 : ℕ)^1061*50000000000000^805 ≤ 25443436839867^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5989581253 10000000000 25443436839867 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270155187/2000000000 : ℝ)^1061 ≤ (7146575870171/100000000000000 : ℝ)^805 := by
    have hnat : (270155187 : ℕ)^1061*100000000000000^805 ≤ 7146575870171^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270155187 2000000000 7146575870171 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174755721/10000000000 : ℝ), (5989581253/10000000000 : ℝ), (-270155187/2000000000 : ℝ)] ![(41966550434707/100000000000000 : ℝ), (25443436839867/50000000000000 : ℝ), (7146575870171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174755721/10000000000 : ℝ)|^1061 ≤ (41966550434707/100000000000000 : ℝ)^805
        have hw : |(5174755721/10000000000 : ℝ)|=(5174755721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5989581253/10000000000 : ℝ)|^1061 ≤ (25443436839867/50000000000000 : ℝ)^805
        have hw : |(5989581253/10000000000 : ℝ)|=(5989581253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270155187/2000000000 : ℝ)|^1061 ≤ (7146575870171/100000000000000 : ℝ)^805
        have hw : |(-270155187/2000000000 : ℝ)|=(270155187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s0_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2098668941/5000000000 : ℝ)*x 0 + (2778031303/5000000000 : ℝ)*x 1 + (3177094283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098668941/5000000000 : ℝ)^1061 ≤ (31847471484509/100000000000000 : ℝ)^805 := by
    have hnat : (2098668941 : ℕ)^1061*100000000000000^805 ≤ 31847471484509^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098668941 5000000000 31847471484509 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2778031303/5000000000 : ℝ)^1061 ≤ (230446391529/500000000000 : ℝ)^805 := by
    have hnat : (2778031303 : ℕ)^1061*500000000000^805 ≤ 230446391529^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778031303 5000000000 230446391529 500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3177094283/10000000000 : ℝ)^1061 ≤ (22063250196359/100000000000000 : ℝ)^805 := by
    have hnat : (3177094283 : ℕ)^1061*100000000000000^805 ≤ 22063250196359^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177094283 10000000000 22063250196359 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098668941/5000000000 : ℝ), (2778031303/5000000000 : ℝ), (3177094283/10000000000 : ℝ)] ![(31847471484509/100000000000000 : ℝ), (230446391529/500000000000 : ℝ), (22063250196359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098668941/5000000000 : ℝ)|^1061 ≤ (31847471484509/100000000000000 : ℝ)^805
        have hw : |(2098668941/5000000000 : ℝ)|=(2098668941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2778031303/5000000000 : ℝ)|^1061 ≤ (230446391529/500000000000 : ℝ)^805
        have hw : |(2778031303/5000000000 : ℝ)|=(2778031303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3177094283/10000000000 : ℝ)|^1061 ≤ (22063250196359/100000000000000 : ℝ)^805
        have hw : |(3177094283/10000000000 : ℝ)|=(3177094283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (97/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13647/50000 : ℝ)*pair X 0 0 := by
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
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4243/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4243 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4243*1^1024 ≤ 0^1024*1^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4243/1024 : ℝ) ≤ (448894007035694609/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4243 ≤ (448894007035694609/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4243*20000000000000000000^1024 ≤ 448894007035694609^1024*5^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 448894007035694609 20000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (448894007035694609/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4243 := by
      have hnat : (1 : ℕ)^1024*1^4243 ≤ 1^4243*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20448894007035694609/20000000000000000000 : ℝ) ≤ (5026856268017301/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (20448894007035694609/20000000000000000000 : ℝ)^1024 ≤ (5026856268017301/5000000000000000 : ℝ)^4243 := by
      have hnat : (20448894007035694609 : ℕ)^1024*5000000000000000^4243 ≤ 5026856268017301^4243*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20448894007035694609 20000000000000000000 5026856268017301 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026856268017301/5000000000000000 : ℝ)) (X := (20448894007035694609/20000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10448894007035694609/10000000000000000000 : ℝ) ≤ (2526856268017301/2500000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (10448894007035694609/10000000000000000000 : ℝ)^1024 ≤ (2526856268017301/2500000000000000 : ℝ)^4243 := by
      have hnat : (10448894007035694609 : ℕ)^1024*2500000000000000^4243 ≤ 2526856268017301^4243*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10448894007035694609 10000000000000000000 2526856268017301 2500000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526856268017301/2500000000000000 : ℝ)) (X := (10448894007035694609/10000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26856268017301/2000000000000000 : ℝ)*(0 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26856268017301/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(448894007035694609/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26856268017301/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26856268017301/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026856268017301/5000000000000000 : ℝ) by norm_num, show 1+(448894007035694609/20000000000000000000 : ℝ)+(0 : ℝ)=(20448894007035694609/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(448894007035694609/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26856268017301/2000000000000000 : ℝ)*(2/5 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26856268017301/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526856268017301/2500000000000000 : ℝ) by norm_num, show 1+2*(448894007035694609/20000000000000000000 : ℝ)=(10448894007035694609/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26856268017301/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26856268017301/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26856268017301/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26856268017301/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26856268017301/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26856268017301/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-921968383/5000000000 : ℝ)*X 0 0+(602234581/1000000000 : ℝ)*X 0 1+(4796883619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377079117/2500000000 : ℝ)*X 1 0+(-2543474149/10000000000 : ℝ)*X 1 1+(239844179/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1101663297/2000000000 : ℝ)*X 2 0+(2398441797/5000000000 : ℝ)*X 2 1+(-254347411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4187564181/10000000000 : ℝ)*X 0 0+(1554983521/5000000000 : ℝ)*X 0 1+(2810442719/5000000000 : ℝ)*X 0 2+(4187564181/10000000000 : ℝ)*X 1 0+(1554983521/5000000000 : ℝ)*X 1 1+(2810442719/5000000000 : ℝ)*X 1 2+(4187564181/10000000000 : ℝ)*X 2 0+(1554983521/5000000000 : ℝ)*X 2 1+(2810442719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1848704743/10000000000 : ℝ)*X 0 0+(965704797/2000000000 : ℝ)*X 0 1+(5989580837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293688621/2500000000 : ℝ)*X 1 0+(-1350774403/10000000000 : ℝ)*X 1 1+(1497395847/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174755721/10000000000 : ℝ)*X 2 0+(5989581253/10000000000 : ℝ)*X 2 1+(-270155187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2098668941/5000000000 : ℝ)*X 0 0+(2778031303/5000000000 : ℝ)*X 0 1+(3177094283/10000000000 : ℝ)*X 0 2+(2098668941/5000000000 : ℝ)*X 1 0+(2778031303/5000000000 : ℝ)*X 1 1+(3177094283/10000000000 : ℝ)*X 1 2+(2098668941/5000000000 : ℝ)*X 2 0+(2778031303/5000000000 : ℝ)*X 2 1+(3177094283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90116196095752492889523/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3492933/6250000000000 : ℝ)*(base1) + (1096383611/100000000000000 : ℝ)*(base19) + (54945103/5000000000000 : ℝ)*(base23) + (61494817/50000000000000 : ℝ)*(upper3) + (133449413/100000000000000 : ℝ)*(upper5) + (607144725649459/100000000000000 : ℝ)*(major0) + (607144725649459/100000000000000 : ℝ)*(major1) + (607144725649459/100000000000000 : ℝ)*(major2) + (408010949391447/50000000000000 : ℝ)*(sp0) + (816024246819969/100000000000000 : ℝ)*(sp1) + (10200303053769/1250000000000 : ℝ)*(sp2) + (39826224723933/10000000000000 : ℝ)*(sp3) + (1750153807/50000000000000 : ℝ)*(sp4) + (330955083/20000000000000 : ℝ)*(sp7) + (199131978950837/50000000000000 : ℝ)*(f.failure) + (40801267160179/5000000000000 : ℝ)*(f.sum) + (239365897890159/100000000000000000000000000000 : ℝ)*base65 + (1505159617290159/200000000000000000000000000000 : ℝ)*base67 + (49929584509841/200000000000000000000000000000 : ℝ)*base70 + (176225622890159/200000000000000000000000000000 : ℝ)*base71 + (577126276390159/100000000000000000000000000000 : ℝ)*base73 + (384749872290159/200000000000000000000000000000 : ℝ)*base75 + (565704081290159/200000000000000000000000000000 : ℝ)*base77 + (621246227290159/200000000000000000000000000000 : ℝ)*base79 + (36889294790159/100000000000000000000000000000 : ℝ)*base81 + (16776177/5000000000000000000000 : ℝ)*base89 + (16776177/5000000000000000000000 : ℝ)*base91 + (16776177/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4415384361813941144727/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (289648107/100000000000000 : ℝ)*(base1) + (151981687/100000000000000 : ℝ)*(base19) + (69034511/20000000000000 : ℝ)*(base23) + (22986423/100000000000000 : ℝ)*(base59) + (748397/50000000000000 : ℝ)*(upper3) + (32040914176403/5000000000000 : ℝ)*(major0) + (32040914176403/5000000000000 : ℝ)*(major1) + (32040914176403/5000000000000 : ℝ)*(major2) + (35442501/4000000000000 : ℝ)*(sp1) + (119334517/12500000000000 : ℝ)*(sp3) + (17225685212013/2000000000000 : ℝ)*(sp4) + (861282932908331/100000000000000 : ℝ)*(sp5) + (215320906444997/25000000000000 : ℝ)*(sp6) + (26271955806721/6250000000000 : ℝ)*(sp7) + (420352537231779/100000000000000 : ℝ)*(f.failure) + (861283970952543/100000000000000 : ℝ)*(f.sum) + (35206232141697/5000000000000000000000000000 : ℝ)*base66 + (37506817831697/10000000000000000000000000000 : ℝ)*base68 + (74614513111697/10000000000000000000000000000 : ℝ)*base70 + (136735142771697/10000000000000000000000000000 : ℝ)*base72 + (11568284601697/5000000000000000000000000000 : ℝ)*base74 + (50219521891697/10000000000000000000000000000 : ℝ)*base76 + (45254577211697/10000000000000000000000000000 : ℝ)*base78 + (83464564971697/10000000000000000000000000000 : ℝ)*base80 + (24533507431697/5000000000000000000000000000 : ℝ)*base82 + (80503559/10000000000000000000000 : ℝ)*base89 + (80503559/10000000000000000000000 : ℝ)*base91 + (80503559/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1284_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (97/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13647/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1284_s1_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037143231/10000000000 : ℝ)*x 0 + (5669152683/10000000000 : ℝ)*x 1 + (201055469/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037143231/10000000000 : ℝ)^1061 ≤ (1228236047537/10000000000000 : ℝ)^805 := by
    have hnat : (2037143231 : ℕ)^1061*10000000000000^805 ≤ 1228236047537^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037143231 10000000000 1228236047537 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5669152683/10000000000 : ℝ)^1061 ≤ (591621403881/1250000000000 : ℝ)^805 := by
    have hnat : (5669152683 : ℕ)^1061*1250000000000^805 ≤ 591621403881^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669152683 10000000000 591621403881 1250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201055469/400000000 : ℝ)^1061 ≤ (4038792719511/10000000000000 : ℝ)^805 := by
    have hnat : (201055469 : ℕ)^1061*10000000000000^805 ≤ 4038792719511^805*400000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201055469 400000000 4038792719511 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037143231/10000000000 : ℝ), (5669152683/10000000000 : ℝ), (201055469/400000000 : ℝ)] ![(1228236047537/10000000000000 : ℝ), (591621403881/1250000000000 : ℝ), (4038792719511/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037143231/10000000000 : ℝ)|^1061 ≤ (1228236047537/10000000000000 : ℝ)^805
        have hw : |(-2037143231/10000000000 : ℝ)|=(2037143231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5669152683/10000000000 : ℝ)|^1061 ≤ (591621403881/1250000000000 : ℝ)^805
        have hw : |(5669152683/10000000000 : ℝ)|=(5669152683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201055469/400000000 : ℝ)|^1061 ≤ (4038792719511/10000000000000 : ℝ)^805
        have hw : |(201055469/400000000 : ℝ)|=(201055469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s1_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5411834993/10000000000 : ℝ)*x 0 + (-238190839/1000000000 : ℝ)*x 1 + (628298323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411834993/10000000000 : ℝ)^1061 ≤ (44518938418421/100000000000000 : ℝ)^805 := by
    have hnat : (5411834993 : ℕ)^1061*100000000000000^805 ≤ 44518938418421^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411834993 10000000000 44518938418421 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238190839/1000000000 : ℝ)^1061 ≤ (1509313585997/10000000000000 : ℝ)^805 := by
    have hnat : (238190839 : ℕ)^1061*10000000000000^805 ≤ 1509313585997^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238190839 1000000000 1509313585997 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628298323/1250000000 : ℝ)^1061 ≤ (20193962850927/50000000000000 : ℝ)^805 := by
    have hnat : (628298323 : ℕ)^1061*50000000000000^805 ≤ 20193962850927^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628298323 1250000000 20193962850927 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411834993/10000000000 : ℝ), (-238190839/1000000000 : ℝ), (628298323/1250000000 : ℝ)] ![(44518938418421/100000000000000 : ℝ), (1509313585997/10000000000000 : ℝ), (20193962850927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411834993/10000000000 : ℝ)|^1061 ≤ (44518938418421/100000000000000 : ℝ)^805
        have hw : |(5411834993/10000000000 : ℝ)|=(5411834993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238190839/1000000000 : ℝ)|^1061 ≤ (1509313585997/10000000000000 : ℝ)^805
        have hw : |(-238190839/1000000000 : ℝ)|=(238190839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628298323/1250000000 : ℝ)|^1061 ≤ (20193962850927/50000000000000 : ℝ)^805
        have hw : |(628298323/1250000000 : ℝ)|=(628298323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s1_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1082366957/2000000000 : ℝ)*x 0 + (5026386737/10000000000 : ℝ)*x 1 + (-1190954233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082366957/2000000000 : ℝ)^1061 ≤ (44518936163231/100000000000000 : ℝ)^805 := by
    have hnat : (1082366957 : ℕ)^1061*100000000000000^805 ≤ 44518936163231^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082366957 2000000000 44518936163231 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5026386737/10000000000 : ℝ)^1061 ≤ (10096981830549/25000000000000 : ℝ)^805 := by
    have hnat : (5026386737 : ℕ)^1061*25000000000000^805 ≤ 10096981830549^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026386737 10000000000 10096981830549 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190954233/5000000000 : ℝ)^1061 ≤ (7546568247349/50000000000000 : ℝ)^805 := by
    have hnat : (1190954233 : ℕ)^1061*50000000000000^805 ≤ 7546568247349^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190954233 5000000000 7546568247349 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082366957/2000000000 : ℝ), (5026386737/10000000000 : ℝ), (-1190954233/5000000000 : ℝ)] ![(44518936163231/100000000000000 : ℝ), (10096981830549/25000000000000 : ℝ), (7546568247349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082366957/2000000000 : ℝ)|^1061 ≤ (44518936163231/100000000000000 : ℝ)^805
        have hw : |(1082366957/2000000000 : ℝ)|=(1082366957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5026386737/10000000000 : ℝ)|^1061 ≤ (10096981830549/25000000000000 : ℝ)^805
        have hw : |(5026386737/10000000000 : ℝ)|=(5026386737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1190954233/5000000000 : ℝ)|^1061 ≤ (7546568247349/50000000000000 : ℝ)^805
        have hw : |(-1190954233/5000000000 : ℝ)|=(1190954233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s1_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (430254103/1000000000 : ℝ)*x 0 + (3691950539/10000000000 : ℝ)*x 1 + (2504474893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430254103/1000000000 : ℝ)^1061 ≤ (32903721990521/100000000000000 : ℝ)^805 := by
    have hnat : (430254103 : ℕ)^1061*100000000000000^805 ≤ 32903721990521^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430254103 1000000000 32903721990521 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3691950539/10000000000 : ℝ)^1061 ≤ (1680807138113/6250000000000 : ℝ)^805 := by
    have hnat : (3691950539 : ℕ)^1061*6250000000000^805 ≤ 1680807138113^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691950539 10000000000 1680807138113 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2504474893/5000000000 : ℝ)^1061 ≤ (40203363786547/100000000000000 : ℝ)^805 := by
    have hnat : (2504474893 : ℕ)^1061*100000000000000^805 ≤ 40203363786547^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504474893 5000000000 40203363786547 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430254103/1000000000 : ℝ), (3691950539/10000000000 : ℝ), (2504474893/5000000000 : ℝ)] ![(32903721990521/100000000000000 : ℝ), (1680807138113/6250000000000 : ℝ), (40203363786547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430254103/1000000000 : ℝ)|^1061 ≤ (32903721990521/100000000000000 : ℝ)^805
        have hw : |(430254103/1000000000 : ℝ)|=(430254103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3691950539/10000000000 : ℝ)|^1061 ≤ (1680807138113/6250000000000 : ℝ)^805
        have hw : |(3691950539/10000000000 : ℝ)|=(3691950539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2504474893/5000000000 : ℝ)|^1061 ≤ (40203363786547/100000000000000 : ℝ)^805
        have hw : |(2504474893/5000000000 : ℝ)|=(2504474893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s1_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-407559567/2000000000 : ℝ)*x 0 + (2517408879/5000000000 : ℝ)*x 1 + (5660561203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407559567/2000000000 : ℝ)^1061 ≤ (6143781299207/50000000000000 : ℝ)^805 := by
    have hnat : (407559567 : ℕ)^1061*50000000000000^805 ≤ 6143781299207^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407559567 2000000000 6143781299207 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517408879/5000000000 : ℝ)^1061 ≤ (40477239588709/100000000000000 : ℝ)^805 := by
    have hnat : (2517408879 : ℕ)^1061*100000000000000^805 ≤ 40477239588709^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517408879 5000000000 40477239588709 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660561203/10000000000 : ℝ)^1061 ≤ (47235197798311/100000000000000 : ℝ)^805 := by
    have hnat : (5660561203 : ℕ)^1061*100000000000000^805 ≤ 47235197798311^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660561203 10000000000 47235197798311 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407559567/2000000000 : ℝ), (2517408879/5000000000 : ℝ), (5660561203/10000000000 : ℝ)] ![(6143781299207/50000000000000 : ℝ), (40477239588709/100000000000000 : ℝ), (47235197798311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407559567/2000000000 : ℝ)|^1061 ≤ (6143781299207/50000000000000 : ℝ)^805
        have hw : |(-407559567/2000000000 : ℝ)|=(407559567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517408879/5000000000 : ℝ)|^1061 ≤ (40477239588709/100000000000000 : ℝ)^805
        have hw : |(2517408879/5000000000 : ℝ)|=(2517408879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660561203/10000000000 : ℝ)|^1061 ≤ (47235197798311/100000000000000 : ℝ)^805
        have hw : |(5660561203/10000000000 : ℝ)|=(5660561203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s1_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1049177217/2000000000 : ℝ)*x 0 + (-1747733629/10000000000 : ℝ)*x 1 + (5660561709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049177217/2000000000 : ℝ)^1061 ≤ (21364256107819/50000000000000 : ℝ)^805 := by
    have hnat : (1049177217 : ℕ)^1061*50000000000000^805 ≤ 21364256107819^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049177217 2000000000 21364256107819 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1747733629/10000000000 : ℝ)^1061 ≤ (1254535550729/12500000000000 : ℝ)^805 := by
    have hnat : (1747733629 : ℕ)^1061*12500000000000^805 ≤ 1254535550729^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747733629 10000000000 1254535550729 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660561709/10000000000 : ℝ)^1061 ≤ (47235203363453/100000000000000 : ℝ)^805 := by
    have hnat : (5660561709 : ℕ)^1061*100000000000000^805 ≤ 47235203363453^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660561709 10000000000 47235203363453 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049177217/2000000000 : ℝ), (-1747733629/10000000000 : ℝ), (5660561709/10000000000 : ℝ)] ![(21364256107819/50000000000000 : ℝ), (1254535550729/12500000000000 : ℝ), (47235203363453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049177217/2000000000 : ℝ)|^1061 ≤ (21364256107819/50000000000000 : ℝ)^805
        have hw : |(1049177217/2000000000 : ℝ)|=(1049177217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1747733629/10000000000 : ℝ)|^1061 ≤ (1254535550729/12500000000000 : ℝ)^805
        have hw : |(-1747733629/10000000000 : ℝ)|=(1747733629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660561709/10000000000 : ℝ)|^1061 ≤ (47235203363453/100000000000000 : ℝ)^805
        have hw : |(5660561709/10000000000 : ℝ)|=(5660561709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s1_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5245885993/10000000000 : ℝ)*x 0 + (5660561371/10000000000 : ℝ)*x 1 + (-436933563/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245885993/10000000000 : ℝ)^1061 ≤ (42728511227981/100000000000000 : ℝ)^805 := by
    have hnat : (5245885993 : ℕ)^1061*100000000000000^805 ≤ 42728511227981^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245885993 10000000000 42728511227981 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5660561371/10000000000 : ℝ)^1061 ≤ (23617599823013/50000000000000 : ℝ)^805 := by
    have hnat : (5660561371 : ℕ)^1061*50000000000000^805 ≤ 23617599823013^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660561371 10000000000 23617599823013 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436933563/2500000000 : ℝ)^1061 ≤ (156817017517/1562500000000 : ℝ)^805 := by
    have hnat : (436933563 : ℕ)^1061*1562500000000^805 ≤ 156817017517^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436933563 2500000000 156817017517 1562500000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245885993/10000000000 : ℝ), (5660561371/10000000000 : ℝ), (-436933563/2500000000 : ℝ)] ![(42728511227981/100000000000000 : ℝ), (23617599823013/50000000000000 : ℝ), (156817017517/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245885993/10000000000 : ℝ)|^1061 ≤ (42728511227981/100000000000000 : ℝ)^805
        have hw : |(5245885993/10000000000 : ℝ)|=(5245885993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5660561371/10000000000 : ℝ)|^1061 ≤ (23617599823013/50000000000000 : ℝ)^805
        have hw : |(5660561371/10000000000 : ℝ)|=(5660561371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436933563/2500000000 : ℝ)|^1061 ≤ (156817017517/1562500000000 : ℝ)^805
        have hw : |(-436933563/2500000000 : ℝ)|=(436933563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s1_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4303881747/10000000000 : ℝ)*x 0 + (4991675213/10000000000 : ℝ)*x 1 + (1854776793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303881747/10000000000 : ℝ)^1061 ≤ (2057327277079/6250000000000 : ℝ)^805 := by
    have hnat : (4303881747 : ℕ)^1061*6250000000000^805 ≤ 2057327277079^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303881747 10000000000 2057327277079 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4991675213/10000000000 : ℝ)^1061 ≤ (10005180081059/25000000000000 : ℝ)^805 := by
    have hnat : (4991675213 : ℕ)^1061*25000000000000^805 ≤ 10005180081059^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991675213 10000000000 10005180081059 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1854776793/5000000000 : ℝ)^1061 ≤ (6765510805971/25000000000000 : ℝ)^805 := by
    have hnat : (1854776793 : ℕ)^1061*25000000000000^805 ≤ 6765510805971^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854776793 5000000000 6765510805971 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303881747/10000000000 : ℝ), (4991675213/10000000000 : ℝ), (1854776793/5000000000 : ℝ)] ![(2057327277079/6250000000000 : ℝ), (10005180081059/25000000000000 : ℝ), (6765510805971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303881747/10000000000 : ℝ)|^1061 ≤ (2057327277079/6250000000000 : ℝ)^805
        have hw : |(4303881747/10000000000 : ℝ)|=(4303881747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4991675213/10000000000 : ℝ)|^1061 ≤ (10005180081059/25000000000000 : ℝ)^805
        have hw : |(4991675213/10000000000 : ℝ)|=(4991675213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1854776793/5000000000 : ℝ)|^1061 ≤ (6765510805971/25000000000000 : ℝ)^805
        have hw : |(1854776793/5000000000 : ℝ)|=(1854776793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13647/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (97/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (6329/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3983/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13647/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (97/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13647/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (97/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13647/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (97/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13647/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (97/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13647/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (97/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13647/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (97/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (97/10000 : ℝ) ^ (4243/1024 : ℝ) ≤ (455070394467/100000000000000000000 : ℝ) := by
    have hpowers : (97/10000 : ℝ)^4243 ≤ (455070394467/100000000000000000000 : ℝ)^1024 := by
      have hnat : (97 : ℕ)^4243*100000000000000000000^1024 ≤ 455070394467^1024*10000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97 10000 455070394467 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (97/10000 : ℝ)) (X := (455070394467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13647/50000 : ℝ) ^ (4243/1024 : ℝ) ≤ (460588987712428843/100000000000000000000 : ℝ) := by
    have hpowers : (13647/50000 : ℝ)^4243 ≤ (460588987712428843/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13647 : ℕ)^4243*100000000000000000000^1024 ≤ 460588987712428843^1024*50000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13647 50000 460588987712428843 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13647/50000 : ℝ)) (X := (460588987712428843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000455070394467/50000000000000000000 : ℝ) ≤ (5000000010982609/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50000000455070394467/50000000000000000000 : ℝ)^1024 ≤ (5000000010982609/5000000000000000 : ℝ)^4243 := by
      have hnat : (50000000455070394467 : ℕ)^1024*5000000000000000^4243 ≤ 5000000010982609^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000455070394467 50000000000000000000 5000000010982609 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000010982609/5000000000000000 : ℝ)) (X := (50000000455070394467/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10046058944278282331/10000000000000000000 : ℝ) ≤ (10011096435822017/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (10046058944278282331/10000000000000000000 : ℝ)^1024 ≤ (10011096435822017/10000000000000000 : ℝ)^4243 := by
      have hnat : (10046058944278282331 : ℕ)^1024*10000000000000000^4243 ≤ 10011096435822017^4243*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10046058944278282331 10000000000000000000 10011096435822017 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011096435822017/10000000000000000 : ℝ)) (X := (10046058944278282331/10000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50460588987712428843/50000000000000000000 : ℝ) ≤ (313193526552463/312500000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50460588987712428843/50000000000000000000 : ℝ)^1024 ≤ (313193526552463/312500000000000 : ℝ)^4243 := by
      have hnat : (50460588987712428843 : ℕ)^1024*312500000000000^4243 ≤ 313193526552463^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50460588987712428843 50000000000000000000 313193526552463 312500000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313193526552463/312500000000000 : ℝ)) (X := (50460588987712428843/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(455070394467/100000000000000000000 : ℝ) ≤ ((65804618383832552143/65810000000000000000 : ℝ)+2*(11096413856799/2632400000000000 : ℝ)*(97/10000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (65804618383832552143/65810000000000000000 : ℝ)+2*(11096413856799/2632400000000000 : ℝ)*(97/10000 : ℝ)=(5000000010982609/5000000000000000 : ℝ) by norm_num, show 1+2*(455070394467/100000000000000000000 : ℝ)=(50000000455070394467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(460588987712428843/100000000000000000000 : ℝ)+(455070394467/100000000000000000000 : ℝ) ≤ ((65804618383832552143/65810000000000000000 : ℝ)+(11096413856799/2632400000000000 : ℝ)*((13647/50000 : ℝ)+(97/10000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (65804618383832552143/65810000000000000000 : ℝ)+(11096413856799/2632400000000000 : ℝ)*((13647/50000 : ℝ)+(97/10000 : ℝ))=(10011096435822017/10000000000000000 : ℝ) by norm_num, show 1+(460588987712428843/100000000000000000000 : ℝ)+(455070394467/100000000000000000000 : ℝ)=(10046058944278282331/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(460588987712428843/100000000000000000000 : ℝ) ≤ ((65804618383832552143/65810000000000000000 : ℝ)+2*(11096413856799/2632400000000000 : ℝ)*(13647/50000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (65804618383832552143/65810000000000000000 : ℝ)+2*(11096413856799/2632400000000000 : ℝ)*(13647/50000 : ℝ)=(313193526552463/312500000000000 : ℝ) by norm_num, show 1+2*(460588987712428843/100000000000000000000 : ℝ)=(50460588987712428843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (65804618383832552143/65810000000000000000 : ℝ)*(X 1 0+X 2 0)+(11096413856799/2632400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (97/10000 : ℝ)) (hi := (13647/50000 : ℝ)) (c := (65804618383832552143/65810000000000000000 : ℝ)) (alpha := (11096413856799/2632400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (65804618383832552143/65810000000000000000 : ℝ)*(X 0 1+X 2 1)+(11096413856799/2632400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (97/10000 : ℝ)) (hi := (13647/50000 : ℝ)) (c := (65804618383832552143/65810000000000000000 : ℝ)) (alpha := (11096413856799/2632400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (65804618383832552143/65810000000000000000 : ℝ)*(X 0 2+X 1 2)+(11096413856799/2632400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (97/10000 : ℝ)) (hi := (13647/50000 : ℝ)) (c := (65804618383832552143/65810000000000000000 : ℝ)) (alpha := (11096413856799/2632400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2037143231/10000000000 : ℝ)*X 0 0+(5669152683/10000000000 : ℝ)*X 0 1+(201055469/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5411834993/10000000000 : ℝ)*X 1 0+(-238190839/1000000000 : ℝ)*X 1 1+(628298323/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1082366957/2000000000 : ℝ)*X 2 0+(5026386737/10000000000 : ℝ)*X 2 1+(-1190954233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430254103/1000000000 : ℝ)*X 0 0+(3691950539/10000000000 : ℝ)*X 0 1+(2504474893/5000000000 : ℝ)*X 0 2+(430254103/1000000000 : ℝ)*X 1 0+(3691950539/10000000000 : ℝ)*X 1 1+(2504474893/5000000000 : ℝ)*X 1 2+(430254103/1000000000 : ℝ)*X 2 0+(3691950539/10000000000 : ℝ)*X 2 1+(2504474893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-407559567/2000000000 : ℝ)*X 0 0+(2517408879/5000000000 : ℝ)*X 0 1+(5660561203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049177217/2000000000 : ℝ)*X 1 0+(-1747733629/10000000000 : ℝ)*X 1 1+(5660561709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245885993/10000000000 : ℝ)*X 2 0+(5660561371/10000000000 : ℝ)*X 2 1+(-436933563/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303881747/10000000000 : ℝ)*X 0 0+(4991675213/10000000000 : ℝ)*X 0 1+(1854776793/5000000000 : ℝ)*X 0 2+(4303881747/10000000000 : ℝ)*X 1 0+(4991675213/10000000000 : ℝ)*X 1 1+(1854776793/5000000000 : ℝ)*X 1 2+(4303881747/10000000000 : ℝ)*X 2 0+(4991675213/10000000000 : ℝ)*X 2 1+(1854776793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10297378446230559387351908559/3290500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8240029/25000000000000 : ℝ)*(base1) + (630379901/100000000000000 : ℝ)*(base19) + (570584527/100000000000000 : ℝ)*(base23) + (83101447/100000000000000 : ℝ)*(upper3) + (39084317/100000000000000 : ℝ)*(upper5) + (1157543937295029/100000000000000 : ℝ)*(major0) + (1157543937295029/100000000000000 : ℝ)*(major1) + (1157543937295029/100000000000000 : ℝ)*(major2) + (311155954064293/20000000000000 : ℝ)*(sp0) + (155578213330287/10000000000000 : ℝ)*(sp1) + (388945548274561/25000000000000 : ℝ)*(sp2) + (379651667688987/50000000000000 : ℝ)*(sp3) + (1513160711/50000000000000 : ℝ)*(sp4) + (409563743/25000000000000 : ℝ)*(sp7) + (379652503296531/50000000000000 : ℝ)*(f.failure) + (1555782763682771/100000000000000 : ℝ)*(f.sum) + (100168949961391/131620000000000000000000000000 : ℝ)*base65 + (3558240898611527853/6581000000000000000000000000000000 : ℝ)*base68 + (7242261362385527853/6581000000000000000000000000000000 : ℝ)*base70 + (13367369027487472147/6581000000000000000000000000000000 : ℝ)*base71 + (556452062817469/131620000000000000000000000000 : ℝ)*base74 + (22127732842705472147/6581000000000000000000000000000000 : ℝ)*base75 + (5020768134457472147/6581000000000000000000000000000000 : ℝ)*base77 + (45134990354971472147/6581000000000000000000000000000000 : ℝ)*base79 + (607474783520069/131620000000000000000000000000 : ℝ)*base82 + (17808951/5000000000000000000000 : ℝ)*base89 + (17808951/5000000000000000000000 : ℝ)*base91 + (17808951/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3468318106034862702333562017/411312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11766941/50000000000000 : ℝ)*(base1) + (1614194587/100000000000000 : ℝ)*(base19) + (309152773/20000000000000 : ℝ)*(base23) + (229701223/100000000000000 : ℝ)*(upper3) + (183990371/100000000000000 : ℝ)*(upper5) + (297256994858627/25000000000000 : ℝ)*(major0) + (297256994858627/25000000000000 : ℝ)*(major1) + (297256994858627/25000000000000 : ℝ)*(major2) + (2122090623/25000000000000 : ℝ)*(sp1) + (7211137819/100000000000000 : ℝ)*(sp2) + (159809835484801/10000000000000 : ℝ)*(sp4) + (1598088228757049/100000000000000 : ℝ)*(sp5) + (399522393603111/25000000000000 : ℝ)*(sp6) + (779957322943709/100000000000000 : ℝ)*(sp7) + (779957346477591/100000000000000 : ℝ)*(f.failure) + (99881145707133/6250000000000 : ℝ)*(f.sum) + (3995517566727/8226250000000000000000000000 : ℝ)*base65 + (1239531113949037339/1645250000000000000000000000000000 : ℝ)*base68 + (10170113264059212661/1645250000000000000000000000000000 : ℝ)*base69 + (7562097777549212661/1645250000000000000000000000000000 : ℝ)*base71 + (148669779923007/32905000000000000000000000000 : ℝ)*base74 + (7236487667894462661/1645250000000000000000000000000000 : ℝ)*base75 + (21038858639807712661/1645250000000000000000000000000000 : ℝ)*base77 + (4535550170799212661/1645250000000000000000000000000000 : ℝ)*base79 + (110325257377513/32905000000000000000000000000 : ℝ)*base81 + (26720789/10000000000000000000000 : ℝ)*base90 + (26720789/10000000000000000000000 : ℝ)*base92 + (26720789/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1284_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13647/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (97/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6329/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3983/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1284_s2_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082594419/10000000000 : ℝ)*x 0 + (2748366223/5000000000 : ℝ)*x 1 + (5169789683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082594419/10000000000 : ℝ)^1061 ≤ (505792658899/4000000000000 : ℝ)^805 := by
    have hnat : (2082594419 : ℕ)^1061*4000000000000^805 ≤ 505792658899^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082594419 10000000000 505792658899 4000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748366223/5000000000 : ℝ)^1061 ≤ (9088341289907/20000000000000 : ℝ)^805 := by
    have hnat : (2748366223 : ℕ)^1061*20000000000000^805 ≤ 9088341289907^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748366223 5000000000 9088341289907 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169789683/10000000000 : ℝ)^1061 ≤ (5239184632989/12500000000000 : ℝ)^805 := by
    have hnat : (5169789683 : ℕ)^1061*12500000000000^805 ≤ 5239184632989^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169789683 10000000000 5239184632989 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082594419/10000000000 : ℝ), (2748366223/5000000000 : ℝ), (5169789683/10000000000 : ℝ)] ![(505792658899/4000000000000 : ℝ), (9088341289907/20000000000000 : ℝ), (5239184632989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082594419/10000000000 : ℝ)|^1061 ≤ (505792658899/4000000000000 : ℝ)^805
        have hw : |(-2082594419/10000000000 : ℝ)|=(2082594419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748366223/5000000000 : ℝ)|^1061 ≤ (9088341289907/20000000000000 : ℝ)^805
        have hw : |(2748366223/5000000000 : ℝ)|=(2748366223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169789683/10000000000 : ℝ)|^1061 ≤ (5239184632989/12500000000000 : ℝ)^805
        have hw : |(5169789683/10000000000 : ℝ)|=(5169789683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s2_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342546577/2500000000 : ℝ)*x 0 + (-2252107247/10000000000 : ℝ)*x 1 + (516979027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342546577/2500000000 : ℝ)^1061 ≤ (22033963077921/50000000000000 : ℝ)^805 := by
    have hnat : (1342546577 : ℕ)^1061*50000000000000^805 ≤ 22033963077921^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342546577 2500000000 22033963077921 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252107247/10000000000 : ℝ)^1061 ≤ (1401859049077/10000000000000 : ℝ)^805 := by
    have hnat : (2252107247 : ℕ)^1061*10000000000000^805 ≤ 1401859049077^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252107247 10000000000 1401859049077 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516979027/1000000000 : ℝ)^1061 ≤ (41913483336379/100000000000000 : ℝ)^805 := by
    have hnat : (516979027 : ℕ)^1061*100000000000000^805 ≤ 41913483336379^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516979027 1000000000 41913483336379 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342546577/2500000000 : ℝ), (-2252107247/10000000000 : ℝ), (516979027/1000000000 : ℝ)] ![(22033963077921/50000000000000 : ℝ), (1401859049077/10000000000000 : ℝ), (41913483336379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342546577/2500000000 : ℝ)|^1061 ≤ (22033963077921/50000000000000 : ℝ)^805
        have hw : |(1342546577/2500000000 : ℝ)|=(1342546577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2252107247/10000000000 : ℝ)|^1061 ≤ (1401859049077/10000000000000 : ℝ)^805
        have hw : |(-2252107247/10000000000 : ℝ)|=(2252107247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516979027/1000000000 : ℝ)|^1061 ≤ (41913483336379/100000000000000 : ℝ)^805
        have hw : |(516979027/1000000000 : ℝ)|=(516979027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s2_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2685093323/5000000000 : ℝ)*x 0 + (5169789757/10000000000 : ℝ)*x 1 + (-225210747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685093323/5000000000 : ℝ)^1061 ≤ (44067929811533/100000000000000 : ℝ)^805 := by
    have hnat : (2685093323 : ℕ)^1061*100000000000000^805 ≤ 44067929811533^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685093323 5000000000 44067929811533 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169789757/10000000000 : ℝ)^1061 ≤ (41913477854649/100000000000000 : ℝ)^805 := by
    have hnat : (5169789757 : ℕ)^1061*100000000000000^805 ≤ 41913477854649^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169789757 10000000000 41913477854649 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225210747/1000000000 : ℝ)^1061 ≤ (140185923203/1000000000000 : ℝ)^805 := by
    have hnat : (225210747 : ℕ)^1061*1000000000000^805 ≤ 140185923203^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225210747 1000000000 140185923203 1000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685093323/5000000000 : ℝ), (5169789757/10000000000 : ℝ), (-225210747/1000000000 : ℝ)] ![(44067929811533/100000000000000 : ℝ), (41913477854649/100000000000000 : ℝ), (140185923203/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685093323/5000000000 : ℝ)|^1061 ≤ (44067929811533/100000000000000 : ℝ)^805
        have hw : |(2685093323/5000000000 : ℝ)|=(2685093323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169789757/10000000000 : ℝ)|^1061 ≤ (41913477854649/100000000000000 : ℝ)^805
        have hw : |(5169789757/10000000000 : ℝ)|=(5169789757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225210747/1000000000 : ℝ)|^1061 ≤ (140185923203/1000000000000 : ℝ)^805
        have hw : |(-225210747/1000000000 : ℝ)|=(225210747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s2_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (866821113/2000000000 : ℝ)*x 0 + (4011533677/10000000000 : ℝ)*x 1 + (292589479/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866821113/2000000000 : ℝ)^1061 ≤ (16611123808353/50000000000000 : ℝ)^805 := by
    have hnat : (866821113 : ℕ)^1061*50000000000000^805 ≤ 16611123808353^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866821113 2000000000 16611123808353 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011533677/10000000000 : ℝ)^1061 ≤ (937579832531/3125000000000 : ℝ)^805 := by
    have hnat : (4011533677 : ℕ)^1061*3125000000000^805 ≤ 937579832531^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011533677 10000000000 937579832531 3125000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292589479/625000000 : ℝ)^1061 ≤ (294201581821/800000000000 : ℝ)^805 := by
    have hnat : (292589479 : ℕ)^1061*800000000000^805 ≤ 294201581821^805*625000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292589479 625000000 294201581821 800000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866821113/2000000000 : ℝ), (4011533677/10000000000 : ℝ), (292589479/625000000 : ℝ)] ![(16611123808353/50000000000000 : ℝ), (937579832531/3125000000000 : ℝ), (294201581821/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866821113/2000000000 : ℝ)|^1061 ≤ (16611123808353/50000000000000 : ℝ)^805
        have hw : |(866821113/2000000000 : ℝ)|=(866821113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011533677/10000000000 : ℝ)|^1061 ≤ (937579832531/3125000000000 : ℝ)^805
        have hw : |(4011533677/10000000000 : ℝ)|=(4011533677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(292589479/625000000 : ℝ)|^1061 ≤ (294201581821/800000000000 : ℝ)^805
        have hw : |(292589479/625000000 : ℝ)|=(292589479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s2_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-416535937/2000000000 : ℝ)*x 0 + (517198063/1000000000 : ℝ)*x 1 + (5494520901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416535937/2000000000 : ℝ)^1061 ≤ (3161374705169/25000000000000 : ℝ)^805 := by
    have hnat : (416535937 : ℕ)^1061*25000000000000^805 ≤ 3161374705169^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416535937 2000000000 3161374705169 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517198063/1000000000 : ℝ)^1061 ≤ (10484222575107/25000000000000 : ℝ)^805 := by
    have hnat : (517198063 : ℕ)^1061*25000000000000^805 ≤ 10484222575107^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517198063 1000000000 10484222575107 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494520901/10000000000 : ℝ)^1061 ≤ (45417610861419/100000000000000 : ℝ)^805 := by
    have hnat : (5494520901 : ℕ)^1061*100000000000000^805 ≤ 45417610861419^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494520901 10000000000 45417610861419 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416535937/2000000000 : ℝ), (517198063/1000000000 : ℝ), (5494520901/10000000000 : ℝ)] ![(3161374705169/25000000000000 : ℝ), (10484222575107/25000000000000 : ℝ), (45417610861419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416535937/2000000000 : ℝ)|^1061 ≤ (3161374705169/25000000000000 : ℝ)^805
        have hw : |(-416535937/2000000000 : ℝ)|=(416535937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517198063/1000000000 : ℝ)|^1061 ≤ (10484222575107/25000000000000 : ℝ)^805
        have hw : |(517198063/1000000000 : ℝ)|=(517198063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494520901/10000000000 : ℝ)|^1061 ≤ (45417610861419/100000000000000 : ℝ)^805
        have hw : |(5494520901/10000000000 : ℝ)|=(5494520901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s2_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1057294027/2000000000 : ℝ)*x 0 + (-1927375949/10000000000 : ℝ)*x 1 + (5494521053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057294027/2000000000 : ℝ)^1061 ≤ (43164733425529/100000000000000 : ℝ)^805 := by
    have hnat : (1057294027 : ℕ)^1061*100000000000000^805 ≤ 43164733425529^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057294027 2000000000 43164733425529 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927375949/10000000000 : ℝ)^1061 ≤ (11417654033323/100000000000000 : ℝ)^805 := by
    have hnat : (1927375949 : ℕ)^1061*100000000000000^805 ≤ 11417654033323^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927375949 10000000000 11417654033323 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494521053/10000000000 : ℝ)^1061 ≤ (1419300391169/3125000000000 : ℝ)^805 := by
    have hnat : (5494521053 : ℕ)^1061*3125000000000^805 ≤ 1419300391169^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494521053 10000000000 1419300391169 3125000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057294027/2000000000 : ℝ), (-1927375949/10000000000 : ℝ), (5494521053/10000000000 : ℝ)] ![(43164733425529/100000000000000 : ℝ), (11417654033323/100000000000000 : ℝ), (1419300391169/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057294027/2000000000 : ℝ)|^1061 ≤ (43164733425529/100000000000000 : ℝ)^805
        have hw : |(1057294027/2000000000 : ℝ)|=(1057294027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927375949/10000000000 : ℝ)|^1061 ≤ (11417654033323/100000000000000 : ℝ)^805
        have hw : |(-1927375949/10000000000 : ℝ)|=(1927375949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494521053/10000000000 : ℝ)|^1061 ≤ (1419300391169/3125000000000 : ℝ)^805
        have hw : |(5494521053/10000000000 : ℝ)|=(5494521053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s2_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1321617579/2500000000 : ℝ)*x 0 + (549452091/1000000000 : ℝ)*x 1 + (-1927375901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321617579/2500000000 : ℝ)^1061 ≤ (8632947074681/20000000000000 : ℝ)^805 := by
    have hnat : (1321617579 : ℕ)^1061*20000000000000^805 ≤ 8632947074681^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321617579 2500000000 8632947074681 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549452091/1000000000 : ℝ)^1061 ≤ (45417610959471/100000000000000 : ℝ)^805 := by
    have hnat : (549452091 : ℕ)^1061*100000000000000^805 ≤ 45417610959471^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549452091 1000000000 45417610959471 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1927375901/10000000000 : ℝ)^1061 ≤ (11417653658547/100000000000000 : ℝ)^805 := by
    have hnat : (1927375901 : ℕ)^1061*100000000000000^805 ≤ 11417653658547^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927375901 10000000000 11417653658547 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321617579/2500000000 : ℝ), (549452091/1000000000 : ℝ), (-1927375901/10000000000 : ℝ)] ![(8632947074681/20000000000000 : ℝ), (45417610959471/100000000000000 : ℝ), (11417653658547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321617579/2500000000 : ℝ)|^1061 ≤ (8632947074681/20000000000000 : ℝ)^805
        have hw : |(1321617579/2500000000 : ℝ)|=(1321617579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549452091/1000000000 : ℝ)|^1061 ≤ (45417610959471/100000000000000 : ℝ)^805
        have hw : |(549452091/1000000000 : ℝ)|=(549452091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1927375901/10000000000 : ℝ)|^1061 ≤ (11417653658547/100000000000000 : ℝ)^805
        have hw : |(-1927375901/10000000000 : ℝ)|=(1927375901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s2_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4334280343/10000000000 : ℝ)*x 0 + (2338470647/5000000000 : ℝ)*x 1 + (4016069411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334280343/10000000000 : ℝ)^1061 ≤ (1661200670239/5000000000000 : ℝ)^805 := by
    have hnat : (4334280343 : ℕ)^1061*5000000000000^805 ≤ 1661200670239^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334280343 10000000000 1661200670239 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2338470647/5000000000 : ℝ)^1061 ≤ (18364356424423/50000000000000 : ℝ)^805 := by
    have hnat : (2338470647 : ℕ)^1061*50000000000000^805 ≤ 18364356424423^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338470647 5000000000 18364356424423 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016069411/10000000000 : ℝ)^1061 ≤ (15023636863871/50000000000000 : ℝ)^805 := by
    have hnat : (4016069411 : ℕ)^1061*50000000000000^805 ≤ 15023636863871^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016069411 10000000000 15023636863871 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334280343/10000000000 : ℝ), (2338470647/5000000000 : ℝ), (4016069411/10000000000 : ℝ)] ![(1661200670239/5000000000000 : ℝ), (18364356424423/50000000000000 : ℝ), (15023636863871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334280343/10000000000 : ℝ)|^1061 ≤ (1661200670239/5000000000000 : ℝ)^805
        have hw : |(4334280343/10000000000 : ℝ)|=(4334280343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2338470647/5000000000 : ℝ)|^1061 ≤ (18364356424423/50000000000000 : ℝ)^805
        have hw : |(2338470647/5000000000 : ℝ)|=(2338470647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016069411/10000000000 : ℝ)|^1061 ≤ (15023636863871/50000000000000 : ℝ)^805
        have hw : |(4016069411/10000000000 : ℝ)|=(4016069411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3983/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1889/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8177/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3983/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3983/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3983/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3983/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3983/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3983/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6329/100000 : ℝ) ^ (4243/1024 : ℝ) ≤ (269902200660989/25000000000000000000 : ℝ) := by
    have hpowers : (6329/100000 : ℝ)^4243 ≤ (269902200660989/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6329 : ℕ)^4243*25000000000000000000^1024 ≤ 269902200660989^1024*100000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6329 100000 269902200660989 25000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6329/100000 : ℝ)) (X := (269902200660989/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3983/20000 : ℝ) ^ (4243/1024 : ℝ) ≤ (12477146992078241/10000000000000000000 : ℝ) := by
    have hpowers : (3983/20000 : ℝ)^4243 ≤ (12477146992078241/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3983 : ℕ)^4243*10000000000000000000^1024 ≤ 12477146992078241^1024*20000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3983 20000 12477146992078241 10000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3983/20000 : ℝ)) (X := (12477146992078241/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500269902200660989/12500000000000000000 : ℝ) ≤ (10000052109844883/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (12500269902200660989/12500000000000000000 : ℝ)^1024 ≤ (10000052109844883/10000000000000000 : ℝ)^4243 := by
      have hnat : (12500269902200660989 : ℕ)^1024*10000000000000000^4243 ≤ 10000052109844883^4243*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500269902200660989 12500000000000000000 10000052109844883 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000052109844883/10000000000000000 : ℝ)) (X := (12500269902200660989/12500000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50062925539361713183/50000000000000000000 : ℝ) ≤ (10003035824364171/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50062925539361713183/50000000000000000000 : ℝ)^1024 ≤ (10003035824364171/10000000000000000 : ℝ)^4243 := by
      have hnat : (50062925539361713183 : ℕ)^1024*10000000000000000^4243 ≤ 10003035824364171^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50062925539361713183 50000000000000000000 10003035824364171 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003035824364171/10000000000000000 : ℝ)) (X := (50062925539361713183/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5012477146992078241/5000000000000000000 : ℝ) ≤ (10006019538883459/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (5012477146992078241/5000000000000000000 : ℝ)^1024 ≤ (10006019538883459/10000000000000000 : ℝ)^4243 := by
      have hnat : (5012477146992078241 : ℕ)^1024*10000000000000000^4243 ≤ 10006019538883459^4243*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5012477146992078241 5000000000000000000 10006019538883459 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006019538883459/10000000000000000 : ℝ)) (X := (5012477146992078241/5000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(269902200660989/25000000000000000000 : ℝ) ≤ ((67911470052983716467/67930000000000000000 : ℝ)+2*(372964314911/169825000000000 : ℝ)*(6329/100000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (67911470052983716467/67930000000000000000 : ℝ)+2*(372964314911/169825000000000 : ℝ)*(6329/100000 : ℝ)=(10000052109844883/10000000000000000 : ℝ) by norm_num, show 1+2*(269902200660989/25000000000000000000 : ℝ)=(12500269902200660989/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12477146992078241/10000000000000000000 : ℝ)+(269902200660989/25000000000000000000 : ℝ) ≤ ((67911470052983716467/67930000000000000000 : ℝ)+(372964314911/169825000000000 : ℝ)*((3983/20000 : ℝ)+(6329/100000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (67911470052983716467/67930000000000000000 : ℝ)+(372964314911/169825000000000 : ℝ)*((3983/20000 : ℝ)+(6329/100000 : ℝ))=(10003035824364171/10000000000000000 : ℝ) by norm_num, show 1+(12477146992078241/10000000000000000000 : ℝ)+(269902200660989/25000000000000000000 : ℝ)=(50062925539361713183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12477146992078241/10000000000000000000 : ℝ) ≤ ((67911470052983716467/67930000000000000000 : ℝ)+2*(372964314911/169825000000000 : ℝ)*(3983/20000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (67911470052983716467/67930000000000000000 : ℝ)+2*(372964314911/169825000000000 : ℝ)*(3983/20000 : ℝ)=(10006019538883459/10000000000000000 : ℝ) by norm_num, show 1+2*(12477146992078241/10000000000000000000 : ℝ)=(5012477146992078241/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67911470052983716467/67930000000000000000 : ℝ)*(X 1 0+X 2 0)+(372964314911/169825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (6329/100000 : ℝ)) (hi := (3983/20000 : ℝ)) (c := (67911470052983716467/67930000000000000000 : ℝ)) (alpha := (372964314911/169825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67911470052983716467/67930000000000000000 : ℝ)*(X 0 1+X 2 1)+(372964314911/169825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (6329/100000 : ℝ)) (hi := (3983/20000 : ℝ)) (c := (67911470052983716467/67930000000000000000 : ℝ)) (alpha := (372964314911/169825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67911470052983716467/67930000000000000000 : ℝ)*(X 0 2+X 1 2)+(372964314911/169825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (6329/100000 : ℝ)) (hi := (3983/20000 : ℝ)) (c := (67911470052983716467/67930000000000000000 : ℝ)) (alpha := (372964314911/169825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2082594419/10000000000 : ℝ)*X 0 0+(2748366223/5000000000 : ℝ)*X 0 1+(5169789683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342546577/2500000000 : ℝ)*X 1 0+(-2252107247/10000000000 : ℝ)*X 1 1+(516979027/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685093323/5000000000 : ℝ)*X 2 0+(5169789757/10000000000 : ℝ)*X 2 1+(-225210747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866821113/2000000000 : ℝ)*X 0 0+(4011533677/10000000000 : ℝ)*X 0 1+(292589479/625000000 : ℝ)*X 0 2+(866821113/2000000000 : ℝ)*X 1 0+(4011533677/10000000000 : ℝ)*X 1 1+(292589479/625000000 : ℝ)*X 1 2+(866821113/2000000000 : ℝ)*X 2 0+(4011533677/10000000000 : ℝ)*X 2 1+(292589479/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-416535937/2000000000 : ℝ)*X 0 0+(517198063/1000000000 : ℝ)*X 0 1+(5494520901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057294027/2000000000 : ℝ)*X 1 0+(-1927375949/10000000000 : ℝ)*X 1 1+(5494521053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321617579/2500000000 : ℝ)*X 2 0+(549452091/1000000000 : ℝ)*X 2 1+(-1927375901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334280343/10000000000 : ℝ)*X 0 0+(2338470647/5000000000 : ℝ)*X 0 1+(4016069411/10000000000 : ℝ)*X 0 2+(4334280343/10000000000 : ℝ)*X 1 0+(2338470647/5000000000 : ℝ)*X 1 1+(4016069411/10000000000 : ℝ)*X 1 2+(4334280343/10000000000 : ℝ)*X 2 0+(2338470647/5000000000 : ℝ)*X 2 1+(4016069411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3122465942497008238911333297/424562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1170001649/50000000000000 : ℝ)*(base19) + (2398344529/100000000000000 : ℝ)*(base23) + (1801331/2500000000000 : ℝ)*(lower2) + (282471801/50000000000000 : ℝ)*(upper3) + (17056577/5000000000000 : ℝ)*(upper5) + (568936370356497/25000000000000 : ℝ)*(major0) + (568936370356497/25000000000000 : ℝ)*(major1) + (568936370356497/25000000000000 : ℝ)*(major2) + (764666221775051/25000000000000 : ℝ)*(sp0) + (1529342742603507/50000000000000 : ℝ)*(sp1) + (382335678358223/12500000000000 : ℝ)*(sp2) + (46649448372581/3125000000000 : ℝ)*(sp3) + (22938110109/100000000000000 : ℝ)*(sp4) + (4108913483/20000000000000 : ℝ)*(sp7) + (1492802892490007/100000000000000 : ℝ)*(f.failure) + (3058687825210313/100000000000000 : ℝ)*(f.sum) + (44081469936553/8491250000000000000000000000 : ℝ)*base65 + (10110275061599863901/1698250000000000000000000000000000 : ℝ)*base68 + (6627513719744363901/1698250000000000000000000000000000 : ℝ)*base70 + (2046879940194113901/1698250000000000000000000000000000 : ℝ)*base72 + (6522191630129/4245625000000000000000000000 : ℝ)*base73 + (6709403546873886099/1698250000000000000000000000000000 : ℝ)*base75 + (1610015575328113901/1698250000000000000000000000000000 : ℝ)*base78 + (13509775587440363901/1698250000000000000000000000000000 : ℝ)*base80 + (6648279032673/33965000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (31424747/10000000000000000000000 : ℝ)*base89 + (31424747/10000000000000000000000 : ℝ)*base91 + (31424747/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10612897027332289658333205123/3396500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146116771/25000000000000 : ℝ)*(base19) + (424123073/50000000000000 : ℝ)*(base23) + (61838867/50000000000000 : ℝ)*(upper3) + (53657401/100000000000000 : ℝ)*(lower4) + (7109517/100000000000000 : ℝ)*(upper5) + (2306769698630359/100000000000000 : ℝ)*(major0) + (2306769698630359/100000000000000 : ℝ)*(major1) + (2306769698630359/100000000000000 : ℝ)*(major2) + (1437949167/25000000000000 : ℝ)*(sp1) + (4648046979/50000000000000 : ℝ)*(sp2) + (3100385688482721/100000000000000 : ℝ)*(sp4) + (3100379352218969/100000000000000 : ℝ)*(sp5) + (3100375544142617/100000000000000 : ℝ)*(sp6) + (378288401155691/25000000000000 : ℝ)*(sp7) + (378288401155691/25000000000000 : ℝ)*(f.failure) + (3100385688482721/100000000000000 : ℝ)*(f.sum) + (162187296064959/33965000000000000000000000000 : ℝ)*base66 + (38268971595836021653/6793000000000000000000000000000000 : ℝ)*base67 + (51113089188089021653/6793000000000000000000000000000000 : ℝ)*base69 + (8764053202191021653/6793000000000000000000000000000000 : ℝ)*base71 + (23042264847439/33965000000000000000000000000 : ℝ)*base74 + (111099198096961021653/6793000000000000000000000000000000 : ℝ)*base75 + (28047143396358021653/6793000000000000000000000000000000 : ℝ)*base77 + (9704980971158021653/6793000000000000000000000000000000 : ℝ)*base79 + (23366487536859/33965000000000000000000000000 : ℝ)*base82 + (300689/2500000000000000000000 : ℝ)*base90 + (300689/2500000000000000000000 : ℝ)*base92 + (300689/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1284_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3983/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1889/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1284_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1889/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1284_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1284_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1284_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1889/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
