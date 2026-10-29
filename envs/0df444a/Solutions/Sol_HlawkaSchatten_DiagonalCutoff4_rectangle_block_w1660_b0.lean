-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1660_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:20.862728+00:00
-- url     : https://prove2.me/submissions/19a4c770-6cda-49a0-a634-7bf92522997f

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
theorem support_rectangle_w1660_s0_0 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-295053889/2000000000 : ℝ)*x 0 + (5773044703/10000000000 : ℝ)*x 1 + (1232067393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (295053889/2000000000 : ℝ)^4959 ≤ (4482887182043/50000000000000 : ℝ)^3935 := by
    have hnat : (295053889 : ℕ)^4959*50000000000000^3935 ≤ 4482887182043^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295053889 2000000000 4482887182043 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5773044703/10000000000 : ℝ)^4959 ≤ (50039807356209/100000000000000 : ℝ)^3935 := by
    have hnat : (5773044703 : ℕ)^4959*100000000000000^3935 ≤ 50039807356209^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5773044703 10000000000 50039807356209 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1232067393/2500000000 : ℝ)^4959 ≤ (40994418258127/100000000000000 : ℝ)^3935 := by
    have hnat : (1232067393 : ℕ)^4959*100000000000000^3935 ≤ 40994418258127^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232067393 2500000000 40994418258127 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-295053889/2000000000 : ℝ), (5773044703/10000000000 : ℝ), (1232067393/2500000000 : ℝ)] ![(4482887182043/50000000000000 : ℝ), (50039807356209/100000000000000 : ℝ), (40994418258127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-295053889/2000000000 : ℝ)|^4959 ≤ (4482887182043/50000000000000 : ℝ)^3935
        have hw : |(-295053889/2000000000 : ℝ)|=(295053889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5773044703/10000000000 : ℝ)|^4959 ≤ (50039807356209/100000000000000 : ℝ)^3935
        have hw : |(5773044703/10000000000 : ℝ)|=(5773044703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1232067393/2500000000 : ℝ)|^4959 ≤ (40994418258127/100000000000000 : ℝ)^3935
        have hw : |(1232067393/2500000000 : ℝ)|=(1232067393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s0_1 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086718417/2000000000 : ℝ)*x 0 + (-1938053573/10000000000 : ℝ)*x 1 + (492827023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086718417/2000000000 : ℝ)^4959 ≤ (23180301165367/50000000000000 : ℝ)^3935 := by
    have hnat : (1086718417 : ℕ)^4959*50000000000000^3935 ≤ 23180301165367^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086718417 2000000000 23180301165367 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938053573/10000000000 : ℝ)^4959 ≤ (3161243122923/25000000000000 : ℝ)^3935 := by
    have hnat : (1938053573 : ℕ)^4959*25000000000000^3935 ≤ 3161243122923^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938053573 10000000000 3161243122923 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492827023/1000000000 : ℝ)^4959 ≤ (40994425155847/100000000000000 : ℝ)^3935 := by
    have hnat : (492827023 : ℕ)^4959*100000000000000^3935 ≤ 40994425155847^3935*1000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492827023 1000000000 40994425155847 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086718417/2000000000 : ℝ), (-1938053573/10000000000 : ℝ), (492827023/1000000000 : ℝ)] ![(23180301165367/50000000000000 : ℝ), (3161243122923/25000000000000 : ℝ), (40994425155847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086718417/2000000000 : ℝ)|^4959 ≤ (23180301165367/50000000000000 : ℝ)^3935
        have hw : |(1086718417/2000000000 : ℝ)|=(1086718417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1938053573/10000000000 : ℝ)|^4959 ≤ (3161243122923/25000000000000 : ℝ)^3935
        have hw : |(-1938053573/10000000000 : ℝ)|=(1938053573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(492827023/1000000000 : ℝ)|^4959 ≤ (40994425155847/100000000000000 : ℝ)^3935
        have hw : |(492827023/1000000000 : ℝ)|=(492827023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s0_2 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5433593457/10000000000 : ℝ)*x 0 + (1232067321/2500000000 : ℝ)*x 1 + (-387610597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5433593457/10000000000 : ℝ)^4959 ≤ (46360617083231/100000000000000 : ℝ)^3935 := by
    have hnat : (5433593457 : ℕ)^4959*100000000000000^3935 ≤ 46360617083231^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433593457 10000000000 46360617083231 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232067321/2500000000 : ℝ)^4959 ≤ (8198883047813/20000000000000 : ℝ)^3935 := by
    have hnat : (1232067321 : ℕ)^4959*20000000000000^3935 ≤ 8198883047813^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232067321 2500000000 8198883047813 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387610597/2000000000 : ℝ)^4959 ≤ (12644967656889/100000000000000 : ℝ)^3935 := by
    have hnat : (387610597 : ℕ)^4959*100000000000000^3935 ≤ 12644967656889^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387610597 2000000000 12644967656889 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5433593457/10000000000 : ℝ), (1232067321/2500000000 : ℝ), (-387610597/2000000000 : ℝ)] ![(46360617083231/100000000000000 : ℝ), (8198883047813/20000000000000 : ℝ), (12644967656889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5433593457/10000000000 : ℝ)|^4959 ≤ (46360617083231/100000000000000 : ℝ)^3935
        have hw : |(5433593457/10000000000 : ℝ)|=(5433593457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1232067321/2500000000 : ℝ)|^4959 ≤ (8198883047813/20000000000000 : ℝ)^3935
        have hw : |(1232067321/2500000000 : ℝ)|=(1232067321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387610597/2000000000 : ℝ)|^4959 ≤ (12644967656889/100000000000000 : ℝ)^3935
        have hw : |(-387610597/2000000000 : ℝ)|=(387610597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s0_3 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4085959539/10000000000 : ℝ)*x 0 + (771297839/2500000000 : ℝ)*x 1 + (1324598961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4085959539/10000000000 : ℝ)^4959 ≤ (32369919120343/100000000000000 : ℝ)^3935 := by
    have hnat : (4085959539 : ℕ)^4959*100000000000000^3935 ≤ 32369919120343^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085959539 10000000000 32369919120343 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771297839/2500000000 : ℝ)^4959 ≤ (5679611794911/25000000000000 : ℝ)^3935 := by
    have hnat : (771297839 : ℕ)^4959*25000000000000^3935 ≤ 5679611794911^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771297839 2500000000 5679611794911 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324598961/2500000000 : ℝ)^4959 ≤ (898232673553/2000000000000 : ℝ)^3935 := by
    have hnat : (1324598961 : ℕ)^4959*2000000000000^3935 ≤ 898232673553^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324598961 2500000000 898232673553 2000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4085959539/10000000000 : ℝ), (771297839/2500000000 : ℝ), (1324598961/2500000000 : ℝ)] ![(32369919120343/100000000000000 : ℝ), (5679611794911/25000000000000 : ℝ), (898232673553/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4085959539/10000000000 : ℝ)|^4959 ≤ (32369919120343/100000000000000 : ℝ)^3935
        have hw : |(4085959539/10000000000 : ℝ)|=(4085959539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771297839/2500000000 : ℝ)|^4959 ≤ (5679611794911/25000000000000 : ℝ)^3935
        have hw : |(771297839/2500000000 : ℝ)|=(771297839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1324598961/2500000000 : ℝ)|^4959 ≤ (898232673553/2000000000000 : ℝ)^3935
        have hw : |(1324598961/2500000000 : ℝ)|=(1324598961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s0_4 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1477455327/10000000000 : ℝ)*x 0 + (154659713/312500000 : ℝ)*x 1 + (359468107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1477455327/10000000000 : ℝ)^4959 ≤ (8982519020133/100000000000000 : ℝ)^3935 := by
    have hnat : (1477455327 : ℕ)^4959*100000000000000^3935 ≤ 8982519020133^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477455327 10000000000 8982519020133 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154659713/312500000 : ℝ)^4959 ≤ (41213014119529/100000000000000 : ℝ)^3935 := by
    have hnat : (154659713 : ℕ)^4959*100000000000000^3935 ≤ 41213014119529^3935*312500000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154659713 312500000 41213014119529 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359468107/625000000 : ℝ)^4959 ≤ (24902233421893/50000000000000 : ℝ)^3935 := by
    have hnat : (359468107 : ℕ)^4959*50000000000000^3935 ≤ 24902233421893^3935*625000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359468107 625000000 24902233421893 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1477455327/10000000000 : ℝ), (154659713/312500000 : ℝ), (359468107/625000000 : ℝ)] ![(8982519020133/100000000000000 : ℝ), (41213014119529/100000000000000 : ℝ), (24902233421893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1477455327/10000000000 : ℝ)|^4959 ≤ (8982519020133/100000000000000 : ℝ)^3935
        have hw : |(-1477455327/10000000000 : ℝ)|=(1477455327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154659713/312500000 : ℝ)|^4959 ≤ (41213014119529/100000000000000 : ℝ)^3935
        have hw : |(154659713/312500000 : ℝ)|=(154659713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(359468107/625000000 : ℝ)|^4959 ≤ (24902233421893/50000000000000 : ℝ)^3935
        have hw : |(359468107/625000000 : ℝ)|=(359468107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s0_5 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203152827/10000000000 : ℝ)*x 0 + (-1114835069/10000000000 : ℝ)*x 1 + (5751488021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203152827/10000000000 : ℝ)^4959 ≤ (685884557593/1562500000000 : ℝ)^3935 := by
    have hnat : (5203152827 : ℕ)^4959*1562500000000^3935 ≤ 685884557593^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203152827 10000000000 685884557593 1562500000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114835069/10000000000 : ℝ)^4959 ≤ (251957595959/4000000000000 : ℝ)^3935 := by
    have hnat : (1114835069 : ℕ)^4959*4000000000000^3935 ≤ 251957595959^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114835069 10000000000 251957595959 4000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5751488021/10000000000 : ℝ)^4959 ≤ (24902224195097/50000000000000 : ℝ)^3935 := by
    have hnat : (5751488021 : ℕ)^4959*50000000000000^3935 ≤ 24902224195097^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5751488021 10000000000 24902224195097 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203152827/10000000000 : ℝ), (-1114835069/10000000000 : ℝ), (5751488021/10000000000 : ℝ)] ![(685884557593/1562500000000 : ℝ), (251957595959/4000000000000 : ℝ), (24902224195097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203152827/10000000000 : ℝ)|^4959 ≤ (685884557593/1562500000000 : ℝ)^3935
        have hw : |(5203152827/10000000000 : ℝ)|=(5203152827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114835069/10000000000 : ℝ)|^4959 ≤ (251957595959/4000000000000 : ℝ)^3935
        have hw : |(-1114835069/10000000000 : ℝ)|=(1114835069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5751488021/10000000000 : ℝ)|^4959 ≤ (24902224195097/50000000000000 : ℝ)^3935
        have hw : |(5751488021/10000000000 : ℝ)|=(5751488021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s0_6 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203151963/10000000000 : ℝ)*x 0 + (5751488477/10000000000 : ℝ)*x 1 + (-557417831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203151963/10000000000 : ℝ)^4959 ≤ (43896602499929/100000000000000 : ℝ)^3935 := by
    have hnat : (5203151963 : ℕ)^4959*100000000000000^3935 ≤ 43896602499929^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203151963 10000000000 43896602499929 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5751488477/10000000000 : ℝ)^4959 ≤ (12451113341611/25000000000000 : ℝ)^3935 := by
    have hnat : (5751488477 : ℕ)^4959*25000000000000^3935 ≤ 12451113341611^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5751488477 10000000000 12451113341611 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557417831/5000000000 : ℝ)^4959 ≤ (629894412139/10000000000000 : ℝ)^3935 := by
    have hnat : (557417831 : ℕ)^4959*10000000000000^3935 ≤ 629894412139^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557417831 5000000000 629894412139 10000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203151963/10000000000 : ℝ), (5751488477/10000000000 : ℝ), (-557417831/5000000000 : ℝ)] ![(43896602499929/100000000000000 : ℝ), (12451113341611/25000000000000 : ℝ), (629894412139/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203151963/10000000000 : ℝ)|^4959 ≤ (43896602499929/100000000000000 : ℝ)^3935
        have hw : |(5203151963/10000000000 : ℝ)|=(5203151963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5751488477/10000000000 : ℝ)|^4959 ≤ (12451113341611/25000000000000 : ℝ)^3935
        have hw : |(5751488477/10000000000 : ℝ)|=(5751488477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-557417831/5000000000 : ℝ)|^4959 ≤ (629894412139/10000000000000 : ℝ)^3935
        have hw : |(-557417831/5000000000 : ℝ)|=(557417831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s0_7 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511460527/1250000000 : ℝ)*x 0 + (1048758861/2000000000 : ℝ)*x 1 + (314166549/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511460527/1250000000 : ℝ)^4959 ≤ (32427083704479/100000000000000 : ℝ)^3935 := by
    have hnat : (511460527 : ℕ)^4959*100000000000000^3935 ≤ 32427083704479^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511460527 1250000000 32427083704479 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048758861/2000000000 : ℝ)^4959 ≤ (44329149012013/100000000000000 : ℝ)^3935 := by
    have hnat : (1048758861 : ℕ)^4959*100000000000000^3935 ≤ 44329149012013^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048758861 2000000000 44329149012013 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314166549/1000000000 : ℝ)^4959 ≤ (2905470908857/12500000000000 : ℝ)^3935 := by
    have hnat : (314166549 : ℕ)^4959*12500000000000^3935 ≤ 2905470908857^3935*1000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314166549 1000000000 2905470908857 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511460527/1250000000 : ℝ), (1048758861/2000000000 : ℝ), (314166549/1000000000 : ℝ)] ![(32427083704479/100000000000000 : ℝ), (44329149012013/100000000000000 : ℝ), (2905470908857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511460527/1250000000 : ℝ)|^4959 ≤ (32427083704479/100000000000000 : ℝ)^3935
        have hw : |(511460527/1250000000 : ℝ)|=(511460527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048758861/2000000000 : ℝ)|^4959 ≤ (44329149012013/100000000000000 : ℝ)^3935
        have hw : |(1048758861/2000000000 : ℝ)|=(1048758861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314166549/1000000000 : ℝ)|^4959 ≤ (2905470908857/12500000000000 : ℝ)^3935
        have hw : |(314166549/1000000000 : ℝ)|=(314166549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1660_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1007/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11573/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4955/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4955 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4955*1^1024 ≤ 0^1024*1^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4955/1024 : ℝ) ≤ (593459592147288871/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4955 ≤ (593459592147288871/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4955*50000000000000000000^1024 ≤ 593459592147288871^1024*5^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 593459592147288871 50000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (593459592147288871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4955 := by
      have hnat : (1 : ℕ)^1024*1^4955 ≤ 1^4955*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50593459592147288871/50000000000000000000 : ℝ) ≤ (10024414191694977/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (50593459592147288871/50000000000000000000 : ℝ)^1024 ≤ (10024414191694977/10000000000000000 : ℝ)^4955 := by
      have hnat : (50593459592147288871 : ℕ)^1024*10000000000000000^4955 ≤ 10024414191694977^4955*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50593459592147288871 50000000000000000000 10024414191694977 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024414191694977/10000000000000000 : ℝ)) (X := (50593459592147288871/50000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25593459592147288871/25000000000000000000 : ℝ) ≤ (5024414191694977/5000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (25593459592147288871/25000000000000000000 : ℝ)^1024 ≤ (5024414191694977/5000000000000000 : ℝ)^4955 := by
      have hnat : (25593459592147288871 : ℕ)^1024*5000000000000000^4955 ≤ 5024414191694977^4955*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25593459592147288871 25000000000000000000 5024414191694977 5000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024414191694977/5000000000000000 : ℝ)) (X := (25593459592147288871/25000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(24414191694977/4000000000000000 : ℝ)*(0 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24414191694977/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(593459592147288871/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(24414191694977/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4955/1024 : ℝ) := by
    rw [show (1 : ℝ)+(24414191694977/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10024414191694977/10000000000000000 : ℝ) by norm_num, show 1+(593459592147288871/50000000000000000000 : ℝ)+(0 : ℝ)=(50593459592147288871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(593459592147288871/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(24414191694977/4000000000000000 : ℝ)*(2/5 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24414191694977/4000000000000000 : ℝ)*(2/5 : ℝ)=(5024414191694977/5000000000000000 : ℝ) by norm_num, show 1+2*(593459592147288871/50000000000000000000 : ℝ)=(25593459592147288871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(24414191694977/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24414191694977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(24414191694977/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24414191694977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(24414191694977/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24414191694977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-295053889/2000000000 : ℝ)*X 0 0+(5773044703/10000000000 : ℝ)*X 0 1+(1232067393/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1086718417/2000000000 : ℝ)*X 1 0+(-1938053573/10000000000 : ℝ)*X 1 1+(492827023/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5433593457/10000000000 : ℝ)*X 2 0+(1232067321/2500000000 : ℝ)*X 2 1+(-387610597/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4085959539/10000000000 : ℝ)*X 0 0+(771297839/2500000000 : ℝ)*X 0 1+(1324598961/2500000000 : ℝ)*X 0 2+(4085959539/10000000000 : ℝ)*X 1 0+(771297839/2500000000 : ℝ)*X 1 1+(1324598961/2500000000 : ℝ)*X 1 2+(4085959539/10000000000 : ℝ)*X 2 0+(771297839/2500000000 : ℝ)*X 2 1+(1324598961/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1477455327/10000000000 : ℝ)*X 0 0+(154659713/312500000 : ℝ)*X 0 1+(359468107/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5203152827/10000000000 : ℝ)*X 1 0+(-1114835069/10000000000 : ℝ)*X 1 1+(5751488021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5203151963/10000000000 : ℝ)*X 2 0+(5751488477/10000000000 : ℝ)*X 2 1+(-557417831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((511460527/1250000000 : ℝ)*X 0 0+(1048758861/2000000000 : ℝ)*X 0 1+(314166549/1000000000 : ℝ)*X 0 2+(511460527/1250000000 : ℝ)*X 1 0+(1048758861/2000000000 : ℝ)*X 1 1+(314166549/1000000000 : ℝ)*X 1 2+(511460527/1250000000 : ℝ)*X 2 0+(1048758861/2000000000 : ℝ)*X 2 1+(314166549/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4068488689907228379/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62399327/50000000000000 : ℝ)*(base1) + (345297577/50000000000000 : ℝ)*(base19) + (190533381/20000000000000 : ℝ)*(base23) + (18414867/50000000000000 : ℝ)*(base24) + (19476177/12500000000000 : ℝ)*(upper5) + (817795146742089/100000000000000 : ℝ)*(major0) + (817795146742089/100000000000000 : ℝ)*(major1) + (817795146742089/100000000000000 : ℝ)*(major2) + (295937346694259/25000000000000 : ℝ)*(sp0) + (11837530250893/1000000000000 : ℝ)*(sp1) + (236750545237563/20000000000000 : ℝ)*(sp2) + (56479379939793/12500000000000 : ℝ)*(sp3) + (556713259/12500000000000 : ℝ)*(sp4) + (1277866431/100000000000000 : ℝ)*(sp7) + (451836442183429/100000000000000 : ℝ)*(f.failure) + (591876857842227/50000000000000 : ℝ)*(f.sum) + (54542813813047/200000000000000000000000000000 : ℝ)*base66 + (1253232384186953/400000000000000000000000000000 : ℝ)*base67 + (1497960977013047/400000000000000000000000000000 : ℝ)*base70 + (1757488429013047/400000000000000000000000000000 : ℝ)*base72 + (1159954171986953/200000000000000000000000000000 : ℝ)*base73 + (1991744634613047/400000000000000000000000000000 : ℝ)*base76 + (653062811013047/400000000000000000000000000000 : ℝ)*base78 + (78168624186953/400000000000000000000000000000 : ℝ)*base79 + (369852225586953/200000000000000000000000000000 : ℝ)*base81 + (54726733/10000000000000000000000 : ℝ)*base90 + (54726733/10000000000000000000000 : ℝ)*base92 + (54726733/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (921925042482567644664963/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252940453/50000000000000 : ℝ)*(base19) + (313720823/100000000000000 : ℝ)*(base23) + (22634473/100000000000000 : ℝ)*(upper2) + (37430979/100000000000000 : ℝ)*(upper3) + (861001971971691/100000000000000 : ℝ)*(major0) + (861001971971691/100000000000000 : ℝ)*(major1) + (861001971971691/100000000000000 : ℝ)*(major2) + (32881989/3125000000000 : ℝ)*(sp0) + (648258093/100000000000000 : ℝ)*(sp1) + (58067199/50000000000000 : ℝ)*(sp3) + (155786785082779/12500000000000 : ℝ)*(sp4) + (1246294178746881/100000000000000 : ℝ)*(sp5) + (1246295019165057/100000000000000 : ℝ)*(sp6) + (7432942832327/1562500000000 : ℝ)*(sp7) + (237854228701663/50000000000000 : ℝ)*(f.failure) + (31157383322147/2500000000000 : ℝ)*(f.sum) + (15061598303893/200000000000000000000000000000 : ℝ)*base66 + (695999317296107/400000000000000000000000000000 : ℝ)*base67 + (2276951037903893/400000000000000000000000000000 : ℝ)*base70 + (232873833903893/400000000000000000000000000000 : ℝ)*base72 + (159004579103893/200000000000000000000000000000 : ℝ)*base74 + (148506258303893/400000000000000000000000000000 : ℝ)*base76 + (328734006496107/400000000000000000000000000000 : ℝ)*base77 + (694035184096107/400000000000000000000000000000 : ℝ)*base79 + (1243392828703893/200000000000000000000000000000 : ℝ)*base82 + (22495049/5000000000000000000000 : ℝ)*base89 + (22495049/5000000000000000000000 : ℝ)*base91 + (22495049/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1660_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1007/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11573/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1660_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1660_s1_0 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-788541891/5000000000 : ℝ)*x 0 + (1372240741/2500000000 : ℝ)*x 1 + (2573044859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (788541891/5000000000 : ℝ)^4959 ≤ (4876222848603/50000000000000 : ℝ)^3935 := by
    have hnat : (788541891 : ℕ)^4959*50000000000000^3935 ≤ 4876222848603^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788541891 5000000000 4876222848603 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372240741/2500000000 : ℝ)^4959 ≤ (23478383922531/50000000000000 : ℝ)^3935 := by
    have hnat : (1372240741 : ℕ)^4959*50000000000000^3935 ≤ 23478383922531^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372240741 2500000000 23478383922531 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2573044859/5000000000 : ℝ)^4959 ≤ (43290786442951/100000000000000 : ℝ)^3935 := by
    have hnat : (2573044859 : ℕ)^4959*100000000000000^3935 ≤ 43290786442951^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573044859 5000000000 43290786442951 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-788541891/5000000000 : ℝ), (1372240741/2500000000 : ℝ), (2573044859/5000000000 : ℝ)] ![(4876222848603/50000000000000 : ℝ), (23478383922531/50000000000000 : ℝ), (43290786442951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-788541891/5000000000 : ℝ)|^4959 ≤ (4876222848603/50000000000000 : ℝ)^3935
        have hw : |(-788541891/5000000000 : ℝ)|=(788541891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372240741/2500000000 : ℝ)|^4959 ≤ (23478383922531/50000000000000 : ℝ)^3935
        have hw : |(1372240741/2500000000 : ℝ)|=(1372240741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2573044859/5000000000 : ℝ)|^4959 ≤ (43290786442951/100000000000000 : ℝ)^3935
        have hw : |(2573044859/5000000000 : ℝ)|=(2573044859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s1_1 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358026443/10000000000 : ℝ)*x 0 + (-877555619/5000000000 : ℝ)*x 1 + (5146089507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358026443/10000000000 : ℝ)^4959 ≤ (11387388611981/25000000000000 : ℝ)^3935 := by
    have hnat : (5358026443 : ℕ)^4959*25000000000000^3935 ≤ 11387388611981^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358026443 10000000000 11387388611981 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877555619/5000000000 : ℝ)^4959 ≤ (11159661334579/100000000000000 : ℝ)^3935 := by
    have hnat : (877555619 : ℕ)^4959*100000000000000^3935 ≤ 11159661334579^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877555619 5000000000 11159661334579 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5146089507/10000000000 : ℝ)^4959 ≤ (21645392103017/50000000000000 : ℝ)^3935 := by
    have hnat : (5146089507 : ℕ)^4959*50000000000000^3935 ≤ 21645392103017^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146089507 10000000000 21645392103017 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358026443/10000000000 : ℝ), (-877555619/5000000000 : ℝ), (5146089507/10000000000 : ℝ)] ![(11387388611981/25000000000000 : ℝ), (11159661334579/100000000000000 : ℝ), (21645392103017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358026443/10000000000 : ℝ)|^4959 ≤ (11387388611981/25000000000000 : ℝ)^3935
        have hw : |(5358026443/10000000000 : ℝ)|=(5358026443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-877555619/5000000000 : ℝ)|^4959 ≤ (11159661334579/100000000000000 : ℝ)^3935
        have hw : |(-877555619/5000000000 : ℝ)|=(877555619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5146089507/10000000000 : ℝ)|^4959 ≤ (21645392103017/50000000000000 : ℝ)^3935
        have hw : |(5146089507/10000000000 : ℝ)|=(5146089507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s1_2 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679012947/5000000000 : ℝ)*x 0 + (643261261/1250000000 : ℝ)*x 1 + (-1755111203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679012947/5000000000 : ℝ)^4959 ≤ (36439638853/80000000000 : ℝ)^3935 := by
    have hnat : (2679012947 : ℕ)^4959*80000000000^3935 ≤ 36439638853^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679012947 5000000000 36439638853 80000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643261261/1250000000 : ℝ)^4959 ≤ (10822697591377/25000000000000 : ℝ)^3935 := by
    have hnat : (643261261 : ℕ)^4959*25000000000000^3935 ≤ 10822697591377^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643261261 1250000000 10822697591377 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1755111203/10000000000 : ℝ)^4959 ≤ (2789915263531/25000000000000 : ℝ)^3935 := by
    have hnat : (1755111203 : ℕ)^4959*25000000000000^3935 ≤ 2789915263531^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755111203 10000000000 2789915263531 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679012947/5000000000 : ℝ), (643261261/1250000000 : ℝ), (-1755111203/10000000000 : ℝ)] ![(36439638853/80000000000 : ℝ), (10822697591377/25000000000000 : ℝ), (2789915263531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679012947/5000000000 : ℝ)|^4959 ≤ (36439638853/80000000000 : ℝ)^3935
        have hw : |(2679012947/5000000000 : ℝ)|=(2679012947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643261261/1250000000 : ℝ)|^4959 ≤ (10822697591377/25000000000000 : ℝ)^3935
        have hw : |(643261261/1250000000 : ℝ)|=(643261261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1755111203/10000000000 : ℝ)|^4959 ≤ (2789915263531/25000000000000 : ℝ)^3935
        have hw : |(-1755111203/10000000000 : ℝ)|=(1755111203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s1_3 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833292207/2000000000 : ℝ)*x 0 + (933646793/2500000000 : ℝ)*x 1 + (2316435829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833292207/2000000000 : ℝ)^4959 ≤ (33175682303733/100000000000000 : ℝ)^3935 := by
    have hnat : (833292207 : ℕ)^4959*100000000000000^3935 ≤ 33175682303733^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833292207 2000000000 33175682303733 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933646793/2500000000 : ℝ)^4959 ≤ (7225499092643/25000000000000 : ℝ)^3935 := by
    have hnat : (933646793 : ℕ)^4959*25000000000000^3935 ≤ 7225499092643^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933646793 2500000000 7225499092643 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2316435829/5000000000 : ℝ)^4959 ≤ (1896116066139/5000000000000 : ℝ)^3935 := by
    have hnat : (2316435829 : ℕ)^4959*5000000000000^3935 ≤ 1896116066139^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316435829 5000000000 1896116066139 5000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833292207/2000000000 : ℝ), (933646793/2500000000 : ℝ), (2316435829/5000000000 : ℝ)] ![(33175682303733/100000000000000 : ℝ), (7225499092643/25000000000000 : ℝ), (1896116066139/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833292207/2000000000 : ℝ)|^4959 ≤ (33175682303733/100000000000000 : ℝ)^3935
        have hw : |(833292207/2000000000 : ℝ)|=(833292207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933646793/2500000000 : ℝ)|^4959 ≤ (7225499092643/25000000000000 : ℝ)^3935
        have hw : |(933646793/2500000000 : ℝ)|=(933646793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2316435829/5000000000 : ℝ)|^4959 ≤ (1896116066139/5000000000000 : ℝ)^3935
        have hw : |(2316435829/5000000000 : ℝ)|=(2316435829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s1_4 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1577227091/10000000000 : ℝ)*x 0 + (643689517/1250000000 : ℝ)*x 1 + (5485489409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1577227091/10000000000 : ℝ)^4959 ≤ (2438390631593/25000000000000 : ℝ)^3935 := by
    have hnat : (1577227091 : ℕ)^4959*25000000000000^3935 ≤ 2438390631593^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577227091 10000000000 2438390631593 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643689517/1250000000 : ℝ)^4959 ≤ (43327114774569/100000000000000 : ℝ)^3935 := by
    have hnat : (643689517 : ℕ)^4959*100000000000000^3935 ≤ 43327114774569^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643689517 1250000000 43327114774569 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485489409/10000000000 : ℝ)^4959 ≤ (1466228833937/3125000000000 : ℝ)^3935 := by
    have hnat : (5485489409 : ℕ)^4959*3125000000000^3935 ≤ 1466228833937^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485489409 10000000000 1466228833937 3125000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1577227091/10000000000 : ℝ), (643689517/1250000000 : ℝ), (5485489409/10000000000 : ℝ)] ![(2438390631593/25000000000000 : ℝ), (43327114774569/100000000000000 : ℝ), (1466228833937/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1577227091/10000000000 : ℝ)|^4959 ≤ (2438390631593/25000000000000 : ℝ)^3935
        have hw : |(-1577227091/10000000000 : ℝ)|=(1577227091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643689517/1250000000 : ℝ)|^4959 ≤ (43327114774569/100000000000000 : ℝ)^3935
        have hw : |(643689517/1250000000 : ℝ)|=(643689517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485489409/10000000000 : ℝ)|^4959 ≤ (1466228833937/3125000000000 : ℝ)^3935
        have hw : |(5485489409/10000000000 : ℝ)|=(5485489409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s1_5 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316565207/2500000000 : ℝ)*x 0 + (-707855643/5000000000 : ℝ)*x 1 + (1371372401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316565207/2500000000 : ℝ)^4959 ≤ (5571078730829/12500000000000 : ℝ)^3935 := by
    have hnat : (1316565207 : ℕ)^4959*12500000000000^3935 ≤ 5571078730829^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316565207 2500000000 5571078730829 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707855643/5000000000 : ℝ)^4959 ≤ (4256022672809/50000000000000 : ℝ)^3935 := by
    have hnat : (707855643 : ℕ)^4959*50000000000000^3935 ≤ 4256022672809^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707855643 5000000000 4256022672809 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371372401/2500000000 : ℝ)^4959 ≤ (11729831196981/25000000000000 : ℝ)^3935 := by
    have hnat : (1371372401 : ℕ)^4959*25000000000000^3935 ≤ 11729831196981^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371372401 2500000000 11729831196981 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316565207/2500000000 : ℝ), (-707855643/5000000000 : ℝ), (1371372401/2500000000 : ℝ)] ![(5571078730829/12500000000000 : ℝ), (4256022672809/50000000000000 : ℝ), (11729831196981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316565207/2500000000 : ℝ)|^4959 ≤ (5571078730829/12500000000000 : ℝ)^3935
        have hw : |(1316565207/2500000000 : ℝ)|=(1316565207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-707855643/5000000000 : ℝ)|^4959 ≤ (4256022672809/50000000000000 : ℝ)^3935
        have hw : |(-707855643/5000000000 : ℝ)|=(707855643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371372401/2500000000 : ℝ)|^4959 ≤ (11729831196981/25000000000000 : ℝ)^3935
        have hw : |(1371372401/2500000000 : ℝ)|=(1371372401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s1_6 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633130333/5000000000 : ℝ)*x 0 + (1371372379/2500000000 : ℝ)*x 1 + (-1415711641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633130333/5000000000 : ℝ)^4959 ≤ (1114215702971/2500000000000 : ℝ)^3935 := by
    have hnat : (2633130333 : ℕ)^4959*2500000000000^3935 ≤ 1114215702971^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633130333 5000000000 1114215702971 2500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371372379/2500000000 : ℝ)^4959 ≤ (11729830959839/25000000000000 : ℝ)^3935 := by
    have hnat : (1371372379 : ℕ)^4959*25000000000000^3935 ≤ 11729830959839^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371372379 2500000000 11729830959839 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1415711641/10000000000 : ℝ)^4959 ≤ (8512048035523/100000000000000 : ℝ)^3935 := by
    have hnat : (1415711641 : ℕ)^4959*100000000000000^3935 ≤ 8512048035523^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415711641 10000000000 8512048035523 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633130333/5000000000 : ℝ), (1371372379/2500000000 : ℝ), (-1415711641/10000000000 : ℝ)] ![(1114215702971/2500000000000 : ℝ), (11729830959839/25000000000000 : ℝ), (8512048035523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633130333/5000000000 : ℝ)|^4959 ≤ (1114215702971/2500000000000 : ℝ)^3935
        have hw : |(2633130333/5000000000 : ℝ)|=(2633130333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371372379/2500000000 : ℝ)|^4959 ≤ (11729830959839/25000000000000 : ℝ)^3935
        have hw : |(1371372379/2500000000 : ℝ)|=(1371372379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1415711641/10000000000 : ℝ)|^4959 ≤ (8512048035523/100000000000000 : ℝ)^3935
        have hw : |(-1415711641/10000000000 : ℝ)|=(1415711641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s1_7 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041709551/2500000000 : ℝ)*x 0 + (924779143/2000000000 : ℝ)*x 1 + (3743687611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041709551/2500000000 : ℝ)^4959 ≤ (16589733552219/50000000000000 : ℝ)^3935 := by
    have hnat : (1041709551 : ℕ)^4959*50000000000000^3935 ≤ 16589733552219^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041709551 2500000000 16589733552219 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924779143/2000000000 : ℝ)^4959 ≤ (37829752539649/100000000000000 : ℝ)^3935 := by
    have hnat : (924779143 : ℕ)^4959*100000000000000^3935 ≤ 37829752539649^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924779143 2000000000 37829752539649 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743687611/10000000000 : ℝ)^4959 ≤ (28990780338311/100000000000000 : ℝ)^3935 := by
    have hnat : (3743687611 : ℕ)^4959*100000000000000^3935 ≤ 28990780338311^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743687611 10000000000 28990780338311 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041709551/2500000000 : ℝ), (924779143/2000000000 : ℝ), (3743687611/10000000000 : ℝ)] ![(16589733552219/50000000000000 : ℝ), (37829752539649/100000000000000 : ℝ), (28990780338311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041709551/2500000000 : ℝ)|^4959 ≤ (16589733552219/50000000000000 : ℝ)^3935
        have hw : |(1041709551/2500000000 : ℝ)|=(1041709551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924779143/2000000000 : ℝ)|^4959 ≤ (37829752539649/100000000000000 : ℝ)^3935
        have hw : |(924779143/2000000000 : ℝ)|=(924779143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743687611/10000000000 : ℝ)|^4959 ≤ (28990780338311/100000000000000 : ℝ)^3935
        have hw : |(3743687611/10000000000 : ℝ)|=(3743687611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1660_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11573/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1007/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9889/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17179/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11573/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1007/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11573/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1007/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11573/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1007/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11573/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1007/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11573/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1007/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11573/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1007/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1007/20000 : ℝ) ^ (4955/1024 : ℝ) ≤ (52377871962181/100000000000000000000 : ℝ) := by
    have hpowers : (1007/20000 : ℝ)^4955 ≤ (52377871962181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1007 : ℕ)^4955*100000000000000000000^1024 ≤ 52377871962181^1024*20000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1007 20000 52377871962181 100000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1007/20000 : ℝ)) (X := (52377871962181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11573/50000 : ℝ) ^ (4955/1024 : ℝ) ≤ (21024396115387347/25000000000000000000 : ℝ) := by
    have hpowers : (11573/50000 : ℝ)^4955 ≤ (21024396115387347/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11573 : ℕ)^4955*25000000000000000000^1024 ≤ 21024396115387347^1024*50000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11573 50000 21024396115387347 25000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11573/50000 : ℝ)) (X := (21024396115387347/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000052377871962181/50000000000000000000 : ℝ) ≤ (10000002164880671/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (50000052377871962181/50000000000000000000 : ℝ)^1024 ≤ (10000002164880671/10000000000000000 : ℝ)^4955 := by
      have hnat : (50000052377871962181 : ℕ)^1024*10000000000000000^4955 ≤ 10000002164880671^4955*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000052377871962181 50000000000000000000 10000002164880671 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002164880671/10000000000000000 : ℝ)) (X := (50000052377871962181/50000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100084149962333511569/100000000000000000000 : ℝ) ≤ (10001738462415541/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (100084149962333511569/100000000000000000000 : ℝ)^1024 ≤ (10001738462415541/10000000000000000 : ℝ)^4955 := by
      have hnat : (100084149962333511569 : ℕ)^1024*10000000000000000^4955 ≤ 10001738462415541^4955*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100084149962333511569 100000000000000000000 10001738462415541 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001738462415541/10000000000000000 : ℝ)) (X := (100084149962333511569/100000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12521024396115387347/12500000000000000000 : ℝ) ≤ (10003474759950411/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (12521024396115387347/12500000000000000000 : ℝ)^1024 ≤ (10003474759950411/10000000000000000 : ℝ)^4955 := by
      have hnat : (12521024396115387347 : ℕ)^1024*10000000000000000^4955 ≤ 10003474759950411^4955*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12521024396115387347 12500000000000000000 10003474759950411 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003474759950411/10000000000000000 : ℝ)) (X := (12521024396115387347/12500000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(52377871962181/100000000000000000000 : ℝ) ≤ ((181092554691977691581/181110000000000000000 : ℝ)+2*(173629753487/181110000000000 : ℝ)*(1007/20000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (181092554691977691581/181110000000000000000 : ℝ)+2*(173629753487/181110000000000 : ℝ)*(1007/20000 : ℝ)=(10000002164880671/10000000000000000 : ℝ) by norm_num, show 1+2*(52377871962181/100000000000000000000 : ℝ)=(50000052377871962181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21024396115387347/25000000000000000000 : ℝ)+(52377871962181/100000000000000000000 : ℝ) ≤ ((181092554691977691581/181110000000000000000 : ℝ)+(173629753487/181110000000000 : ℝ)*((11573/50000 : ℝ)+(1007/20000 : ℝ)))^(4955/1024 : ℝ) := by
    rw [show (181092554691977691581/181110000000000000000 : ℝ)+(173629753487/181110000000000 : ℝ)*((11573/50000 : ℝ)+(1007/20000 : ℝ))=(10001738462415541/10000000000000000 : ℝ) by norm_num, show 1+(21024396115387347/25000000000000000000 : ℝ)+(52377871962181/100000000000000000000 : ℝ)=(100084149962333511569/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21024396115387347/25000000000000000000 : ℝ) ≤ ((181092554691977691581/181110000000000000000 : ℝ)+2*(173629753487/181110000000000 : ℝ)*(11573/50000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (181092554691977691581/181110000000000000000 : ℝ)+2*(173629753487/181110000000000 : ℝ)*(11573/50000 : ℝ)=(10003474759950411/10000000000000000 : ℝ) by norm_num, show 1+2*(21024396115387347/25000000000000000000 : ℝ)=(12521024396115387347/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (181092554691977691581/181110000000000000000 : ℝ)*(X 1 0+X 2 0)+(173629753487/181110000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (1007/20000 : ℝ)) (hi := (11573/50000 : ℝ)) (c := (181092554691977691581/181110000000000000000 : ℝ)) (alpha := (173629753487/181110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (181092554691977691581/181110000000000000000 : ℝ)*(X 0 1+X 2 1)+(173629753487/181110000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (1007/20000 : ℝ)) (hi := (11573/50000 : ℝ)) (c := (181092554691977691581/181110000000000000000 : ℝ)) (alpha := (173629753487/181110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (181092554691977691581/181110000000000000000 : ℝ)*(X 0 2+X 1 2)+(173629753487/181110000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (1007/20000 : ℝ)) (hi := (11573/50000 : ℝ)) (c := (181092554691977691581/181110000000000000000 : ℝ)) (alpha := (173629753487/181110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-788541891/5000000000 : ℝ)*X 0 0+(1372240741/2500000000 : ℝ)*X 0 1+(2573044859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358026443/10000000000 : ℝ)*X 1 0+(-877555619/5000000000 : ℝ)*X 1 1+(5146089507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679012947/5000000000 : ℝ)*X 2 0+(643261261/1250000000 : ℝ)*X 2 1+(-1755111203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((833292207/2000000000 : ℝ)*X 0 0+(933646793/2500000000 : ℝ)*X 0 1+(2316435829/5000000000 : ℝ)*X 0 2+(833292207/2000000000 : ℝ)*X 1 0+(933646793/2500000000 : ℝ)*X 1 1+(2316435829/5000000000 : ℝ)*X 1 2+(833292207/2000000000 : ℝ)*X 2 0+(933646793/2500000000 : ℝ)*X 2 1+(2316435829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1577227091/10000000000 : ℝ)*X 0 0+(643689517/1250000000 : ℝ)*X 0 1+(5485489409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1316565207/2500000000 : ℝ)*X 1 0+(-707855643/5000000000 : ℝ)*X 1 1+(1371372401/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633130333/5000000000 : ℝ)*X 2 0+(1371372379/2500000000 : ℝ)*X 2 1+(-1415711641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1041709551/2500000000 : ℝ)*X 0 0+(924779143/2000000000 : ℝ)*X 0 1+(3743687611/10000000000 : ℝ)*X 0 2+(1041709551/2500000000 : ℝ)*X 1 0+(924779143/2000000000 : ℝ)*X 1 1+(3743687611/10000000000 : ℝ)*X 1 2+(1041709551/2500000000 : ℝ)*X 2 0+(924779143/2000000000 : ℝ)*X 2 1+(3743687611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1979890898656175959172091057/754625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1248383671/100000000000000 : ℝ)*(base19) + (96749273/12500000000000 : ℝ)*(base23) + (4334869/2000000000000 : ℝ)*(upper3) + (47030259/50000000000000 : ℝ)*(upper4) + (14177981/20000000000000 : ℝ)*(upper5) + (1007448275846797/50000000000000 : ℝ)*(major0) + (1007448275846797/50000000000000 : ℝ)*(major1) + (1007448275846797/50000000000000 : ℝ)*(major2) + (145827081247803/5000000000000 : ℝ)*(sp0) + (729137507754441/25000000000000 : ℝ)*(sp1) + (2916550505407251/100000000000000 : ℝ)*(sp2) + (55661847604219/5000000000000 : ℝ)*(sp3) + (150850709/1562500000000 : ℝ)*(sp4) + (598055691/12500000000000 : ℝ)*(sp7) + (278310434132477/25000000000000 : ℝ)*(f.failure) + (583310255880287/20000000000000 : ℝ)*(f.sum) + (1084091350883/452775000000000000000000000 : ℝ)*base65 + (46554601801296283943/9055500000000000000000000000000000 : ℝ)*base68 + (50120971528704283943/9055500000000000000000000000000000 : ℝ)*base70 + (22950131336459716057/9055500000000000000000000000000000 : ℝ)*base71 + (14386211584693/4527750000000000000000000000 : ℝ)*base74 + (27176041345566283943/9055500000000000000000000000000000 : ℝ)*base76 + (50930287770321283943/9055500000000000000000000000000000 : ℝ)*base78 + (5483192400012283943/9055500000000000000000000000000000 : ℝ)*base80 + (34979387195411/18111000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (24194171/2500000000000000000000 : ℝ)*base89 + (24194171/2500000000000000000000 : ℝ)*base91 + (24194171/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32873531204363527993803/3018500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1875867139/100000000000000 : ℝ)*(base19) + (2066451279/100000000000000 : ℝ)*(base23) + (290136153/100000000000000 : ℝ)*(upper3) + (28458727/20000000000000 : ℝ)*(lower4) + (48938101/25000000000000 : ℝ)*(upper5) + (2056259292330171/100000000000000 : ℝ)*(major0) + (2056259292330171/100000000000000 : ℝ)*(major1) + (2056259292330171/100000000000000 : ℝ)*(major2) + (18113320443/100000000000000 : ℝ)*(sp1) + (4699736811/25000000000000 : ℝ)*(sp2) + (2976423337051353/100000000000000 : ℝ)*(sp4) + (2976403347863771/100000000000000 : ℝ)*(sp5) + (297640247165283/10000000000000 : ℝ)*(sp6) + (568047442293083/50000000000000 : ℝ)*(sp7) + (568047442293083/50000000000000 : ℝ)*(f.failure) + (2976423337051353/100000000000000 : ℝ)*(f.sum) + (21669675967101/6037000000000000000000000000 : ℝ)*base65 + (8524260269380669883/6037000000000000000000000000000000 : ℝ)*base68 + (4184233833734330117/6037000000000000000000000000000000 : ℝ)*base69 + (25724776875908330117/6037000000000000000000000000000000 : ℝ)*base71 + (1420459721221/754625000000000000000000000 : ℝ)*base73 + (31488446906861669883/6037000000000000000000000000000000 : ℝ)*base76 + (6983608983585330117/6037000000000000000000000000000000 : ℝ)*base77 + (35122773615908669883/6037000000000000000000000000000000 : ℝ)*base80 + (576429473631/120740000000000000000000000 : ℝ)*base81 + (29990291/5000000000000000000000 : ℝ)*base90 + (29990291/5000000000000000000000 : ℝ)*base92 + (29990291/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1660_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11573/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1007/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17179/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1660_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1660_s2_0 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-792739387/5000000000 : ℝ)*x 0 + (1089517979/2000000000 : ℝ)*x 1 + (518191403/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792739387/5000000000 : ℝ)^4959 ≤ (1963582729187/20000000000000 : ℝ)^3935 := by
    have hnat : (792739387 : ℕ)^4959*20000000000000^3935 ≤ 1963582729187^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792739387 5000000000 1963582729187 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089517979/2000000000 : ℝ)^4959 ≤ (1860446595221/4000000000000 : ℝ)^3935 := by
    have hnat : (1089517979 : ℕ)^4959*4000000000000^3935 ≤ 1860446595221^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089517979 2000000000 1860446595221 4000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518191403/1000000000 : ℝ)^4959 ≤ (8734184292339/20000000000000 : ℝ)^3935 := by
    have hnat : (518191403 : ℕ)^4959*20000000000000^3935 ≤ 8734184292339^3935*1000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518191403 1000000000 8734184292339 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-792739387/5000000000 : ℝ), (1089517979/2000000000 : ℝ), (518191403/1000000000 : ℝ)] ![(1963582729187/20000000000000 : ℝ), (1860446595221/4000000000000 : ℝ), (8734184292339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-792739387/5000000000 : ℝ)|^4959 ≤ (1963582729187/20000000000000 : ℝ)^3935
        have hw : |(-792739387/5000000000 : ℝ)|=(792739387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089517979/2000000000 : ℝ)|^4959 ≤ (1860446595221/4000000000000 : ℝ)^3935
        have hw : |(1089517979/2000000000 : ℝ)|=(1089517979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518191403/1000000000 : ℝ)|^4959 ≤ (8734184292339/20000000000000 : ℝ)^3935
        have hw : |(518191403/1000000000 : ℝ)|=(518191403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s2_1 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336760119/2500000000 : ℝ)*x 0 + (-1722275419/10000000000 : ℝ)*x 1 + (2590956971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336760119/2500000000 : ℝ)^4959 ≤ (45431888443693/100000000000000 : ℝ)^3935 := by
    have hnat : (1336760119 : ℕ)^4959*100000000000000^3935 ≤ 45431888443693^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336760119 2500000000 45431888443693 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722275419/10000000000 : ℝ)^4959 ≤ (10897191023889/100000000000000 : ℝ)^3935 := by
    have hnat : (1722275419 : ℕ)^4959*100000000000000^3935 ≤ 10897191023889^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722275419 10000000000 10897191023889 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590956971/5000000000 : ℝ)^4959 ≤ (43670920527077/100000000000000 : ℝ)^3935 := by
    have hnat : (2590956971 : ℕ)^4959*100000000000000^3935 ≤ 43670920527077^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590956971 5000000000 43670920527077 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336760119/2500000000 : ℝ), (-1722275419/10000000000 : ℝ), (2590956971/5000000000 : ℝ)] ![(45431888443693/100000000000000 : ℝ), (10897191023889/100000000000000 : ℝ), (43670920527077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336760119/2500000000 : ℝ)|^4959 ≤ (45431888443693/100000000000000 : ℝ)^3935
        have hw : |(1336760119/2500000000 : ℝ)|=(1336760119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1722275419/10000000000 : ℝ)|^4959 ≤ (10897191023889/100000000000000 : ℝ)^3935
        have hw : |(-1722275419/10000000000 : ℝ)|=(1722275419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590956971/5000000000 : ℝ)|^4959 ≤ (43670920527077/100000000000000 : ℝ)^3935
        have hw : |(2590956971/5000000000 : ℝ)|=(2590956971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s2_2 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347039307/10000000000 : ℝ)*x 0 + (5181914587/10000000000 : ℝ)*x 1 + (-1722276127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347039307/10000000000 : ℝ)^4959 ≤ (22715937963189/50000000000000 : ℝ)^3935 := by
    have hnat : (5347039307 : ℕ)^4959*50000000000000^3935 ≤ 22715937963189^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347039307 10000000000 22715937963189 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181914587/10000000000 : ℝ)^4959 ≤ (43670927377403/100000000000000 : ℝ)^3935 := by
    have hnat : (5181914587 : ℕ)^4959*100000000000000^3935 ≤ 43670927377403^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181914587 10000000000 43670927377403 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722276127/10000000000 : ℝ)^4959 ≤ (10897196669287/100000000000000 : ℝ)^3935 := by
    have hnat : (1722276127 : ℕ)^4959*100000000000000^3935 ≤ 10897196669287^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722276127 10000000000 10897196669287 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347039307/10000000000 : ℝ), (5181914587/10000000000 : ℝ), (-1722276127/10000000000 : ℝ)] ![(22715937963189/50000000000000 : ℝ), (43670927377403/100000000000000 : ℝ), (10897196669287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347039307/10000000000 : ℝ)|^4959 ≤ (22715937963189/50000000000000 : ℝ)^3935
        have hw : |(5347039307/10000000000 : ℝ)|=(5347039307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181914587/10000000000 : ℝ)|^4959 ≤ (43670927377403/100000000000000 : ℝ)^3935
        have hw : |(5181914587/10000000000 : ℝ)|=(5181914587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722276127/10000000000 : ℝ)|^4959 ≤ (10897196669287/100000000000000 : ℝ)^3935
        have hw : |(-1722276127/10000000000 : ℝ)|=(1722276127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s2_3 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1043183487/2500000000 : ℝ)*x 0 + (3835090523/10000000000 : ℝ)*x 1 + (4531124171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043183487/2500000000 : ℝ)^4959 ≤ (16619320535193/50000000000000 : ℝ)^3935 := by
    have hnat : (1043183487 : ℕ)^4959*50000000000000^3935 ≤ 16619320535193^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043183487 2500000000 16619320535193 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3835090523/10000000000 : ℝ)^4959 ≤ (29885607132803/100000000000000 : ℝ)^3935 := by
    have hnat : (3835090523 : ℕ)^4959*100000000000000^3935 ≤ 29885607132803^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3835090523 10000000000 29885607132803 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531124171/10000000000 : ℝ)^4959 ≤ (1475030071013/4000000000000 : ℝ)^3935 := by
    have hnat : (4531124171 : ℕ)^4959*4000000000000^3935 ≤ 1475030071013^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531124171 10000000000 1475030071013 4000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043183487/2500000000 : ℝ), (3835090523/10000000000 : ℝ), (4531124171/10000000000 : ℝ)] ![(16619320535193/50000000000000 : ℝ), (29885607132803/100000000000000 : ℝ), (1475030071013/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043183487/2500000000 : ℝ)|^4959 ≤ (16619320535193/50000000000000 : ℝ)^3935
        have hw : |(1043183487/2500000000 : ℝ)|=(1043183487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3835090523/10000000000 : ℝ)|^4959 ≤ (29885607132803/100000000000000 : ℝ)^3935
        have hw : |(3835090523/10000000000 : ℝ)|=(3835090523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531124171/10000000000 : ℝ)|^4959 ≤ (1475030071013/4000000000000 : ℝ)^3935
        have hw : |(4531124171/10000000000 : ℝ)|=(4531124171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s2_4 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-317108999/2000000000 : ℝ)*x 0 + (2591988317/5000000000 : ℝ)*x 1 + (1361376429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317108999/2000000000 : ℝ)^4959 ≤ (9818430426583/100000000000000 : ℝ)^3935 := by
    have hnat : (317108999 : ℕ)^4959*100000000000000^3935 ≤ 9818430426583^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317108999 2000000000 9818430426583 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591988317/5000000000 : ℝ)^4959 ≤ (43692828812813/100000000000000 : ℝ)^3935 := by
    have hnat : (2591988317 : ℕ)^4959*100000000000000^3935 ≤ 43692828812813^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591988317 5000000000 43692828812813 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361376429/2500000000 : ℝ)^4959 ≤ (46488740751869/100000000000000 : ℝ)^3935 := by
    have hnat : (1361376429 : ℕ)^4959*100000000000000^3935 ≤ 46488740751869^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361376429 2500000000 46488740751869 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-317108999/2000000000 : ℝ), (2591988317/5000000000 : ℝ), (1361376429/2500000000 : ℝ)] ![(9818430426583/100000000000000 : ℝ), (43692828812813/100000000000000 : ℝ), (46488740751869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-317108999/2000000000 : ℝ)|^4959 ≤ (9818430426583/100000000000000 : ℝ)^3935
        have hw : |(-317108999/2000000000 : ℝ)|=(317108999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591988317/5000000000 : ℝ)|^4959 ≤ (43692828812813/100000000000000 : ℝ)^3935
        have hw : |(2591988317/5000000000 : ℝ)|=(2591988317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361376429/2500000000 : ℝ)|^4959 ≤ (46488740751869/100000000000000 : ℝ)^3935
        have hw : |(1361376429/2500000000 : ℝ)|=(1361376429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s2_5 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275981257/10000000000 : ℝ)*x 0 + (-1458685241/10000000000 : ℝ)*x 1 + (1089100927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275981257/10000000000 : ℝ)^4959 ≤ (357378614337/800000000000 : ℝ)^3935 := by
    have hnat : (5275981257 : ℕ)^4959*800000000000^3935 ≤ 357378614337^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275981257 10000000000 357378614337 800000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1458685241/10000000000 : ℝ)^4959 ≤ (4419472036309/50000000000000 : ℝ)^3935 := by
    have hnat : (1458685241 : ℕ)^4959*50000000000000^3935 ≤ 4419472036309^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458685241 10000000000 4419472036309 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089100927/2000000000 : ℝ)^4959 ≤ (23244364560869/50000000000000 : ℝ)^3935 := by
    have hnat : (1089100927 : ℕ)^4959*50000000000000^3935 ≤ 23244364560869^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089100927 2000000000 23244364560869 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275981257/10000000000 : ℝ), (-1458685241/10000000000 : ℝ), (1089100927/2000000000 : ℝ)] ![(357378614337/800000000000 : ℝ), (4419472036309/50000000000000 : ℝ), (23244364560869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275981257/10000000000 : ℝ)|^4959 ≤ (357378614337/800000000000 : ℝ)^3935
        have hw : |(5275981257/10000000000 : ℝ)|=(5275981257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1458685241/10000000000 : ℝ)|^4959 ≤ (4419472036309/50000000000000 : ℝ)^3935
        have hw : |(-1458685241/10000000000 : ℝ)|=(1458685241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089100927/2000000000 : ℝ)|^4959 ≤ (23244364560869/50000000000000 : ℝ)^3935
        have hw : |(1089100927/2000000000 : ℝ)|=(1089100927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s2_6 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637991019/5000000000 : ℝ)*x 0 + (5445504233/10000000000 : ℝ)*x 1 + (-1458684717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637991019/5000000000 : ℝ)^4959 ≤ (5584041890723/12500000000000 : ℝ)^3935 := by
    have hnat : (2637991019 : ℕ)^4959*12500000000000^3935 ≤ 5584041890723^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637991019 5000000000 5584041890723 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445504233/10000000000 : ℝ)^4959 ≤ (46488724796749/100000000000000 : ℝ)^3935 := by
    have hnat : (5445504233 : ℕ)^4959*100000000000000^3935 ≤ 46488724796749^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445504233 10000000000 46488724796749 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458684717/10000000000 : ℝ)^4959 ≤ (176778801423/2000000000000 : ℝ)^3935 := by
    have hnat : (1458684717 : ℕ)^4959*2000000000000^3935 ≤ 176778801423^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458684717 10000000000 176778801423 2000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637991019/5000000000 : ℝ), (5445504233/10000000000 : ℝ), (-1458684717/10000000000 : ℝ)] ![(5584041890723/12500000000000 : ℝ), (46488724796749/100000000000000 : ℝ), (176778801423/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637991019/5000000000 : ℝ)|^4959 ≤ (5584041890723/12500000000000 : ℝ)^3935
        have hw : |(2637991019/5000000000 : ℝ)|=(2637991019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445504233/10000000000 : ℝ)|^4959 ≤ (46488724796749/100000000000000 : ℝ)^3935
        have hw : |(5445504233/10000000000 : ℝ)|=(5445504233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1458684717/10000000000 : ℝ)|^4959 ≤ (176778801423/2000000000000 : ℝ)^3935
        have hw : |(-1458684717/10000000000 : ℝ)|=(1458684717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s2_7 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2086455309/5000000000 : ℝ)*x 0 + (2262860933/5000000000 : ℝ)*x 1 + (960137493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086455309/5000000000 : ℝ)^4959 ≤ (33240414594663/100000000000000 : ℝ)^3935 := by
    have hnat : (2086455309 : ℕ)^4959*100000000000000^3935 ≤ 33240414594663^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086455309 5000000000 33240414594663 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262860933/5000000000 : ℝ)^4959 ≤ (36820353532079/100000000000000 : ℝ)^3935 := by
    have hnat : (2262860933 : ℕ)^4959*100000000000000^3935 ≤ 36820353532079^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262860933 5000000000 36820353532079 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960137493/2500000000 : ℝ)^4959 ≤ (29939231854941/100000000000000 : ℝ)^3935 := by
    have hnat : (960137493 : ℕ)^4959*100000000000000^3935 ≤ 29939231854941^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960137493 2500000000 29939231854941 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086455309/5000000000 : ℝ), (2262860933/5000000000 : ℝ), (960137493/2500000000 : ℝ)] ![(33240414594663/100000000000000 : ℝ), (36820353532079/100000000000000 : ℝ), (29939231854941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086455309/5000000000 : ℝ)|^4959 ≤ (33240414594663/100000000000000 : ℝ)^3935
        have hw : |(2086455309/5000000000 : ℝ)|=(2086455309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262860933/5000000000 : ℝ)|^4959 ≤ (36820353532079/100000000000000 : ℝ)^3935
        have hw : |(2262860933/5000000000 : ℝ)|=(2262860933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(960137493/2500000000 : ℝ)|^4959 ≤ (29939231854941/100000000000000 : ℝ)^3935
        have hw : |(960137493/2500000000 : ℝ)|=(960137493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1660_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5331/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16313/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9889/100000 : ℝ) ^ (4955/1024 : ℝ) ≤ (137301666367671/10000000000000000000 : ℝ) := by
    have hpowers : (9889/100000 : ℝ)^4955 ≤ (137301666367671/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9889 : ℕ)^4955*10000000000000000000^1024 ≤ 137301666367671^1024*100000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9889 100000 137301666367671 10000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9889/100000 : ℝ)) (X := (137301666367671/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17179/100000 : ℝ) ^ (4955/1024 : ℝ) ≤ (621021110263463/3125000000000000000 : ℝ) := by
    have hpowers : (17179/100000 : ℝ)^4955 ≤ (621021110263463/3125000000000000000 : ℝ)^1024 := by
      have hnat : (17179 : ℕ)^4955*3125000000000000000^1024 ≤ 621021110263463^1024*100000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17179 100000 621021110263463 3125000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17179/100000 : ℝ)) (X := (621021110263463/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000137301666367671/5000000000000000000 : ℝ) ≤ (10000056748889973/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (5000137301666367671/5000000000000000000 : ℝ)^1024 ≤ (10000056748889973/10000000000000000 : ℝ)^4955 := by
      have hnat : (5000137301666367671 : ℕ)^1024*10000000000000000^4955 ≤ 10000056748889973^4955*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000137301666367671 5000000000000000000 10000056748889973 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000056748889973/10000000000000000 : ℝ)) (X := (5000137301666367671/5000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010622846096053763/50000000000000000000 : ℝ) ≤ (10000439026348717/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (50010622846096053763/50000000000000000000 : ℝ)^1024 ≤ (10000439026348717/10000000000000000 : ℝ)^4955 := by
      have hnat : (50010622846096053763 : ℕ)^1024*10000000000000000^4955 ≤ 10000439026348717^4955*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010622846096053763 50000000000000000000 10000439026348717 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000439026348717/10000000000000000 : ℝ)) (X := (50010622846096053763/50000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563121021110263463/1562500000000000000 : ℝ) ≤ (10000821303807461/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (1563121021110263463/1562500000000000000 : ℝ)^1024 ≤ (10000821303807461/10000000000000000 : ℝ)^4955 := by
      have hnat : (1563121021110263463 : ℕ)^1024*10000000000000000^4955 ≤ 10000821303807461^4955*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563121021110263463 1562500000000000000 10000821303807461 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000821303807461/10000000000000000 : ℝ)) (X := (1563121021110263463/1562500000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(137301666367671/10000000000000000000 : ℝ) ≤ ((36446426507914432169/36450000000000000000 : ℝ)+2*(47784682343/91125000000000 : ℝ)*(9889/100000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (36446426507914432169/36450000000000000000 : ℝ)+2*(47784682343/91125000000000 : ℝ)*(9889/100000 : ℝ)=(10000056748889973/10000000000000000 : ℝ) by norm_num, show 1+2*(137301666367671/10000000000000000000 : ℝ)=(5000137301666367671/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(621021110263463/3125000000000000000 : ℝ)+(137301666367671/10000000000000000000 : ℝ) ≤ ((36446426507914432169/36450000000000000000 : ℝ)+(47784682343/91125000000000 : ℝ)*((17179/100000 : ℝ)+(9889/100000 : ℝ)))^(4955/1024 : ℝ) := by
    rw [show (36446426507914432169/36450000000000000000 : ℝ)+(47784682343/91125000000000 : ℝ)*((17179/100000 : ℝ)+(9889/100000 : ℝ))=(10000439026348717/10000000000000000 : ℝ) by norm_num, show 1+(621021110263463/3125000000000000000 : ℝ)+(137301666367671/10000000000000000000 : ℝ)=(50010622846096053763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(621021110263463/3125000000000000000 : ℝ) ≤ ((36446426507914432169/36450000000000000000 : ℝ)+2*(47784682343/91125000000000 : ℝ)*(17179/100000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (36446426507914432169/36450000000000000000 : ℝ)+2*(47784682343/91125000000000 : ℝ)*(17179/100000 : ℝ)=(10000821303807461/10000000000000000 : ℝ) by norm_num, show 1+2*(621021110263463/3125000000000000000 : ℝ)=(1563121021110263463/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36446426507914432169/36450000000000000000 : ℝ)*(X 1 0+X 2 0)+(47784682343/91125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (17179/100000 : ℝ)) (c := (36446426507914432169/36450000000000000000 : ℝ)) (alpha := (47784682343/91125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36446426507914432169/36450000000000000000 : ℝ)*(X 0 1+X 2 1)+(47784682343/91125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (17179/100000 : ℝ)) (c := (36446426507914432169/36450000000000000000 : ℝ)) (alpha := (47784682343/91125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36446426507914432169/36450000000000000000 : ℝ)*(X 0 2+X 1 2)+(47784682343/91125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (17179/100000 : ℝ)) (c := (36446426507914432169/36450000000000000000 : ℝ)) (alpha := (47784682343/91125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-792739387/5000000000 : ℝ)*X 0 0+(1089517979/2000000000 : ℝ)*X 0 1+(518191403/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336760119/2500000000 : ℝ)*X 1 0+(-1722275419/10000000000 : ℝ)*X 1 1+(2590956971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347039307/10000000000 : ℝ)*X 2 0+(5181914587/10000000000 : ℝ)*X 2 1+(-1722276127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1043183487/2500000000 : ℝ)*X 0 0+(3835090523/10000000000 : ℝ)*X 0 1+(4531124171/10000000000 : ℝ)*X 0 2+(1043183487/2500000000 : ℝ)*X 1 0+(3835090523/10000000000 : ℝ)*X 1 1+(4531124171/10000000000 : ℝ)*X 1 2+(1043183487/2500000000 : ℝ)*X 2 0+(3835090523/10000000000 : ℝ)*X 2 1+(4531124171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-317108999/2000000000 : ℝ)*X 0 0+(2591988317/5000000000 : ℝ)*X 0 1+(1361376429/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275981257/10000000000 : ℝ)*X 1 0+(-1458685241/10000000000 : ℝ)*X 1 1+(1089100927/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2637991019/5000000000 : ℝ)*X 2 0+(5445504233/10000000000 : ℝ)*X 2 1+(-1458684717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2086455309/5000000000 : ℝ)*X 0 0+(2262860933/5000000000 : ℝ)*X 0 1+(960137493/2500000000 : ℝ)*X 0 2+(2086455309/5000000000 : ℝ)*X 1 0+(2262860933/5000000000 : ℝ)*X 1 1+(960137493/2500000000 : ℝ)*X 1 2+(2086455309/5000000000 : ℝ)*X 2 0+(2262860933/5000000000 : ℝ)*X 2 1+(960137493/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1025506140094149562499/75000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73120357/4000000000000 : ℝ)*(base19) + (971672129/100000000000000 : ℝ)*(base23) + (332212561/100000000000000 : ℝ)*(upper3) + (4810233/20000000000000 : ℝ)*(lower4) + (2600380681149159/100000000000000 : ℝ)*(major0) + (2600380681149159/100000000000000 : ℝ)*(major1) + (2600380681149159/100000000000000 : ℝ)*(major2) + (1882008162385037/50000000000000 : ℝ)*(sp0) + (235252128142157/6250000000000 : ℝ)*(sp1) + (376402900683001/10000000000000 : ℝ)*(sp2) + (718359002674707/50000000000000 : ℝ)*(sp3) + (19553513363/100000000000000 : ℝ)*(sp4) + (5899781297/100000000000000 : ℝ)*(sp6) + (1755721239/25000000000000 : ℝ)*(sp7) + (143672502823437/10000000000000 : ℝ)*(f.failure) + (3764035878283437/100000000000000 : ℝ)*(f.sum) + (1085566185301/675000000000000000000000000 : ℝ)*base66 + (212182570783025773/135000000000000000000000000000000 : ℝ)*base67 + (391120868356974227/135000000000000000000000000000000 : ℝ)*base70 + (54496861486974227/135000000000000000000000000000000 : ℝ)*base72 + (316637529113/337500000000000000000000000 : ℝ)*base74 + (476061732883025773/135000000000000000000000000000000 : ℝ)*base75 + (251920678426974227/135000000000000000000000000000000 : ℝ)*base78 + (1789451871418025773/135000000000000000000000000000000 : ℝ)*base79 + (3311517727201/675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1942251/1000000000000000000000 : ℝ)*base89 + (1942251/1000000000000000000000 : ℝ)*base91 + (1942251/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (779050441194525219646506959/303750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (274516461/100000000000000 : ℝ)*(base19) + (28097109/100000000000000 : ℝ)*(base23) + (428640423/100000000000000 : ℝ)*(lower2) + (21433647/20000000000000 : ℝ)*(lower3) + (5399921/3125000000000 : ℝ)*(lower5) + (2641591069220089/100000000000000 : ℝ)*(major0) + (2641591069220089/100000000000000 : ℝ)*(major1) + (2641591069220089/100000000000000 : ℝ)*(major2) + (6872145719/100000000000000 : ℝ)*(sp0) + (712508471/50000000000000 : ℝ)*(sp3) + (955920295041301/25000000000000 : ℝ)*(sp4) + (1911843888897231/50000000000000 : ℝ)*(sp5) + (1911844012106907/50000000000000 : ℝ)*(sp6) + (364873143904951/25000000000000 : ℝ)*(sp7) + (729747000318373/50000000000000 : ℝ)*(f.failure) + (3823688052310923/100000000000000 : ℝ)*(f.sum) + (20186737623671/9112500000000000000000000000 : ℝ)*base66 + (39042923528238443041/3645000000000000000000000000000000 : ℝ)*base67 + (10329208120046556959/3645000000000000000000000000000000 : ℝ)*base70 + (15774713006343443041/3645000000000000000000000000000000 : ℝ)*base71 + (2715561529649/2278125000000000000000000000 : ℝ)*base74 + (21741369082233443041/3645000000000000000000000000000000 : ℝ)*base75 + (17870317554633443041/3645000000000000000000000000000000 : ℝ)*base77 + (27939080490693443041/3645000000000000000000000000000000 : ℝ)*base79 + (6028313297287/1139062500000000000000000000 : ℝ)*base82 + (32735379/5000000000000000000000 : ℝ)*base89 + (32735379/5000000000000000000000 : ℝ)*base91 + (32735379/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1660_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1660_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1660_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1660_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1660_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1660_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1660_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
