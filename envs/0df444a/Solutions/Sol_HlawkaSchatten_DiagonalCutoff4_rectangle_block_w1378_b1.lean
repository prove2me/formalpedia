-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1378_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:46.396111+00:00
-- url     : https://prove2.me/submissions/f181fe82-8aec-45e0-85aa-aff08c5ce134

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
theorem support_rectangle_w1378_s3_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-502961573/2500000000 : ℝ)*x 0 + (16946231/31250000 : ℝ)*x 1 + (5234642969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502961573/2500000000 : ℝ)^2169 ≤ (245155165541/2000000000000 : ℝ)^1657 := by
    have hnat : (502961573 : ℕ)^2169*2000000000000^1657 ≤ 245155165541^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502961573 2500000000 245155165541 2000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16946231/31250000 : ℝ)^2169 ≤ (44884885706237/100000000000000 : ℝ)^1657 := by
    have hnat : (16946231 : ℕ)^2169*100000000000000^1657 ≤ 44884885706237^1657*31250000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16946231 31250000 44884885706237 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234642969/10000000000 : ℝ)^2169 ≤ (8571471199991/20000000000000 : ℝ)^1657 := by
    have hnat : (5234642969 : ℕ)^2169*20000000000000^1657 ≤ 8571471199991^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234642969 10000000000 8571471199991 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502961573/2500000000 : ℝ), (16946231/31250000 : ℝ), (5234642969/10000000000 : ℝ)] ![(245155165541/2000000000000 : ℝ), (44884885706237/100000000000000 : ℝ), (8571471199991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502961573/2500000000 : ℝ)|^2169 ≤ (245155165541/2000000000000 : ℝ)^1657
        have hw : |(-502961573/2500000000 : ℝ)|=(502961573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16946231/31250000 : ℝ)|^2169 ≤ (44884885706237/100000000000000 : ℝ)^1657
        have hw : |(16946231/31250000 : ℝ)|=(16946231/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234642969/10000000000 : ℝ)|^2169 ≤ (8571471199991/20000000000000 : ℝ)^1657
        have hw : |(5234642969/10000000000 : ℝ)|=(5234642969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s3_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675704663/5000000000 : ℝ)*x 0 + (-2107923077/10000000000 : ℝ)*x 1 + (5234643263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675704663/5000000000 : ℝ)^2169 ≤ (11028259457463/25000000000000 : ℝ)^1657 := by
    have hnat : (2675704663 : ℕ)^2169*25000000000000^1657 ≤ 11028259457463^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675704663 5000000000 11028259457463 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107923077/10000000000 : ℝ)^2169 ≤ (6514801501603/50000000000000 : ℝ)^1657 := by
    have hnat : (2107923077 : ℕ)^2169*50000000000000^1657 ≤ 6514801501603^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107923077 10000000000 6514801501603 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234643263/10000000000 : ℝ)^2169 ≤ (42857359150769/100000000000000 : ℝ)^1657 := by
    have hnat : (5234643263 : ℕ)^2169*100000000000000^1657 ≤ 42857359150769^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234643263 10000000000 42857359150769 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675704663/5000000000 : ℝ), (-2107923077/10000000000 : ℝ), (5234643263/10000000000 : ℝ)] ![(11028259457463/25000000000000 : ℝ), (6514801501603/50000000000000 : ℝ), (42857359150769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675704663/5000000000 : ℝ)|^2169 ≤ (11028259457463/25000000000000 : ℝ)^1657
        have hw : |(2675704663/5000000000 : ℝ)|=(2675704663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107923077/10000000000 : ℝ)|^2169 ≤ (6514801501603/50000000000000 : ℝ)^1657
        have hw : |(-2107923077/10000000000 : ℝ)|=(2107923077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234643263/10000000000 : ℝ)|^2169 ≤ (42857359150769/100000000000000 : ℝ)^1657
        have hw : |(5234643263/10000000000 : ℝ)|=(5234643263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s3_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351409363/10000000000 : ℝ)*x 0 + (5234643491/10000000000 : ℝ)*x 1 + (-84316909/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351409363/10000000000 : ℝ)^2169 ≤ (8822607645819/20000000000000 : ℝ)^1657 := by
    have hnat : (5351409363 : ℕ)^2169*20000000000000^1657 ≤ 8822607645819^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351409363 10000000000 8822607645819 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234643491/10000000000 : ℝ)^2169 ≤ (42857361594257/100000000000000 : ℝ)^1657 := by
    have hnat : (5234643491 : ℕ)^2169*100000000000000^1657 ≤ 42857361594257^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234643491 10000000000 42857361594257 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84316909/400000000 : ℝ)^2169 ≤ (130296001551/1000000000000 : ℝ)^1657 := by
    have hnat : (84316909 : ℕ)^2169*1000000000000^1657 ≤ 130296001551^1657*400000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84316909 400000000 130296001551 1000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351409363/10000000000 : ℝ), (5234643491/10000000000 : ℝ), (-84316909/400000000 : ℝ)] ![(8822607645819/20000000000000 : ℝ), (42857361594257/100000000000000 : ℝ), (130296001551/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351409363/10000000000 : ℝ)|^2169 ≤ (8822607645819/20000000000000 : ℝ)^1657
        have hw : |(5351409363/10000000000 : ℝ)|=(5351409363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234643491/10000000000 : ℝ)|^2169 ≤ (42857361594257/100000000000000 : ℝ)^1657
        have hw : |(5234643491/10000000000 : ℝ)|=(5234643491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84316909/400000000 : ℝ)|^2169 ≤ (130296001551/1000000000000 : ℝ)^1657
        have hw : |(-84316909/400000000 : ℝ)|=(84316909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s3_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863285419/2000000000 : ℝ)*x 0 + (1030238889/2500000000 : ℝ)*x 1 + (4520394173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863285419/2000000000 : ℝ)^2169 ≤ (33295130032639/100000000000000 : ℝ)^1657 := by
    have hnat : (863285419 : ℕ)^2169*100000000000000^1657 ≤ 33295130032639^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863285419 2000000000 33295130032639 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030238889/2500000000 : ℝ)^2169 ≤ (6267080995409/20000000000000 : ℝ)^1657 := by
    have hnat : (1030238889 : ℕ)^2169*20000000000000^1657 ≤ 6267080995409^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030238889 2500000000 6267080995409 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520394173/10000000000 : ℝ)^2169 ≤ (17684732488531/50000000000000 : ℝ)^1657 := by
    have hnat : (4520394173 : ℕ)^2169*50000000000000^1657 ≤ 17684732488531^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520394173 10000000000 17684732488531 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863285419/2000000000 : ℝ), (1030238889/2500000000 : ℝ), (4520394173/10000000000 : ℝ)] ![(33295130032639/100000000000000 : ℝ), (6267080995409/20000000000000 : ℝ), (17684732488531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863285419/2000000000 : ℝ)|^2169 ≤ (33295130032639/100000000000000 : ℝ)^1657
        have hw : |(863285419/2000000000 : ℝ)|=(863285419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030238889/2500000000 : ℝ)|^2169 ≤ (6267080995409/20000000000000 : ℝ)^1657
        have hw : |(1030238889/2500000000 : ℝ)|=(1030238889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520394173/10000000000 : ℝ)|^2169 ≤ (17684732488531/50000000000000 : ℝ)^1657
        have hw : |(4520394173/10000000000 : ℝ)|=(4520394173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s3_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2011864637/10000000000 : ℝ)*x 0 + (5235411979/10000000000 : ℝ)*x 1 + (5422019717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011864637/10000000000 : ℝ)^2169 ≤ (12257904586247/100000000000000 : ℝ)^1657 := by
    have hnat : (2011864637 : ℕ)^2169*100000000000000^1657 ≤ 12257904586247^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011864637 10000000000 12257904586247 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235411979/10000000000 : ℝ)^2169 ≤ (42865597707437/100000000000000 : ℝ)^1657 := by
    have hnat : (5235411979 : ℕ)^2169*100000000000000^1657 ≤ 42865597707437^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235411979 10000000000 42865597707437 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422019717/10000000000 : ℝ)^2169 ≤ (22438248844281/50000000000000 : ℝ)^1657 := by
    have hnat : (5422019717 : ℕ)^2169*50000000000000^1657 ≤ 22438248844281^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422019717 10000000000 22438248844281 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2011864637/10000000000 : ℝ), (5235411979/10000000000 : ℝ), (5422019717/10000000000 : ℝ)] ![(12257904586247/100000000000000 : ℝ), (42865597707437/100000000000000 : ℝ), (22438248844281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2011864637/10000000000 : ℝ)|^2169 ≤ (12257904586247/100000000000000 : ℝ)^1657
        have hw : |(-2011864637/10000000000 : ℝ)|=(2011864637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235411979/10000000000 : ℝ)|^2169 ≤ (42865597707437/100000000000000 : ℝ)^1657
        have hw : |(5235411979/10000000000 : ℝ)|=(5235411979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422019717/10000000000 : ℝ)|^2169 ≤ (22438248844281/50000000000000 : ℝ)^1657
        have hw : |(5422019717/10000000000 : ℝ)|=(5422019717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s3_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302751163/10000000000 : ℝ)*x 0 + (-384109101/2000000000 : ℝ)*x 1 + (2711010227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302751163/10000000000 : ℝ)^2169 ≤ (5448592244869/12500000000000 : ℝ)^1657 := by
    have hnat : (5302751163 : ℕ)^2169*12500000000000^1657 ≤ 5448592244869^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302751163 10000000000 5448592244869 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384109101/2000000000 : ℝ)^2169 ≤ (2306951271199/20000000000000 : ℝ)^1657 := by
    have hnat : (384109101 : ℕ)^2169*20000000000000^1657 ≤ 2306951271199^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384109101 2000000000 2306951271199 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711010227/5000000000 : ℝ)^2169 ≤ (11219126418333/25000000000000 : ℝ)^1657 := by
    have hnat : (2711010227 : ℕ)^2169*25000000000000^1657 ≤ 11219126418333^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711010227 5000000000 11219126418333 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302751163/10000000000 : ℝ), (-384109101/2000000000 : ℝ), (2711010227/5000000000 : ℝ)] ![(5448592244869/12500000000000 : ℝ), (2306951271199/20000000000000 : ℝ), (11219126418333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302751163/10000000000 : ℝ)|^2169 ≤ (5448592244869/12500000000000 : ℝ)^1657
        have hw : |(5302751163/10000000000 : ℝ)|=(5302751163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-384109101/2000000000 : ℝ)|^2169 ≤ (2306951271199/20000000000000 : ℝ)^1657
        have hw : |(-384109101/2000000000 : ℝ)|=(384109101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711010227/5000000000 : ℝ)|^2169 ≤ (11219126418333/25000000000000 : ℝ)^1657
        have hw : |(2711010227/5000000000 : ℝ)|=(2711010227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s3_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302752547/10000000000 : ℝ)*x 0 + (5422019389/10000000000 : ℝ)*x 1 + (-1920545079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302752547/10000000000 : ℝ)^2169 ≤ (21794376425359/50000000000000 : ℝ)^1657 := by
    have hnat : (5302752547 : ℕ)^2169*50000000000000^1657 ≤ 21794376425359^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302752547 10000000000 21794376425359 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422019389/10000000000 : ℝ)^2169 ≤ (560956176687/1250000000000 : ℝ)^1657 := by
    have hnat : (5422019389 : ℕ)^2169*1250000000000^1657 ≤ 560956176687^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422019389 10000000000 560956176687 1250000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920545079/10000000000 : ℝ)^2169 ≤ (11534753006877/100000000000000 : ℝ)^1657 := by
    have hnat : (1920545079 : ℕ)^2169*100000000000000^1657 ≤ 11534753006877^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920545079 10000000000 11534753006877 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302752547/10000000000 : ℝ), (5422019389/10000000000 : ℝ), (-1920545079/10000000000 : ℝ)] ![(21794376425359/50000000000000 : ℝ), (560956176687/1250000000000 : ℝ), (11534753006877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302752547/10000000000 : ℝ)|^2169 ≤ (21794376425359/50000000000000 : ℝ)^1657
        have hw : |(5302752547/10000000000 : ℝ)|=(5302752547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422019389/10000000000 : ℝ)|^2169 ≤ (560956176687/1250000000000 : ℝ)^1657
        have hw : |(5422019389/10000000000 : ℝ)|=(5422019389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1920545079/10000000000 : ℝ)|^2169 ≤ (11534753006877/100000000000000 : ℝ)^1657
        have hw : |(-1920545079/10000000000 : ℝ)|=(1920545079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s3_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4316465811/10000000000 : ℝ)*x 0 + (4518761359/10000000000 : ℝ)*x 1 + (3298077/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316465811/10000000000 : ℝ)^2169 ≤ (16647760474763/50000000000000 : ℝ)^1657 := by
    have hnat : (4316465811 : ℕ)^2169*50000000000000^1657 ≤ 16647760474763^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316465811 10000000000 16647760474763 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518761359/10000000000 : ℝ)^2169 ≤ (1104773201807/3125000000000 : ℝ)^1657 := by
    have hnat : (4518761359 : ℕ)^2169*3125000000000^1657 ≤ 1104773201807^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518761359 10000000000 1104773201807 3125000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3298077/8000000 : ℝ)^2169 ≤ (7837934144171/25000000000000 : ℝ)^1657 := by
    have hnat : (3298077 : ℕ)^2169*25000000000000^1657 ≤ 7837934144171^1657*8000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3298077 8000000 7837934144171 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316465811/10000000000 : ℝ), (4518761359/10000000000 : ℝ), (3298077/8000000 : ℝ)] ![(16647760474763/50000000000000 : ℝ), (1104773201807/3125000000000 : ℝ), (7837934144171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316465811/10000000000 : ℝ)|^2169 ≤ (16647760474763/50000000000000 : ℝ)^1657
        have hw : |(4316465811/10000000000 : ℝ)|=(4316465811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518761359/10000000000 : ℝ)|^2169 ≤ (1104773201807/3125000000000 : ℝ)^1657
        have hw : |(4518761359/10000000000 : ℝ)|=(4518761359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3298077/8000000 : ℝ)|^2169 ≤ (7837934144171/25000000000000 : ℝ)^1657
        have hw : |(3298077/8000000 : ℝ)|=(3298077/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5039/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2749/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14979/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5039/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5039/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5039/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5039/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5039/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5039/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5039/50000 : ℝ) ^ (4337/1024 : ℝ) ≤ (6010907060887549/100000000000000000000 : ℝ) := by
    have hpowers : (5039/50000 : ℝ)^4337 ≤ (6010907060887549/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5039 : ℕ)^4337*100000000000000000000^1024 ≤ 6010907060887549^1024*50000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5039 50000 6010907060887549 100000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5039/50000 : ℝ)) (X := (6010907060887549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15969/100000 : ℝ) ^ (4337/1024 : ℝ) ≤ (2639253265957827/6250000000000000000 : ℝ) := by
    have hpowers : (15969/100000 : ℝ)^4337 ≤ (2639253265957827/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15969 : ℕ)^4337*6250000000000000000^1024 ≤ 2639253265957827^1024*100000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15969 100000 2639253265957827 6250000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15969/100000 : ℝ)) (X := (2639253265957827/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006010907060887549/50000000000000000000 : ℝ) ≤ (400011353260271/400000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (50006010907060887549/50000000000000000000 : ℝ)^1024 ≤ (400011353260271/400000000000000 : ℝ)^4337 := by
      have hnat : (50006010907060887549 : ℕ)^1024*400000000000000^4337 ≤ 400011353260271^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006010907060887549 50000000000000000000 400011353260271 400000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400011353260271/400000000000000 : ℝ)) (X := (50006010907060887549/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048238959316212781/100000000000000000000 : ℝ) ≤ (10001138750189937/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (100048238959316212781/100000000000000000000 : ℝ)^1024 ≤ (10001138750189937/10000000000000000 : ℝ)^4337 := by
      have hnat : (100048238959316212781 : ℕ)^1024*10000000000000000^4337 ≤ 10001138750189937^4337*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048238959316212781 100000000000000000000 10001138750189937 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001138750189937/10000000000000000 : ℝ)) (X := (100048238959316212781/100000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127639253265957827/3125000000000000000 : ℝ) ≤ (10001993668873099/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (3127639253265957827/3125000000000000000 : ℝ)^1024 ≤ (10001993668873099/10000000000000000 : ℝ)^4337 := by
      have hnat : (3127639253265957827 : ℕ)^1024*10000000000000000^4337 ≤ 10001993668873099^4337*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127639253265957827 3125000000000000000 10001993668873099 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001993668873099/10000000000000000 : ℝ)) (X := (3127639253265957827/3125000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6010907060887549/100000000000000000000 : ℝ) ≤ ((58894440310428598253/58910000000000000000 : ℝ)+2*(427459341581/294550000000000 : ℝ)*(5039/50000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (58894440310428598253/58910000000000000000 : ℝ)+2*(427459341581/294550000000000 : ℝ)*(5039/50000 : ℝ)=(400011353260271/400000000000000 : ℝ) by norm_num, show 1+2*(6010907060887549/100000000000000000000 : ℝ)=(50006010907060887549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2639253265957827/6250000000000000000 : ℝ)+(6010907060887549/100000000000000000000 : ℝ) ≤ ((58894440310428598253/58910000000000000000 : ℝ)+(427459341581/294550000000000 : ℝ)*((15969/100000 : ℝ)+(5039/50000 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (58894440310428598253/58910000000000000000 : ℝ)+(427459341581/294550000000000 : ℝ)*((15969/100000 : ℝ)+(5039/50000 : ℝ))=(10001138750189937/10000000000000000 : ℝ) by norm_num, show 1+(2639253265957827/6250000000000000000 : ℝ)+(6010907060887549/100000000000000000000 : ℝ)=(100048238959316212781/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2639253265957827/6250000000000000000 : ℝ) ≤ ((58894440310428598253/58910000000000000000 : ℝ)+2*(427459341581/294550000000000 : ℝ)*(15969/100000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (58894440310428598253/58910000000000000000 : ℝ)+2*(427459341581/294550000000000 : ℝ)*(15969/100000 : ℝ)=(10001993668873099/10000000000000000 : ℝ) by norm_num, show 1+2*(2639253265957827/6250000000000000000 : ℝ)=(3127639253265957827/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58894440310428598253/58910000000000000000 : ℝ)*(X 1 0+X 2 0)+(427459341581/294550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (5039/50000 : ℝ)) (hi := (15969/100000 : ℝ)) (c := (58894440310428598253/58910000000000000000 : ℝ)) (alpha := (427459341581/294550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58894440310428598253/58910000000000000000 : ℝ)*(X 0 1+X 2 1)+(427459341581/294550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (5039/50000 : ℝ)) (hi := (15969/100000 : ℝ)) (c := (58894440310428598253/58910000000000000000 : ℝ)) (alpha := (427459341581/294550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58894440310428598253/58910000000000000000 : ℝ)*(X 0 2+X 1 2)+(427459341581/294550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (5039/50000 : ℝ)) (hi := (15969/100000 : ℝ)) (c := (58894440310428598253/58910000000000000000 : ℝ)) (alpha := (427459341581/294550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-502961573/2500000000 : ℝ)*X 0 0+(16946231/31250000 : ℝ)*X 0 1+(5234642969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675704663/5000000000 : ℝ)*X 1 0+(-2107923077/10000000000 : ℝ)*X 1 1+(5234643263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351409363/10000000000 : ℝ)*X 2 0+(5234643491/10000000000 : ℝ)*X 2 1+(-84316909/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863285419/2000000000 : ℝ)*X 0 0+(1030238889/2500000000 : ℝ)*X 0 1+(4520394173/10000000000 : ℝ)*X 0 2+(863285419/2000000000 : ℝ)*X 1 0+(1030238889/2500000000 : ℝ)*X 1 1+(4520394173/10000000000 : ℝ)*X 1 2+(863285419/2000000000 : ℝ)*X 2 0+(1030238889/2500000000 : ℝ)*X 2 1+(4520394173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2011864637/10000000000 : ℝ)*X 0 0+(5235411979/10000000000 : ℝ)*X 0 1+(5422019717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302751163/10000000000 : ℝ)*X 1 0+(-384109101/2000000000 : ℝ)*X 1 1+(2711010227/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302752547/10000000000 : ℝ)*X 2 0+(5422019389/10000000000 : ℝ)*X 2 1+(-1920545079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316465811/10000000000 : ℝ)*X 0 0+(4518761359/10000000000 : ℝ)*X 0 1+(3298077/8000000 : ℝ)*X 0 2+(4316465811/10000000000 : ℝ)*X 1 0+(4518761359/10000000000 : ℝ)*X 1 1+(3298077/8000000 : ℝ)*X 1 2+(4316465811/10000000000 : ℝ)*X 2 0+(4518761359/10000000000 : ℝ)*X 2 1+(3298077/8000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32194379135958753149824923387/2945500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35428257/4000000000000 : ℝ)*(base19) + (382353419/100000000000000 : ℝ)*(base23) + (289030013/100000000000000 : ℝ)*(lower2) + (127337407/100000000000000 : ℝ)*(upper3) + (1171333/1000000000000 : ℝ)*(upper5) + (3909223647600431/100000000000000 : ℝ)*(major0) + (3909223647600431/100000000000000 : ℝ)*(major1) + (3909223647600431/100000000000000 : ℝ)*(major2) + (1328724889886951/25000000000000 : ℝ)*(sp0) + (332182671410781/6250000000000 : ℝ)*(sp1) + (2657461622962751/50000000000000 : ℝ)*(sp2) + (2503517272604037/100000000000000 : ℝ)*(sp3) + (24068731117/100000000000000 : ℝ)*(sp4) + (602998383/10000000000000 : ℝ)*(sp7) + (1251761651293933/50000000000000 : ℝ)*(f.failure) + (5314923628278921/100000000000000 : ℝ)*(f.sum) + (50133227818759/14727500000000000000000000000 : ℝ)*base66 + (91471504545964152957/5891000000000000000000000000000000 : ℝ)*base68 + (82255807361955152957/5891000000000000000000000000000000 : ℝ)*base70 + (103483309958180152957/5891000000000000000000000000000000 : ℝ)*base72 + (20906448634107/7363750000000000000000000000 : ℝ)*base74 + (28659904577308152957/5891000000000000000000000000000000 : ℝ)*base76 + (107476097387410152957/5891000000000000000000000000000000 : ℝ)*base78 + (47658990326733152957/5891000000000000000000000000000000 : ℝ)*base80 + (159877914768883/29455000000000000000000000000 : ℝ)*base82 + (29333547/2500000000000000000000 : ℝ)*base90 + (29333547/2500000000000000000000 : ℝ)*base92 + (29333547/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1670474626016423349257384667/736375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (456963977/20000000000000 : ℝ)*(base19) + (4287726737/100000000000000 : ℝ)*(base23) + (262626861/50000000000000 : ℝ)*(upper3) + (174685007/100000000000000 : ℝ)*(lower4) + (30985053/10000000000000 : ℝ)*(upper5) + (985380182885787/25000000000000 : ℝ)*(major0) + (985380182885787/25000000000000 : ℝ)*(major1) + (985380182885787/25000000000000 : ℝ)*(major2) + (3054261337/6250000000000 : ℝ)*(sp1) + (78823106627/100000000000000 : ℝ)*(sp2) + (1339708641427767/25000000000000 : ℝ)*(sp4) + (535878341270979/10000000000000 : ℝ)*(sp5) + (669843931859713/12500000000000 : ℝ)*(sp6) + (252420682175819/10000000000000 : ℝ)*(sp7) + (252420682175819/10000000000000 : ℝ)*(f.failure) + (1339708641427767/25000000000000 : ℝ)*(f.sum) + (8758410015403/14727500000000000000000000000 : ℝ)*base65 + (1589058694284369889/1472750000000000000000000000000000 : ℝ)*base68 + (9258332852617869889/1472750000000000000000000000000000 : ℝ)*base70 + (8801743555673130111/1472750000000000000000000000000000 : ℝ)*base71 + (22306524617599/7363750000000000000000000000 : ℝ)*base73 + (4261984900132130111/1472750000000000000000000000000000 : ℝ)*base75 + (7001729172883880111/1472750000000000000000000000000000 : ℝ)*base77 + (2716917474557880111/1472750000000000000000000000000000 : ℝ)*base79 + (140938261622381/29455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7857821/500000000000000000000 : ℝ)*base90 + (7857821/500000000000000000000 : ℝ)*base92 + (7857821/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1378_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5039/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14979/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1378_s4_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013045251/10000000000 : ℝ)*x 0 + (5412833277/10000000000 : ℝ)*x 1 + (5243815227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013045251/10000000000 : ℝ)^2169 ≤ (12267321353123/100000000000000 : ℝ)^1657 := by
    have hnat : (2013045251 : ℕ)^2169*100000000000000^1657 ≤ 12267321353123^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013045251 10000000000 12267321353123 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412833277/10000000000 : ℝ)^2169 ≤ (22388498233863/50000000000000 : ℝ)^1657 := by
    have hnat : (5412833277 : ℕ)^2169*50000000000000^1657 ≤ 22388498233863^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412833277 10000000000 22388498233863 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243815227/10000000000 : ℝ)^2169 ≤ (42955682169257/100000000000000 : ℝ)^1657 := by
    have hnat : (5243815227 : ℕ)^2169*100000000000000^1657 ≤ 42955682169257^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243815227 10000000000 42955682169257 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013045251/10000000000 : ℝ), (5412833277/10000000000 : ℝ), (5243815227/10000000000 : ℝ)] ![(12267321353123/100000000000000 : ℝ), (22388498233863/50000000000000 : ℝ), (42955682169257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013045251/10000000000 : ℝ)|^2169 ≤ (12267321353123/100000000000000 : ℝ)^1657
        have hw : |(-2013045251/10000000000 : ℝ)|=(2013045251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412833277/10000000000 : ℝ)|^2169 ≤ (22388498233863/50000000000000 : ℝ)^1657
        have hw : |(5412833277/10000000000 : ℝ)|=(5412833277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243815227/10000000000 : ℝ)|^2169 ≤ (42955682169257/100000000000000 : ℝ)^1657
        have hw : |(5243815227/10000000000 : ℝ)|=(5243815227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s4_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (83575889/156250000 : ℝ)*x 0 + (-209916927/1000000000 : ℝ)*x 1 + (2621907613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83575889/156250000 : ℝ)^2169 ≤ (44085498227077/100000000000000 : ℝ)^1657 := by
    have hnat : (83575889 : ℕ)^2169*100000000000000^1657 ≤ 44085498227077^1657*156250000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83575889 156250000 44085498227077 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209916927/1000000000 : ℝ)^2169 ≤ (1619852450007/12500000000000 : ℝ)^1657 := by
    have hnat : (209916927 : ℕ)^2169*12500000000000^1657 ≤ 1619852450007^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209916927 1000000000 1619852450007 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621907613/5000000000 : ℝ)^2169 ≤ (21477841079267/50000000000000 : ℝ)^1657 := by
    have hnat : (2621907613 : ℕ)^2169*50000000000000^1657 ≤ 21477841079267^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621907613 5000000000 21477841079267 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83575889/156250000 : ℝ), (-209916927/1000000000 : ℝ), (2621907613/5000000000 : ℝ)] ![(44085498227077/100000000000000 : ℝ), (1619852450007/12500000000000 : ℝ), (21477841079267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83575889/156250000 : ℝ)|^2169 ≤ (44085498227077/100000000000000 : ℝ)^1657
        have hw : |(83575889/156250000 : ℝ)|=(83575889/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209916927/1000000000 : ℝ)|^2169 ≤ (1619852450007/12500000000000 : ℝ)^1657
        have hw : |(-209916927/1000000000 : ℝ)|=(209916927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621907613/5000000000 : ℝ)|^2169 ≤ (21477841079267/50000000000000 : ℝ)^1657
        have hw : |(2621907613/5000000000 : ℝ)|=(2621907613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s4_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337214223/2500000000 : ℝ)*x 0 + (209752609/400000000 : ℝ)*x 1 + (-2099169277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337214223/2500000000 : ℝ)^2169 ≤ (22042749091961/50000000000000 : ℝ)^1657 := by
    have hnat : (1337214223 : ℕ)^2169*50000000000000^1657 ≤ 22042749091961^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337214223 2500000000 22042749091961 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209752609/400000000 : ℝ)^2169 ≤ (42955682147811/100000000000000 : ℝ)^1657 := by
    have hnat : (209752609 : ℕ)^2169*100000000000000^1657 ≤ 42955682147811^1657*400000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209752609 400000000 42955682147811 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099169277/10000000000 : ℝ)^2169 ≤ (12958819656621/100000000000000 : ℝ)^1657 := by
    have hnat : (2099169277 : ℕ)^2169*100000000000000^1657 ≤ 12958819656621^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099169277 10000000000 12958819656621 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337214223/2500000000 : ℝ), (209752609/400000000 : ℝ), (-2099169277/10000000000 : ℝ)] ![(22042749091961/50000000000000 : ℝ), (42955682147811/100000000000000 : ℝ), (12958819656621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337214223/2500000000 : ℝ)|^2169 ≤ (22042749091961/50000000000000 : ℝ)^1657
        have hw : |(1337214223/2500000000 : ℝ)|=(1337214223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209752609/400000000 : ℝ)|^2169 ≤ (42955682147811/100000000000000 : ℝ)^1657
        have hw : |(209752609/400000000 : ℝ)|=(209752609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099169277/10000000000 : ℝ)|^2169 ≤ (12958819656621/100000000000000 : ℝ)^1657
        have hw : |(-2099169277/10000000000 : ℝ)|=(2099169277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s4_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4317156871/10000000000 : ℝ)*x 0 + (4141174707/10000000000 : ℝ)*x 1 + (899999251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317156871/10000000000 : ℝ)^2169 ≤ (33302498790217/100000000000000 : ℝ)^1657 := by
    have hnat : (4317156871 : ℕ)^2169*100000000000000^1657 ≤ 33302498790217^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317156871 10000000000 33302498790217 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4141174707/10000000000 : ℝ)^2169 ≤ (6307361606041/20000000000000 : ℝ)^1657 := by
    have hnat : (4141174707 : ℕ)^2169*20000000000000^1657 ≤ 6307361606041^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141174707 10000000000 6307361606041 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899999251/2000000000 : ℝ)^2169 ≤ (17580346578077/50000000000000 : ℝ)^1657 := by
    have hnat : (899999251 : ℕ)^2169*50000000000000^1657 ≤ 17580346578077^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899999251 2000000000 17580346578077 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317156871/10000000000 : ℝ), (4141174707/10000000000 : ℝ), (899999251/2000000000 : ℝ)] ![(33302498790217/100000000000000 : ℝ), (6307361606041/20000000000000 : ℝ), (17580346578077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317156871/10000000000 : ℝ)|^2169 ≤ (33302498790217/100000000000000 : ℝ)^1657
        have hw : |(4317156871/10000000000 : ℝ)|=(4317156871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4141174707/10000000000 : ℝ)|^2169 ≤ (6307361606041/20000000000000 : ℝ)^1657
        have hw : |(4141174707/10000000000 : ℝ)|=(4141174707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899999251/2000000000 : ℝ)|^2169 ≤ (17580346578077/50000000000000 : ℝ)^1657
        have hw : |(899999251/2000000000 : ℝ)|=(899999251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s4_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-402611603/2000000000 : ℝ)*x 0 + (1048887203/2000000000 : ℝ)*x 1 + (5412209119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402611603/2000000000 : ℝ)^2169 ≤ (12267423170163/100000000000000 : ℝ)^1657 := by
    have hnat : (402611603 : ℕ)^2169*100000000000000^1657 ≤ 12267423170163^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402611603 2000000000 12267423170163 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048887203/2000000000 : ℝ)^2169 ≤ (42962338908419/100000000000000 : ℝ)^1657 := by
    have hnat : (1048887203 : ℕ)^2169*100000000000000^1657 ≤ 42962338908419^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048887203 2000000000 42962338908419 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412209119/10000000000 : ℝ)^2169 ≤ (44770237907999/100000000000000 : ℝ)^1657 := by
    have hnat : (5412209119 : ℕ)^2169*100000000000000^1657 ≤ 44770237907999^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412209119 10000000000 44770237907999 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402611603/2000000000 : ℝ), (1048887203/2000000000 : ℝ), (5412209119/10000000000 : ℝ)] ![(12267423170163/100000000000000 : ℝ), (42962338908419/100000000000000 : ℝ), (44770237907999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402611603/2000000000 : ℝ)|^2169 ≤ (12267423170163/100000000000000 : ℝ)^1657
        have hw : |(-402611603/2000000000 : ℝ)|=(402611603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048887203/2000000000 : ℝ)|^2169 ≤ (42962338908419/100000000000000 : ℝ)^1657
        have hw : |(1048887203/2000000000 : ℝ)|=(1048887203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412209119/10000000000 : ℝ)|^2169 ≤ (44770237907999/100000000000000 : ℝ)^1657
        have hw : |(5412209119/10000000000 : ℝ)|=(5412209119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s4_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305146529/10000000000 : ℝ)*x 0 + (-1930775251/10000000000 : ℝ)*x 1 + (541220929/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305146529/10000000000 : ℝ)^2169 ≤ (43614513766253/100000000000000 : ℝ)^1657 := by
    have hnat : (5305146529 : ℕ)^2169*100000000000000^1657 ≤ 43614513766253^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305146529 10000000000 43614513766253 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930775251/10000000000 : ℝ)^2169 ≤ (11615246466477/100000000000000 : ℝ)^1657 := by
    have hnat : (1930775251 : ℕ)^2169*100000000000000^1657 ≤ 11615246466477^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930775251 10000000000 11615246466477 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541220929/1000000000 : ℝ)^2169 ≤ (44770239759603/100000000000000 : ℝ)^1657 := by
    have hnat : (541220929 : ℕ)^2169*100000000000000^1657 ≤ 44770239759603^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541220929 1000000000 44770239759603 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305146529/10000000000 : ℝ), (-1930775251/10000000000 : ℝ), (541220929/1000000000 : ℝ)] ![(43614513766253/100000000000000 : ℝ), (11615246466477/100000000000000 : ℝ), (44770239759603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305146529/10000000000 : ℝ)|^2169 ≤ (43614513766253/100000000000000 : ℝ)^1657
        have hw : |(5305146529/10000000000 : ℝ)|=(5305146529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930775251/10000000000 : ℝ)|^2169 ≤ (11615246466477/100000000000000 : ℝ)^1657
        have hw : |(-1930775251/10000000000 : ℝ)|=(1930775251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541220929/1000000000 : ℝ)|^2169 ≤ (44770239759603/100000000000000 : ℝ)^1657
        have hw : |(541220929/1000000000 : ℝ)|=(541220929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s4_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663143313/1250000000 : ℝ)*x 0 + (1082441843/2000000000 : ℝ)*x 1 + (-482693847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663143313/1250000000 : ℝ)^2169 ≤ (43614513497217/100000000000000 : ℝ)^1657 := by
    have hnat : (663143313 : ℕ)^2169*100000000000000^1657 ≤ 43614513497217^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663143313 1250000000 43614513497217 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082441843/2000000000 : ℝ)^2169 ≤ (5596279868437/12500000000000 : ℝ)^1657 := by
    have hnat : (1082441843 : ℕ)^2169*12500000000000^1657 ≤ 5596279868437^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082441843 2000000000 5596279868437 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482693847/2500000000 : ℝ)^2169 ≤ (11615247545311/100000000000000 : ℝ)^1657 := by
    have hnat : (482693847 : ℕ)^2169*100000000000000^1657 ≤ 11615247545311^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482693847 2500000000 11615247545311 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663143313/1250000000 : ℝ), (1082441843/2000000000 : ℝ), (-482693847/2500000000 : ℝ)] ![(43614513497217/100000000000000 : ℝ), (5596279868437/12500000000000 : ℝ), (11615247545311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663143313/1250000000 : ℝ)|^2169 ≤ (43614513497217/100000000000000 : ℝ)^1657
        have hw : |(663143313/1250000000 : ℝ)|=(663143313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082441843/2000000000 : ℝ)|^2169 ≤ (5596279868437/12500000000000 : ℝ)^1657
        have hw : |(1082441843/2000000000 : ℝ)|=(1082441843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482693847/2500000000 : ℝ)|^2169 ≤ (11615247545311/100000000000000 : ℝ)^1657
        have hw : |(-482693847/2500000000 : ℝ)|=(482693847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s4_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863436759/2000000000 : ℝ)*x 0 + (4498678139/10000000000 : ℝ)*x 1 + (4142499707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863436759/2000000000 : ℝ)^2169 ≤ (33302770656929/100000000000000 : ℝ)^1657 := by
    have hnat : (863436759 : ℕ)^2169*100000000000000^1657 ≤ 33302770656929^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863436759 2000000000 33302770656929 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498678139/10000000000 : ℝ)^2169 ≤ (35147212336593/100000000000000 : ℝ)^1657 := by
    have hnat : (4498678139 : ℕ)^2169*100000000000000^1657 ≤ 35147212336593^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498678139 10000000000 35147212336593 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4142499707/10000000000 : ℝ)^2169 ≤ (15775008494259/50000000000000 : ℝ)^1657 := by
    have hnat : (4142499707 : ℕ)^2169*50000000000000^1657 ≤ 15775008494259^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142499707 10000000000 15775008494259 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863436759/2000000000 : ℝ), (4498678139/10000000000 : ℝ), (4142499707/10000000000 : ℝ)] ![(33302770656929/100000000000000 : ℝ), (35147212336593/100000000000000 : ℝ), (15775008494259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863436759/2000000000 : ℝ)|^2169 ≤ (33302770656929/100000000000000 : ℝ)^1657
        have hw : |(863436759/2000000000 : ℝ)|=(863436759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498678139/10000000000 : ℝ)|^2169 ≤ (35147212336593/100000000000000 : ℝ)^1657
        have hw : |(4498678139/10000000000 : ℝ)|=(4498678139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4142499707/10000000000 : ℝ)|^2169 ≤ (15775008494259/50000000000000 : ℝ)^1657
        have hw : |(4142499707/10000000000 : ℝ)|=(4142499707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1399/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2749/25000 : ℝ) ^ (4337/1024 : ℝ) ≤ (8695449167362313/100000000000000000000 : ℝ) := by
    have hpowers : (2749/25000 : ℝ)^4337 ≤ (8695449167362313/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2749 : ℕ)^4337*100000000000000000000^1024 ≤ 8695449167362313^1024*25000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2749 25000 8695449167362313 100000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2749/25000 : ℝ)) (X := (8695449167362313/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14979/100000 : ℝ) ^ (4337/1024 : ℝ) ≤ (16100889927516749/50000000000000000000 : ℝ) := by
    have hpowers : (14979/100000 : ℝ)^4337 ≤ (16100889927516749/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14979 : ℕ)^4337*50000000000000000000^1024 ≤ 16100889927516749^1024*100000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14979 100000 16100889927516749 50000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14979/100000 : ℝ)) (X := (16100889927516749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008695449167362313/50000000000000000000 : ℝ) ≤ (1250051323198989/1250000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (50008695449167362313/50000000000000000000 : ℝ)^1024 ≤ (1250051323198989/1250000000000000 : ℝ)^4337 := by
      have hnat : (50008695449167362313 : ℕ)^1024*1250000000000000^4337 ≤ 1250051323198989^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008695449167362313 50000000000000000000 1250051323198989 1250000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250051323198989/1250000000000000 : ℝ)) (X := (50008695449167362313/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040897229022395811/100000000000000000000 : ℝ) ≤ (2500241366280867/2500000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (100040897229022395811/100000000000000000000 : ℝ)^1024 ≤ (2500241366280867/2500000000000000 : ℝ)^4337 := by
      have hnat : (100040897229022395811 : ℕ)^1024*2500000000000000^4337 ≤ 2500241366280867^4337*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040897229022395811 100000000000000000000 2500241366280867 2500000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500241366280867/2500000000000000 : ℝ)) (X := (100040897229022395811/100000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016100889927516749/25000000000000000000 : ℝ) ≤ (625095021540939/625000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (25016100889927516749/25000000000000000000 : ℝ)^1024 ≤ (625095021540939/625000000000000 : ℝ)^4337 := by
      have hnat : (25016100889927516749 : ℕ)^1024*625000000000000^4337 ≤ 625095021540939^4337*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016100889927516749 25000000000000000000 625095021540939 625000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625095021540939/625000000000000 : ℝ)) (X := (25016100889927516749/25000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8695449167362313/100000000000000000000 : ℝ) ≤ ((711061293781332249/711250000000000000 : ℝ)+2*(19817126127/14225000000000 : ℝ)*(2749/25000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (711061293781332249/711250000000000000 : ℝ)+2*(19817126127/14225000000000 : ℝ)*(2749/25000 : ℝ)=(1250051323198989/1250000000000000 : ℝ) by norm_num, show 1+2*(8695449167362313/100000000000000000000 : ℝ)=(50008695449167362313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16100889927516749/50000000000000000000 : ℝ)+(8695449167362313/100000000000000000000 : ℝ) ≤ ((711061293781332249/711250000000000000 : ℝ)+(19817126127/14225000000000 : ℝ)*((14979/100000 : ℝ)+(2749/25000 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (711061293781332249/711250000000000000 : ℝ)+(19817126127/14225000000000 : ℝ)*((14979/100000 : ℝ)+(2749/25000 : ℝ))=(2500241366280867/2500000000000000 : ℝ) by norm_num, show 1+(16100889927516749/50000000000000000000 : ℝ)+(8695449167362313/100000000000000000000 : ℝ)=(100040897229022395811/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16100889927516749/50000000000000000000 : ℝ) ≤ ((711061293781332249/711250000000000000 : ℝ)+2*(19817126127/14225000000000 : ℝ)*(14979/100000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (711061293781332249/711250000000000000 : ℝ)+2*(19817126127/14225000000000 : ℝ)*(14979/100000 : ℝ)=(625095021540939/625000000000000 : ℝ) by norm_num, show 1+2*(16100889927516749/50000000000000000000 : ℝ)=(25016100889927516749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (711061293781332249/711250000000000000 : ℝ)*(X 1 0+X 2 0)+(19817126127/14225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (14979/100000 : ℝ)) (c := (711061293781332249/711250000000000000 : ℝ)) (alpha := (19817126127/14225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (711061293781332249/711250000000000000 : ℝ)*(X 0 1+X 2 1)+(19817126127/14225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (14979/100000 : ℝ)) (c := (711061293781332249/711250000000000000 : ℝ)) (alpha := (19817126127/14225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (711061293781332249/711250000000000000 : ℝ)*(X 0 2+X 1 2)+(19817126127/14225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (14979/100000 : ℝ)) (c := (711061293781332249/711250000000000000 : ℝ)) (alpha := (19817126127/14225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2013045251/10000000000 : ℝ)*X 0 0+(5412833277/10000000000 : ℝ)*X 0 1+(5243815227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83575889/156250000 : ℝ)*X 1 0+(-209916927/1000000000 : ℝ)*X 1 1+(2621907613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337214223/2500000000 : ℝ)*X 2 0+(209752609/400000000 : ℝ)*X 2 1+(-2099169277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317156871/10000000000 : ℝ)*X 0 0+(4141174707/10000000000 : ℝ)*X 0 1+(899999251/2000000000 : ℝ)*X 0 2+(4317156871/10000000000 : ℝ)*X 1 0+(4141174707/10000000000 : ℝ)*X 1 1+(899999251/2000000000 : ℝ)*X 1 2+(4317156871/10000000000 : ℝ)*X 2 0+(4141174707/10000000000 : ℝ)*X 2 1+(899999251/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-402611603/2000000000 : ℝ)*X 0 0+(1048887203/2000000000 : ℝ)*X 0 1+(5412209119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305146529/10000000000 : ℝ)*X 1 0+(-1930775251/10000000000 : ℝ)*X 1 1+(541220929/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663143313/1250000000 : ℝ)*X 2 0+(1082441843/2000000000 : ℝ)*X 2 1+(-482693847/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863436759/2000000000 : ℝ)*X 0 0+(4498678139/10000000000 : ℝ)*X 0 1+(4142499707/10000000000 : ℝ)*X 0 2+(863436759/2000000000 : ℝ)*X 1 0+(4498678139/10000000000 : ℝ)*X 1 1+(4142499707/10000000000 : ℝ)*X 1 2+(863436759/2000000000 : ℝ)*X 2 0+(4498678139/10000000000 : ℝ)*X 2 1+(4142499707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117305235820594757478378591/17781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306797331/25000000000000 : ℝ)*(base19) + (1139157221/100000000000000 : ℝ)*(base23) + (44720481/100000000000000 : ℝ)*(lower2) + (8442651/5000000000000 : ℝ)*(upper3) + (1226103/1250000000000 : ℝ)*(upper5) + (4351751716085697/100000000000000 : ℝ)*(major0) + (4351751716085697/100000000000000 : ℝ)*(major1) + (4351751716085697/100000000000000 : ℝ)*(major2) + (5916553942351153/100000000000000 : ℝ)*(sp0) + (5916577313989939/100000000000000 : ℝ)*(sp1) + (5916577402022043/100000000000000 : ℝ)*(sp2) + (170099605427/6103515625 : ℝ)*(sp3) + (24598828111/100000000000000 : ℝ)*(sp4) + (12735771781/100000000000000 : ℝ)*(sp7) + (696731167771937/25000000000000 : ℝ)*(f.failure) + (5916578541179263/100000000000000 : ℝ)*(f.sum) + (3399478205101/2845000000000000000000000000 : ℝ)*base65 + (313578747616067553/71125000000000000000000000000000 : ℝ)*base67 + (744278605784317553/71125000000000000000000000000000 : ℝ)*base69 + (676976189036817553/71125000000000000000000000000000 : ℝ)*base71 + (14788098820149/2845000000000000000000000000 : ℝ)*base74 + (1484770918796067553/71125000000000000000000000000000 : ℝ)*base75 + (183247704558317553/71125000000000000000000000000000 : ℝ)*base77 + (551903583621557447/71125000000000000000000000000000 : ℝ)*base80 + (2940292181511/711250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (15737783/1250000000000000000000 : ℝ)*base90 + (15737783/1250000000000000000000 : ℝ)*base92 + (15737783/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (366321351691517445973773459/35562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (478879129/25000000000000 : ℝ)*(base19) + (1885037511/100000000000000 : ℝ)*(base23) + (244328461/100000000000000 : ℝ)*(upper3) + (10404731/50000000000000 : ℝ)*(lower4) + (2157821/800000000000 : ℝ)*(upper5) + (4384006004512903/100000000000000 : ℝ)*(major0) + (4384006004512903/100000000000000 : ℝ)*(major1) + (4384006004512903/100000000000000 : ℝ)*(major2) + (8746077809/20000000000000 : ℝ)*(sp1) + (9669851609/25000000000000 : ℝ)*(sp2) + (2980215441137471/50000000000000 : ℝ)*(sp4) + (2980192618184691/50000000000000 : ℝ)*(sp5) + (1490097579457749/25000000000000 : ℝ)*(sp6) + (56151615667833/2000000000000 : ℝ)*(sp7) + (56151615667833/2000000000000 : ℝ)*(f.failure) + (2980215441137471/50000000000000 : ℝ)*(f.sum) + (1254729043261/177812500000000000000000000 : ℝ)*base66 + (184616901969558847/71125000000000000000000000000000 : ℝ)*base67 + (702302549645558847/71125000000000000000000000000000 : ℝ)*base69 + (295726899916941153/71125000000000000000000000000000 : ℝ)*base72 + (11133407276493/1422500000000000000000000000 : ℝ)*base74 + (837479862077941153/71125000000000000000000000000000 : ℝ)*base76 + (318102085287808847/71125000000000000000000000000000 : ℝ)*base77 + (1076042166645808847/71125000000000000000000000000000 : ℝ)*base79 + (9798997028563/1422500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (156353/100000000000000000000 : ℝ)*base89 + (156353/100000000000000000000 : ℝ)*base91 + (156353/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1378_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1378_s5_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006619553/5000000000 : ℝ)*x 0 + (5411134839/10000000000 : ℝ)*x 1 + (209815441/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006619553/5000000000 : ℝ)^2169 ≤ (3067216933719/25000000000000 : ℝ)^1657 := by
    have hnat : (1006619553 : ℕ)^2169*25000000000000^1657 ≤ 3067216933719^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006619553 5000000000 3067216933719 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411134839/10000000000 : ℝ)^2169 ≤ (44758605863669/100000000000000 : ℝ)^1657 := by
    have hnat : (5411134839 : ℕ)^2169*100000000000000^1657 ≤ 44758605863669^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411134839 10000000000 44758605863669 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209815441/400000000 : ℝ)^2169 ≤ (42972526382097/100000000000000 : ℝ)^1657 := by
    have hnat : (209815441 : ℕ)^2169*100000000000000^1657 ≤ 42972526382097^1657*400000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209815441 400000000 42972526382097 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006619553/5000000000 : ℝ), (5411134839/10000000000 : ℝ), (209815441/400000000 : ℝ)] ![(3067216933719/25000000000000 : ℝ), (44758605863669/100000000000000 : ℝ), (42972526382097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006619553/5000000000 : ℝ)|^2169 ≤ (3067216933719/25000000000000 : ℝ)^1657
        have hw : |(-1006619553/5000000000 : ℝ)|=(1006619553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411134839/10000000000 : ℝ)|^2169 ≤ (44758605863669/100000000000000 : ℝ)^1657
        have hw : |(5411134839/10000000000 : ℝ)|=(5411134839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209815441/400000000 : ℝ)|^2169 ≤ (42972526382097/100000000000000 : ℝ)^1657
        have hw : |(209815441/400000000 : ℝ)|=(209815441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s5_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348420913/10000000000 : ℝ)*x 0 + (-2097666753/10000000000 : ℝ)*x 1 + (655673249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348420913/10000000000 : ℝ)^2169 ≤ (8816158913453/20000000000000 : ℝ)^1657 := by
    have hnat : (5348420913 : ℕ)^2169*20000000000000^1657 ≤ 8816158913453^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348420913 10000000000 8816158913453 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097666753/10000000000 : ℝ)^2169 ≤ (6473339692419/50000000000000 : ℝ)^1657 := by
    have hnat : (2097666753 : ℕ)^2169*50000000000000^1657 ≤ 6473339692419^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097666753 10000000000 6473339692419 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655673249/1250000000 : ℝ)^2169 ≤ (4297252602821/10000000000000 : ℝ)^1657 := by
    have hnat : (655673249 : ℕ)^2169*10000000000000^1657 ≤ 4297252602821^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655673249 1250000000 4297252602821 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348420913/10000000000 : ℝ), (-2097666753/10000000000 : ℝ), (655673249/1250000000 : ℝ)] ![(8816158913453/20000000000000 : ℝ), (6473339692419/50000000000000 : ℝ), (4297252602821/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348420913/10000000000 : ℝ)|^2169 ≤ (8816158913453/20000000000000 : ℝ)^1657
        have hw : |(5348420913/10000000000 : ℝ)|=(5348420913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097666753/10000000000 : ℝ)|^2169 ≤ (6473339692419/50000000000000 : ℝ)^1657
        have hw : |(-2097666753/10000000000 : ℝ)|=(2097666753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655673249/1250000000 : ℝ)|^2169 ≤ (4297252602821/10000000000000 : ℝ)^1657
        have hw : |(655673249/1250000000 : ℝ)|=(655673249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s5_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348420959/10000000000 : ℝ)*x 0 + (5245386023/10000000000 : ℝ)*x 1 + (-524416663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348420959/10000000000 : ℝ)^2169 ≤ (8816159012707/20000000000000 : ℝ)^1657 := by
    have hnat : (5348420959 : ℕ)^2169*20000000000000^1657 ≤ 8816159012707^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348420959 10000000000 8816159012707 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245386023/10000000000 : ℝ)^2169 ≤ (42972526360649/100000000000000 : ℝ)^1657 := by
    have hnat : (5245386023 : ℕ)^2169*100000000000000^1657 ≤ 42972526360649^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245386023 10000000000 42972526360649 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524416663/2500000000 : ℝ)^2169 ≤ (12946678568857/100000000000000 : ℝ)^1657 := by
    have hnat : (524416663 : ℕ)^2169*100000000000000^1657 ≤ 12946678568857^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524416663 2500000000 12946678568857 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348420959/10000000000 : ℝ), (5245386023/10000000000 : ℝ), (-524416663/2500000000 : ℝ)] ![(8816159012707/20000000000000 : ℝ), (42972526360649/100000000000000 : ℝ), (12946678568857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348420959/10000000000 : ℝ)|^2169 ≤ (8816159012707/20000000000000 : ℝ)^1657
        have hw : |(5348420959/10000000000 : ℝ)|=(5348420959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245386023/10000000000 : ℝ)|^2169 ≤ (42972526360649/100000000000000 : ℝ)^1657
        have hw : |(5245386023/10000000000 : ℝ)|=(5245386023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524416663/2500000000 : ℝ)|^2169 ≤ (12946678568857/100000000000000 : ℝ)^1657
        have hw : |(-524416663/2500000000 : ℝ)|=(524416663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s5_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (86345469/200000000 : ℝ)*x 0 + (1036157811/2500000000 : ℝ)*x 1 + (2248255697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86345469/200000000 : ℝ)^2169 ≤ (33303675957471/100000000000000 : ℝ)^1657 := by
    have hnat : (86345469 : ℕ)^2169*100000000000000^1657 ≤ 33303675957471^1657*200000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86345469 200000000 33303675957471 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036157811/2500000000 : ℝ)^2169 ≤ (7892817268447/25000000000000 : ℝ)^1657 := by
    have hnat : (1036157811 : ℕ)^2169*25000000000000^1657 ≤ 7892817268447^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036157811 2500000000 7892817268447 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248255697/5000000000 : ℝ)^2169 ≤ (17562527476201/50000000000000 : ℝ)^1657 := by
    have hnat : (2248255697 : ℕ)^2169*50000000000000^1657 ≤ 17562527476201^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248255697 5000000000 17562527476201 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86345469/200000000 : ℝ), (1036157811/2500000000 : ℝ), (2248255697/5000000000 : ℝ)] ![(33303675957471/100000000000000 : ℝ), (7892817268447/25000000000000 : ℝ), (17562527476201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86345469/200000000 : ℝ)|^2169 ≤ (33303675957471/100000000000000 : ℝ)^1657
        have hw : |(86345469/200000000 : ℝ)|=(86345469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036157811/2500000000 : ℝ)|^2169 ≤ (7892817268447/25000000000000 : ℝ)^1657
        have hw : |(1036157811/2500000000 : ℝ)|=(1036157811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248255697/5000000000 : ℝ)|^2169 ≤ (17562527476201/50000000000000 : ℝ)^1657
        have hw : |(2248255697/5000000000 : ℝ)|=(2248255697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s5_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013251069/10000000000 : ℝ)*x 0 + (5245983171/10000000000 : ℝ)*x 1 + (1352633643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013251069/10000000000 : ℝ)^2169 ≤ (613448158263/5000000000000 : ℝ)^1657 := by
    have hnat : (2013251069 : ℕ)^2169*5000000000000^1657 ≤ 613448158263^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013251069 10000000000 613448158263 5000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245983171/10000000000 : ℝ)^2169 ≤ (8595786039019/20000000000000 : ℝ)^1657 := by
    have hnat : (5245983171 : ℕ)^2169*20000000000000^1657 ≤ 8595786039019^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245983171 10000000000 8595786039019 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352633643/2500000000 : ℝ)^2169 ≤ (4475210662833/10000000000000 : ℝ)^1657 := by
    have hnat : (1352633643 : ℕ)^2169*10000000000000^1657 ≤ 4475210662833^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352633643 2500000000 4475210662833 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013251069/10000000000 : ℝ), (5245983171/10000000000 : ℝ), (1352633643/2500000000 : ℝ)] ![(613448158263/5000000000000 : ℝ), (8595786039019/20000000000000 : ℝ), (4475210662833/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013251069/10000000000 : ℝ)|^2169 ≤ (613448158263/5000000000000 : ℝ)^1657
        have hw : |(-2013251069/10000000000 : ℝ)|=(2013251069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245983171/10000000000 : ℝ)|^2169 ≤ (8595786039019/20000000000000 : ℝ)^1657
        have hw : |(5245983171/10000000000 : ℝ)|=(5245983171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352633643/2500000000 : ℝ)|^2169 ≤ (4475210662833/10000000000000 : ℝ)^1657
        have hw : |(1352633643/2500000000 : ℝ)|=(1352633643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s5_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305556071/10000000000 : ℝ)*x 0 + (-966259047/5000000000 : ℝ)*x 1 + (5410534529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305556071/10000000000 : ℝ)^2169 ≤ (21809460541793/50000000000000 : ℝ)^1657 := by
    have hnat : (5305556071 : ℕ)^2169*50000000000000^1657 ≤ 21809460541793^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305556071 10000000000 21809460541793 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966259047/5000000000 : ℝ)^2169 ≤ (5814486368683/50000000000000 : ℝ)^1657 := by
    have hnat : (966259047 : ℕ)^2169*50000000000000^1657 ≤ 5814486368683^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966259047 5000000000 5814486368683 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410534529/10000000000 : ℝ)^2169 ≤ (44752106162767/100000000000000 : ℝ)^1657 := by
    have hnat : (5410534529 : ℕ)^2169*100000000000000^1657 ≤ 44752106162767^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410534529 10000000000 44752106162767 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305556071/10000000000 : ℝ), (-966259047/5000000000 : ℝ), (5410534529/10000000000 : ℝ)] ![(21809460541793/50000000000000 : ℝ), (5814486368683/50000000000000 : ℝ), (44752106162767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305556071/10000000000 : ℝ)|^2169 ≤ (21809460541793/50000000000000 : ℝ)^1657
        have hw : |(5305556071/10000000000 : ℝ)|=(5305556071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966259047/5000000000 : ℝ)|^2169 ≤ (5814486368683/50000000000000 : ℝ)^1657
        have hw : |(-966259047/5000000000 : ℝ)|=(966259047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410534529/10000000000 : ℝ)|^2169 ≤ (44752106162767/100000000000000 : ℝ)^1657
        have hw : |(5410534529/10000000000 : ℝ)|=(5410534529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s5_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652778057/5000000000 : ℝ)*x 0 + (1352633569/2500000000 : ℝ)*x 1 + (-1932518383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652778057/5000000000 : ℝ)^2169 ≤ (2180946077317/5000000000000 : ℝ)^1657 := by
    have hnat : (2652778057 : ℕ)^2169*5000000000000^1657 ≤ 2180946077317^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652778057 5000000000 2180946077317 5000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352633569/2500000000 : ℝ)^2169 ≤ (22376051711761/50000000000000 : ℝ)^1657 := by
    have hnat : (1352633569 : ℕ)^2169*50000000000000^1657 ≤ 22376051711761^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352633569 2500000000 22376051711761 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932518383/10000000000 : ℝ)^2169 ≤ (11628975013787/100000000000000 : ℝ)^1657 := by
    have hnat : (1932518383 : ℕ)^2169*100000000000000^1657 ≤ 11628975013787^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932518383 10000000000 11628975013787 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652778057/5000000000 : ℝ), (1352633569/2500000000 : ℝ), (-1932518383/10000000000 : ℝ)] ![(2180946077317/5000000000000 : ℝ), (22376051711761/50000000000000 : ℝ), (11628975013787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652778057/5000000000 : ℝ)|^2169 ≤ (2180946077317/5000000000000 : ℝ)^1657
        have hw : |(2652778057/5000000000 : ℝ)|=(2652778057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352633569/2500000000 : ℝ)|^2169 ≤ (22376051711761/50000000000000 : ℝ)^1657
        have hw : |(1352633569/2500000000 : ℝ)|=(1352633569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1932518383/10000000000 : ℝ)|^2169 ≤ (11628975013787/100000000000000 : ℝ)^1657
        have hw : |(-1932518383/10000000000 : ℝ)|=(1932518383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s5_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4317299577/10000000000 : ℝ)*x 0 + (561905433/1250000000 : ℝ)*x 1 + (414590493/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317299577/10000000000 : ℝ)^2169 ≤ (33303939778621/100000000000000 : ℝ)^1657 := by
    have hnat : (4317299577 : ℕ)^2169*100000000000000^1657 ≤ 33303939778621^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317299577 10000000000 33303939778621 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561905433/1250000000 : ℝ)^2169 ≤ (8778022620999/25000000000000 : ℝ)^1657 := by
    have hnat : (561905433 : ℕ)^2169*25000000000000^1657 ≤ 8778022620999^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561905433 1250000000 8778022620999 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414590493/1000000000 : ℝ)^2169 ≤ (31583969730553/100000000000000 : ℝ)^1657 := by
    have hnat : (414590493 : ℕ)^2169*100000000000000^1657 ≤ 31583969730553^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414590493 1000000000 31583969730553 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317299577/10000000000 : ℝ), (561905433/1250000000 : ℝ), (414590493/1000000000 : ℝ)] ![(33303939778621/100000000000000 : ℝ), (8778022620999/25000000000000 : ℝ), (31583969730553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317299577/10000000000 : ℝ)|^2169 ≤ (33303939778621/100000000000000 : ℝ)^1657
        have hw : |(4317299577/10000000000 : ℝ)|=(4317299577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561905433/1250000000 : ℝ)|^2169 ≤ (8778022620999/25000000000000 : ℝ)^1657
        have hw : |(561905433/1250000000 : ℝ)|=(561905433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414590493/1000000000 : ℝ)|^2169 ≤ (31583969730553/100000000000000 : ℝ)^1657
        have hw : |(414590493/1000000000 : ℝ)|=(414590493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2947/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1399/12500 : ℝ) ^ (4337/1024 : ℝ) ≤ (9371082200339963/100000000000000000000 : ℝ) := by
    have hpowers : (1399/12500 : ℝ)^4337 ≤ (9371082200339963/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1399 : ℕ)^4337*100000000000000000000^1024 ≤ 9371082200339963^1024*12500^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 12500 9371082200339963 100000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/12500 : ℝ)) (X := (9371082200339963/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (4337/1024 : ℝ) ≤ (3793751912028531/12500000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^4337 ≤ (3793751912028531/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14771 : ℕ)^4337*12500000000000000000^1024 ≤ 3793751912028531^1024*100000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 3793751912028531 12500000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (3793751912028531/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009371082200339963/50000000000000000000 : ℝ) ≤ (1000044248565001/1000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (50009371082200339963/50000000000000000000 : ℝ)^1024 ≤ (1000044248565001/1000000000000000 : ℝ)^4337 := by
      have hnat : (50009371082200339963 : ℕ)^1024*1000000000000000^4337 ≤ 1000044248565001^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009371082200339963 50000000000000000000 1000044248565001 1000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000044248565001/1000000000000000 : ℝ)) (X := (50009371082200339963/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039721097496568211/100000000000000000000 : ℝ) ≤ (10000937704275649/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (100039721097496568211/100000000000000000000 : ℝ)^1024 ≤ (10000937704275649/10000000000000000 : ℝ)^4337 := by
      have hnat : (100039721097496568211 : ℕ)^1024*10000000000000000^4337 ≤ 10000937704275649^4337*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039721097496568211 100000000000000000000 10000937704275649 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000937704275649/10000000000000000 : ℝ)) (X := (100039721097496568211/100000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253793751912028531/6250000000000000000 : ℝ) ≤ (1250179115362661/1250000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (6253793751912028531/6250000000000000000 : ℝ)^1024 ≤ (1250179115362661/1250000000000000 : ℝ)^4337 := by
      have hnat : (6253793751912028531 : ℕ)^1024*1250000000000000^4337 ≤ 1250179115362661^4337*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253793751912028531 6250000000000000000 1250179115362661 1250000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250179115362661/1250000000000000 : ℝ)) (X := (6253793751912028531/6250000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9371082200339963/100000000000000000000 : ℝ) ≤ ((5963416447070847069/5965000000000000000 : ℝ)+2*(165072875213/119300000000000 : ℝ)*(1399/12500 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (5963416447070847069/5965000000000000000 : ℝ)+2*(165072875213/119300000000000 : ℝ)*(1399/12500 : ℝ)=(1000044248565001/1000000000000000 : ℝ) by norm_num, show 1+2*(9371082200339963/100000000000000000000 : ℝ)=(50009371082200339963/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3793751912028531/12500000000000000000 : ℝ)+(9371082200339963/100000000000000000000 : ℝ) ≤ ((5963416447070847069/5965000000000000000 : ℝ)+(165072875213/119300000000000 : ℝ)*((14771/100000 : ℝ)+(1399/12500 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (5963416447070847069/5965000000000000000 : ℝ)+(165072875213/119300000000000 : ℝ)*((14771/100000 : ℝ)+(1399/12500 : ℝ))=(10000937704275649/10000000000000000 : ℝ) by norm_num, show 1+(3793751912028531/12500000000000000000 : ℝ)+(9371082200339963/100000000000000000000 : ℝ)=(100039721097496568211/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3793751912028531/12500000000000000000 : ℝ) ≤ ((5963416447070847069/5965000000000000000 : ℝ)+2*(165072875213/119300000000000 : ℝ)*(14771/100000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (5963416447070847069/5965000000000000000 : ℝ)+2*(165072875213/119300000000000 : ℝ)*(14771/100000 : ℝ)=(1250179115362661/1250000000000000 : ℝ) by norm_num, show 1+2*(3793751912028531/12500000000000000000 : ℝ)=(6253793751912028531/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5963416447070847069/5965000000000000000 : ℝ)*(X 1 0+X 2 0)+(165072875213/119300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (5963416447070847069/5965000000000000000 : ℝ)) (alpha := (165072875213/119300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5963416447070847069/5965000000000000000 : ℝ)*(X 0 1+X 2 1)+(165072875213/119300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (5963416447070847069/5965000000000000000 : ℝ)) (alpha := (165072875213/119300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5963416447070847069/5965000000000000000 : ℝ)*(X 0 2+X 1 2)+(165072875213/119300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (5963416447070847069/5965000000000000000 : ℝ)) (alpha := (165072875213/119300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1006619553/5000000000 : ℝ)*X 0 0+(5411134839/10000000000 : ℝ)*X 0 1+(209815441/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348420913/10000000000 : ℝ)*X 1 0+(-2097666753/10000000000 : ℝ)*X 1 1+(655673249/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348420959/10000000000 : ℝ)*X 2 0+(5245386023/10000000000 : ℝ)*X 2 1+(-524416663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86345469/200000000 : ℝ)*X 0 0+(1036157811/2500000000 : ℝ)*X 0 1+(2248255697/5000000000 : ℝ)*X 0 2+(86345469/200000000 : ℝ)*X 1 0+(1036157811/2500000000 : ℝ)*X 1 1+(2248255697/5000000000 : ℝ)*X 1 2+(86345469/200000000 : ℝ)*X 2 0+(1036157811/2500000000 : ℝ)*X 2 1+(2248255697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2013251069/10000000000 : ℝ)*X 0 0+(5245983171/10000000000 : ℝ)*X 0 1+(1352633643/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305556071/10000000000 : ℝ)*X 1 0+(-966259047/5000000000 : ℝ)*X 1 1+(5410534529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652778057/5000000000 : ℝ)*X 2 0+(1352633569/2500000000 : ℝ)*X 2 1+(-1932518383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317299577/10000000000 : ℝ)*X 0 0+(561905433/1250000000 : ℝ)*X 0 1+(414590493/1000000000 : ℝ)*X 0 2+(4317299577/10000000000 : ℝ)*X 1 0+(561905433/1250000000 : ℝ)*X 1 1+(414590493/1000000000 : ℝ)*X 1 2+(4317299577/10000000000 : ℝ)*X 2 0+(561905433/1250000000 : ℝ)*X 2 1+(414590493/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87028739919330993892407999/37281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129355223/50000000000000 : ℝ)*(base19) + (280912519/100000000000000 : ℝ)*(base23) + (26771683/50000000000000 : ℝ)*(lower3) + (22447249/100000000000000 : ℝ)*(upper4) + (554695206886907/12500000000000 : ℝ)*(major0) + (554695206886907/12500000000000 : ℝ)*(major1) + (554695206886907/12500000000000 : ℝ)*(major2) + (3016616809653751/50000000000000 : ℝ)*(sp0) + (754155355677619/12500000000000 : ℝ)*(sp1) + (603324435569321/10000000000000 : ℝ)*(sp2) + (1420938917139921/50000000000000 : ℝ)*(sp3) + (11017298227/100000000000000 : ℝ)*(sp4) + (1532474331/100000000000000 : ℝ)*(sp5) + (152298429/20000000000000 : ℝ)*(sp7) + (1420939297885993/50000000000000 : ℝ)*(f.failure) + (6033244636605729/100000000000000 : ℝ)*(f.sum) + (7282353605661/2982500000000000000000000000 : ℝ)*base66 + (89069876063788083/74562500000000000000000000000000 : ℝ)*base67 + (72200182243524417/74562500000000000000000000000000 : ℝ)*base70 + (1216760076259149417/74562500000000000000000000000000 : ℝ)*base72 + (1240196533471/2982500000000000000000000000 : ℝ)*base74 + (132137149370413083/74562500000000000000000000000000 : ℝ)*base75 + (387931208484711917/74562500000000000000000000000000 : ℝ)*base78 + (1279420709883399417/74562500000000000000000000000000 : ℝ)*base80 + (18975161309871/2982500000000000000000000000 : ℝ)*base82 + (14795087/2500000000000000000000 : ℝ)*base90 + (14795087/2500000000000000000000 : ℝ)*base92 + (14795087/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135417927576856374776746887/29825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1148050681/100000000000000 : ℝ)*(base19) + (762633717/50000000000000 : ℝ)*(base23) + (17693163/20000000000000 : ℝ)*(upper3) + (100502687/50000000000000 : ℝ)*(lower4) + (52098679/25000000000000 : ℝ)*(upper5) + (893967779513241/20000000000000 : ℝ)*(major0) + (893967779513241/20000000000000 : ℝ)*(major1) + (893967779513241/20000000000000 : ℝ)*(major2) + (24965188127/100000000000000 : ℝ)*(sp1) + (3733144479/20000000000000 : ℝ)*(sp2) + (6077128235608051/100000000000000 : ℝ)*(sp4) + (6077102122369243/100000000000000 : ℝ)*(sp5) + (3038554022309111/50000000000000 : ℝ)*(sp6) + (286254940817713/10000000000000 : ℝ)*(sp7) + (286254940817713/10000000000000 : ℝ)*(f.failure) + (6077128235608051/100000000000000 : ℝ)*(f.sum) + (348833842857/119300000000000000000000000 : ℝ)*base65 + (495764694846890629/119300000000000000000000000000000 : ℝ)*base67 + (2079457277451409371/119300000000000000000000000000000 : ℝ)*base70 + (252259448792009371/119300000000000000000000000000000 : ℝ)*base72 + (1748561627931/596500000000000000000000000 : ℝ)*base73 + (2100044801980109371/119300000000000000000000000000000 : ℝ)*base76 + (1122333664535709371/119300000000000000000000000000000 : ℝ)*base78 + (565784914627909371/119300000000000000000000000000000 : ℝ)*base80 + (245660824871/1193000000000000000000000000 : ℝ)*base81 + (373433/500000000000000000000 : ℝ)*base89 + (373433/500000000000000000000 : ℝ)*base91 + (373433/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1378_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1378_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5039/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1378_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1378_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1378_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5039/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1378_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
