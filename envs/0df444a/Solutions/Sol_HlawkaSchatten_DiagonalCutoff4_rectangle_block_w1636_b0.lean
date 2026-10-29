-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1636_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:01:39.166357+00:00
-- url     : https://prove2.me/submissions/25b83a5d-8332-4c45-a463-b17e2ba02db5

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
theorem support_rectangle_w1636_s0_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-758771917/5000000000 : ℝ)*x 0 + (580291371/1000000000 : ℝ)*x 1 + (4911884371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (758771917/5000000000 : ℝ)^4863 ≤ (4588725026927/50000000000000 : ℝ)^3839 := by
    have hnat : (758771917 : ℕ)^4863*50000000000000^3839 ≤ 4588725026927^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758771917 5000000000 4588725026927 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580291371/1000000000 : ℝ)^4863 ≤ (25094121469783/50000000000000 : ℝ)^3839 := by
    have hnat : (580291371 : ℕ)^4863*50000000000000^3839 ≤ 25094121469783^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580291371 1000000000 25094121469783 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4911884371/10000000000 : ℝ)^4863 ≤ (2031715348977/5000000000000 : ℝ)^3839 := by
    have hnat : (4911884371 : ℕ)^4863*5000000000000^3839 ≤ 2031715348977^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911884371 10000000000 2031715348977 5000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-758771917/5000000000 : ℝ), (580291371/1000000000 : ℝ), (4911884371/10000000000 : ℝ)] ![(4588725026927/50000000000000 : ℝ), (25094121469783/50000000000000 : ℝ), (2031715348977/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-758771917/5000000000 : ℝ)|^4863 ≤ (4588725026927/50000000000000 : ℝ)^3839
        have hw : |(-758771917/5000000000 : ℝ)|=(758771917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(580291371/1000000000 : ℝ)|^4863 ≤ (25094121469783/50000000000000 : ℝ)^3839
        have hw : |(580291371/1000000000 : ℝ)|=(580291371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4911884371/10000000000 : ℝ)|^4863 ≤ (2031715348977/5000000000000 : ℝ)^3839
        have hw : |(4911884371/10000000000 : ℝ)|=(4911884371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s0_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5443127397/10000000000 : ℝ)*x 0 + (-2008084973/10000000000 : ℝ)*x 1 + (4911886041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5443127397/10000000000 : ℝ)^4863 ≤ (23139808186603/50000000000000 : ℝ)^3839 := by
    have hnat : (5443127397 : ℕ)^4863*50000000000000^3839 ≤ 23139808186603^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443127397 10000000000 23139808186603 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008084973/10000000000 : ℝ)^4863 ≤ (13086059140447/100000000000000 : ℝ)^3839 := by
    have hnat : (2008084973 : ℕ)^4863*100000000000000^3839 ≤ 13086059140447^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008084973 10000000000 13086059140447 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4911886041/10000000000 : ℝ)^4863 ≤ (10158581119979/25000000000000 : ℝ)^3839 := by
    have hnat : (4911886041 : ℕ)^4863*25000000000000^3839 ≤ 10158581119979^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911886041 10000000000 10158581119979 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5443127397/10000000000 : ℝ), (-2008084973/10000000000 : ℝ), (4911886041/10000000000 : ℝ)] ![(23139808186603/50000000000000 : ℝ), (13086059140447/100000000000000 : ℝ), (10158581119979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5443127397/10000000000 : ℝ)|^4863 ≤ (23139808186603/50000000000000 : ℝ)^3839
        have hw : |(5443127397/10000000000 : ℝ)|=(5443127397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2008084973/10000000000 : ℝ)|^4863 ≤ (13086059140447/100000000000000 : ℝ)^3839
        have hw : |(-2008084973/10000000000 : ℝ)|=(2008084973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4911886041/10000000000 : ℝ)|^4863 ≤ (10158581119979/25000000000000 : ℝ)^3839
        have hw : |(4911886041/10000000000 : ℝ)|=(4911886041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s0_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85048887/156250000 : ℝ)*x 0 + (2455942301/5000000000 : ℝ)*x 1 + (-200808501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85048887/156250000 : ℝ)^4863 ≤ (23139815569637/50000000000000 : ℝ)^3839 := by
    have hnat : (85048887 : ℕ)^4863*50000000000000^3839 ≤ 23139815569637^3839*156250000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85048887 156250000 23139815569637 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2455942301/5000000000 : ℝ)^4863 ≤ (40634309400251/100000000000000 : ℝ)^3839 := by
    have hnat : (2455942301 : ℕ)^4863*100000000000000^3839 ≤ 40634309400251^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455942301 5000000000 40634309400251 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200808501/1000000000 : ℝ)^4863 ≤ (13086059445879/100000000000000 : ℝ)^3839 := by
    have hnat : (200808501 : ℕ)^4863*100000000000000^3839 ≤ 13086059445879^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200808501 1000000000 13086059445879 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85048887/156250000 : ℝ), (2455942301/5000000000 : ℝ), (-200808501/1000000000 : ℝ)] ![(23139815569637/50000000000000 : ℝ), (40634309400251/100000000000000 : ℝ), (13086059445879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85048887/156250000 : ℝ)|^4863 ≤ (23139815569637/50000000000000 : ℝ)^3839
        have hw : |(85048887/156250000 : ℝ)|=(85048887/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2455942301/5000000000 : ℝ)|^4863 ≤ (40634309400251/100000000000000 : ℝ)^3839
        have hw : |(2455942301/5000000000 : ℝ)|=(2455942301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200808501/1000000000 : ℝ)|^4863 ≤ (13086059445879/100000000000000 : ℝ)^3839
        have hw : |(-200808501/1000000000 : ℝ)|=(200808501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s0_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4097220613/10000000000 : ℝ)*x 0 + (3079314391/10000000000 : ℝ)*x 1 + (2672009893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4097220613/10000000000 : ℝ)^4863 ≤ (8073582111267/25000000000000 : ℝ)^3839 := by
    have hnat : (4097220613 : ℕ)^4863*25000000000000^3839 ≤ 8073582111267^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097220613 10000000000 8073582111267 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3079314391/10000000000 : ℝ)^4863 ≤ (22490869215023/100000000000000 : ℝ)^3839 := by
    have hnat : (3079314391 : ℕ)^4863*100000000000000^3839 ≤ 22490869215023^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3079314391 10000000000 22490869215023 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2672009893/5000000000 : ℝ)^4863 ≤ (45214802319553/100000000000000 : ℝ)^3839 := by
    have hnat : (2672009893 : ℕ)^4863*100000000000000^3839 ≤ 45214802319553^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672009893 5000000000 45214802319553 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4097220613/10000000000 : ℝ), (3079314391/10000000000 : ℝ), (2672009893/5000000000 : ℝ)] ![(8073582111267/25000000000000 : ℝ), (22490869215023/100000000000000 : ℝ), (45214802319553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4097220613/10000000000 : ℝ)|^4863 ≤ (8073582111267/25000000000000 : ℝ)^3839
        have hw : |(4097220613/10000000000 : ℝ)|=(4097220613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3079314391/10000000000 : ℝ)|^4863 ≤ (22490869215023/100000000000000 : ℝ)^3839
        have hw : |(3079314391/10000000000 : ℝ)|=(3079314391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2672009893/5000000000 : ℝ)|^4863 ≤ (45214802319553/100000000000000 : ℝ)^3839
        have hw : |(2672009893/5000000000 : ℝ)|=(2672009893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s0_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-760001583/5000000000 : ℝ)*x 0 + (2467074923/5000000000 : ℝ)*x 1 + (577987149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760001583/5000000000 : ℝ)^4863 ≤ (574768391457/6250000000000 : ℝ)^3839 := by
    have hnat : (760001583 : ℕ)^4863*6250000000000^3839 ≤ 574768391457^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760001583 5000000000 574768391457 6250000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2467074923/5000000000 : ℝ)^4863 ≤ (5108471715669/12500000000000 : ℝ)^3839 := by
    have hnat : (2467074923 : ℕ)^4863*12500000000000^3839 ≤ 5108471715669^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467074923 5000000000 5108471715669 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (577987149/1000000000 : ℝ)^4863 ≤ (6241991500227/12500000000000 : ℝ)^3839 := by
    have hnat : (577987149 : ℕ)^4863*12500000000000^3839 ≤ 6241991500227^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577987149 1000000000 6241991500227 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760001583/5000000000 : ℝ), (2467074923/5000000000 : ℝ), (577987149/1000000000 : ℝ)] ![(574768391457/6250000000000 : ℝ), (5108471715669/12500000000000 : ℝ), (6241991500227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760001583/5000000000 : ℝ)|^4863 ≤ (574768391457/6250000000000 : ℝ)^3839
        have hw : |(-760001583/5000000000 : ℝ)|=(760001583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2467074923/5000000000 : ℝ)|^4863 ≤ (5108471715669/12500000000000 : ℝ)^3839
        have hw : |(2467074923/5000000000 : ℝ)|=(2467074923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(577987149/1000000000 : ℝ)|^4863 ≤ (6241991500227/12500000000000 : ℝ)^3839
        have hw : |(577987149/1000000000 : ℝ)|=(577987149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s0_5 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299971837/2500000000 : ℝ)*x 0 + (-228020037/2000000000 : ℝ)*x 1 + (231194779/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299971837/2500000000 : ℝ)^4863 ≤ (43675637886321/100000000000000 : ℝ)^3839 := by
    have hnat : (1299971837 : ℕ)^4863*100000000000000^3839 ≤ 43675637886321^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299971837 2500000000 43675637886321 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228020037/2000000000 : ℝ)^4863 ≤ (3194226078037/50000000000000 : ℝ)^3839 := by
    have hnat : (228020037 : ℕ)^4863*50000000000000^3839 ≤ 3194226078037^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228020037 2000000000 3194226078037 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231194779/400000000 : ℝ)^4863 ≤ (49935909949401/100000000000000 : ℝ)^3839 := by
    have hnat : (231194779 : ℕ)^4863*100000000000000^3839 ≤ 49935909949401^3839*400000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231194779 400000000 49935909949401 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299971837/2500000000 : ℝ), (-228020037/2000000000 : ℝ), (231194779/400000000 : ℝ)] ![(43675637886321/100000000000000 : ℝ), (3194226078037/50000000000000 : ℝ), (49935909949401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299971837/2500000000 : ℝ)|^4863 ≤ (43675637886321/100000000000000 : ℝ)^3839
        have hw : |(1299971837/2500000000 : ℝ)|=(1299971837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-228020037/2000000000 : ℝ)|^4863 ≤ (3194226078037/50000000000000 : ℝ)^3839
        have hw : |(-228020037/2000000000 : ℝ)|=(228020037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(231194779/400000000 : ℝ)|^4863 ≤ (49935909949401/100000000000000 : ℝ)^3839
        have hw : |(231194779/400000000 : ℝ)|=(231194779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s0_6 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299972031/2500000000 : ℝ)*x 0 + (5779868443/10000000000 : ℝ)*x 1 + (-285025153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299972031/2500000000 : ℝ)^4863 ≤ (2729727883923/6250000000000 : ℝ)^3839 := by
    have hnat : (1299972031 : ℕ)^4863*6250000000000^3839 ≤ 2729727883923^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299972031 2500000000 2729727883923 6250000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5779868443/10000000000 : ℝ)^4863 ≤ (49935898655063/100000000000000 : ℝ)^3839 := by
    have hnat : (5779868443 : ℕ)^4863*100000000000000^3839 ≤ 49935898655063^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5779868443 10000000000 49935898655063 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285025153/2500000000 : ℝ)^4863 ≤ (319422759347/5000000000000 : ℝ)^3839 := by
    have hnat : (285025153 : ℕ)^4863*5000000000000^3839 ≤ 319422759347^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285025153 2500000000 319422759347 5000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299972031/2500000000 : ℝ), (5779868443/10000000000 : ℝ), (-285025153/2500000000 : ℝ)] ![(2729727883923/6250000000000 : ℝ), (49935898655063/100000000000000 : ℝ), (319422759347/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299972031/2500000000 : ℝ)|^4863 ≤ (2729727883923/6250000000000 : ℝ)^3839
        have hw : |(1299972031/2500000000 : ℝ)|=(1299972031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5779868443/10000000000 : ℝ)|^4863 ≤ (49935898655063/100000000000000 : ℝ)^3839
        have hw : |(5779868443/10000000000 : ℝ)|=(5779868443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-285025153/2500000000 : ℝ)|^4863 ≤ (319422759347/5000000000000 : ℝ)^3839
        have hw : |(-285025153/2500000000 : ℝ)|=(285025153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s0_7 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4103474419/10000000000 : ℝ)*x 0 + (5287423923/10000000000 : ℝ)*x 1 + (3137884369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103474419/10000000000 : ℝ)^4863 ≤ (16178390904599/50000000000000 : ℝ)^3839 := by
    have hnat : (4103474419 : ℕ)^4863*50000000000000^3839 ≤ 16178390904599^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103474419 10000000000 16178390904599 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5287423923/10000000000 : ℝ)^4863 ≤ (22304543903441/50000000000000 : ℝ)^3839 := by
    have hnat : (5287423923 : ℕ)^4863*50000000000000^3839 ≤ 22304543903441^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287423923 10000000000 22304543903441 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3137884369/10000000000 : ℝ)^4863 ≤ (23034130365621/100000000000000 : ℝ)^3839 := by
    have hnat : (3137884369 : ℕ)^4863*100000000000000^3839 ≤ 23034130365621^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137884369 10000000000 23034130365621 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103474419/10000000000 : ℝ), (5287423923/10000000000 : ℝ), (3137884369/10000000000 : ℝ)] ![(16178390904599/50000000000000 : ℝ), (22304543903441/50000000000000 : ℝ), (23034130365621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103474419/10000000000 : ℝ)|^4863 ≤ (16178390904599/50000000000000 : ℝ)^3839
        have hw : |(4103474419/10000000000 : ℝ)|=(4103474419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5287423923/10000000000 : ℝ)|^4863 ≤ (22304543903441/50000000000000 : ℝ)^3839
        have hw : |(5287423923/10000000000 : ℝ)|=(5287423923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3137884369/10000000000 : ℝ)|^4863 ≤ (23034130365621/100000000000000 : ℝ)^3839
        have hw : |(3137884369/10000000000 : ℝ)|=(3137884369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4567/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23659/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4859/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4859 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4859*1^1024 ≤ 0^1024*1^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4859/1024 : ℝ) ≤ (1293385611515575383/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4859 ≤ (1293385611515575383/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4859*100000000000000000000^1024 ≤ 1293385611515575383^1024*5^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1293385611515575383 100000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1293385611515575383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4859 := by
      have hnat : (1 : ℕ)^1024*1^4859 ≤ 1^4859*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101293385611515575383/100000000000000000000 : ℝ) ≤ (2506779782780863/2500000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (101293385611515575383/100000000000000000000 : ℝ)^1024 ≤ (2506779782780863/2500000000000000 : ℝ)^4859 := by
      have hnat : (101293385611515575383 : ℕ)^1024*2500000000000000^4859 ≤ 2506779782780863^4859*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101293385611515575383 100000000000000000000 2506779782780863 2500000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506779782780863/2500000000000000 : ℝ)) (X := (101293385611515575383/100000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51293385611515575383/50000000000000000000 : ℝ) ≤ (1256779782780863/1250000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (51293385611515575383/50000000000000000000 : ℝ)^1024 ≤ (1256779782780863/1250000000000000 : ℝ)^4859 := by
      have hnat : (51293385611515575383 : ℕ)^1024*1250000000000000^4859 ≤ 1256779782780863^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51293385611515575383 50000000000000000000 1256779782780863 1250000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256779782780863/1250000000000000 : ℝ)) (X := (51293385611515575383/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6779782780863/1000000000000000 : ℝ)*(0 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6779782780863/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1293385611515575383/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6779782780863/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6779782780863/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2506779782780863/2500000000000000 : ℝ) by norm_num, show 1+(1293385611515575383/100000000000000000000 : ℝ)+(0 : ℝ)=(101293385611515575383/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1293385611515575383/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6779782780863/1000000000000000 : ℝ)*(2/5 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6779782780863/1000000000000000 : ℝ)*(2/5 : ℝ)=(1256779782780863/1250000000000000 : ℝ) by norm_num, show 1+2*(1293385611515575383/100000000000000000000 : ℝ)=(51293385611515575383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6779782780863/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6779782780863/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6779782780863/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6779782780863/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6779782780863/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6779782780863/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-758771917/5000000000 : ℝ)*X 0 0+(580291371/1000000000 : ℝ)*X 0 1+(4911884371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5443127397/10000000000 : ℝ)*X 1 0+(-2008084973/10000000000 : ℝ)*X 1 1+(4911886041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((85048887/156250000 : ℝ)*X 2 0+(2455942301/5000000000 : ℝ)*X 2 1+(-200808501/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4097220613/10000000000 : ℝ)*X 0 0+(3079314391/10000000000 : ℝ)*X 0 1+(2672009893/5000000000 : ℝ)*X 0 2+(4097220613/10000000000 : ℝ)*X 1 0+(3079314391/10000000000 : ℝ)*X 1 1+(2672009893/5000000000 : ℝ)*X 1 2+(4097220613/10000000000 : ℝ)*X 2 0+(3079314391/10000000000 : ℝ)*X 2 1+(2672009893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-760001583/5000000000 : ℝ)*X 0 0+(2467074923/5000000000 : ℝ)*X 0 1+(577987149/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299971837/2500000000 : ℝ)*X 1 0+(-228020037/2000000000 : ℝ)*X 1 1+(231194779/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299972031/2500000000 : ℝ)*X 2 0+(5779868443/10000000000 : ℝ)*X 2 1+(-285025153/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4103474419/10000000000 : ℝ)*X 0 0+(5287423923/10000000000 : ℝ)*X 0 1+(3137884369/10000000000 : ℝ)*X 0 2+(4103474419/10000000000 : ℝ)*X 1 0+(5287423923/10000000000 : ℝ)*X 1 1+(3137884369/10000000000 : ℝ)*X 1 2+(4103474419/10000000000 : ℝ)*X 2 0+(5287423923/10000000000 : ℝ)*X 2 1+(3137884369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49800808621142534721921/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68222137/5000000000000 : ℝ)*(base19) + (1632780237/100000000000000 : ℝ)*(base23) + (181112531/100000000000000 : ℝ)*(upper3) + (1952323/25000000000000 : ℝ)*(upper4) + (227592979/100000000000000 : ℝ)*(upper5) + (195484604127339/25000000000000 : ℝ)*(major0) + (195484604127339/25000000000000 : ℝ)*(major1) + (195484604127339/25000000000000 : ℝ)*(major2) + (112230435926493/10000000000000 : ℝ)*(sp0) + (1122311065882753/100000000000000 : ℝ)*(sp1) + (140288849693157/12500000000000 : ℝ)*(sp2) + (441561256410913/100000000000000 : ℝ)*(sp3) + (8071060563/100000000000000 : ℝ)*(sp4) + (288067799/10000000000000 : ℝ)*(sp7) + (441564137088903/100000000000000 : ℝ)*(f.failure) + (1122312430325493/100000000000000 : ℝ)*(f.sum) + (2549758198943/12500000000000000000000000000 : ℝ)*base66 + (53137350538557/25000000000000000000000000000 : ℝ)*base67 + (202510236386443/25000000000000000000000000000 : ℝ)*base70 + (80086501186443/25000000000000000000000000000 : ℝ)*base72 + (41633620763557/12500000000000000000000000000 : ℝ)*base73 + (76032560711443/25000000000000000000000000000 : ℝ)*base76 + (126872517861443/25000000000000000000000000000 : ℝ)*base78 + (39581487688557/25000000000000000000000000000 : ℝ)*base79 + (46800345286443/12500000000000000000000000000 : ℝ)*base82 + (31315407/10000000000000000000000 : ℝ)*base89 + (31315407/10000000000000000000000 : ℝ)*base91 + (31315407/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29957490525015221056137/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1936993021/100000000000000 : ℝ)*(base19) + (2063037773/100000000000000 : ℝ)*(base23) + (166708907/50000000000000 : ℝ)*(base32) + (140347507/100000000000000 : ℝ)*(upper3) + (277239319/100000000000000 : ℝ)*(upper5) + (51488691041333/6250000000000 : ℝ)*(major0) + (51488691041333/6250000000000 : ℝ)*(major1) + (51488691041333/6250000000000 : ℝ)*(major2) + (2527873709/50000000000000 : ℝ)*(sp1) + (497254353/12500000000000 : ℝ)*(sp2) + (14780293387771/1250000000000 : ℝ)*(sp4) + (1182416478281241/100000000000000 : ℝ)*(sp5) + (1182417429949083/100000000000000 : ℝ)*(sp6) + (465213989336593/100000000000000 : ℝ)*(sp7) + (465214322754407/100000000000000 : ℝ)*(f.failure) + (14780293387771/1250000000000 : ℝ)*(f.sum) + (103725800251/781250000000000000000000000 : ℝ)*base65 + (36531583208371/6250000000000000000000000000 : ℝ)*base68 + (9117526804129/6250000000000000000000000000 : ℝ)*base69 + (3302762345871/6250000000000000000000000000 : ℝ)*base72 + (14305595089621/3125000000000000000000000000 : ℝ)*base74 + (23464394527121/6250000000000000000000000000 : ℝ)*base76 + (29222495533371/6250000000000000000000000000 : ℝ)*base78 + (26026624064621/6250000000000000000000000000 : ℝ)*base80 + (5577120047377/1562500000000000000000000000 : ℝ)*base81 + (52919983/10000000000000000000000 : ℝ)*base89 + (52919983/10000000000000000000000 : ℝ)*base91 + (52919983/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1636_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4567/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23659/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1636_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1636_s1_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-407331451/2500000000 : ℝ)*x 0 + (2753602501/5000000000 : ℝ)*x 1 + (1283767041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407331451/2500000000 : ℝ)^4863 ≤ (2510510205427/25000000000000 : ℝ)^3839 := by
    have hnat : (407331451 : ℕ)^4863*25000000000000^3839 ≤ 2510510205427^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407331451 2500000000 2510510205427 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753602501/5000000000 : ℝ)^4863 ≤ (9394166242711/20000000000000 : ℝ)^3839 := by
    have hnat : (2753602501 : ℕ)^4863*20000000000000^3839 ≤ 9394166242711^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753602501 5000000000 9394166242711 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283767041/2500000000 : ℝ)^4863 ≤ (42987127956929/100000000000000 : ℝ)^3839 := by
    have hnat : (1283767041 : ℕ)^4863*100000000000000^3839 ≤ 42987127956929^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283767041 2500000000 42987127956929 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407331451/2500000000 : ℝ), (2753602501/5000000000 : ℝ), (1283767041/2500000000 : ℝ)] ![(2510510205427/25000000000000 : ℝ), (9394166242711/20000000000000 : ℝ), (42987127956929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407331451/2500000000 : ℝ)|^4863 ≤ (2510510205427/25000000000000 : ℝ)^3839
        have hw : |(-407331451/2500000000 : ℝ)|=(407331451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753602501/5000000000 : ℝ)|^4863 ≤ (9394166242711/20000000000000 : ℝ)^3839
        have hw : |(2753602501/5000000000 : ℝ)|=(2753602501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283767041/2500000000 : ℝ)|^4863 ≤ (42987127956929/100000000000000 : ℝ)^3839
        have hw : |(1283767041/2500000000 : ℝ)|=(1283767041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s1_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6705593/12500000 : ℝ)*x 0 + (-911581783/5000000000 : ℝ)*x 1 + (1027013589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6705593/12500000 : ℝ)^4863 ≤ (4543413909681/10000000000000 : ℝ)^3839 := by
    have hnat : (6705593 : ℕ)^4863*10000000000000^3839 ≤ 4543413909681^3839*12500000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6705593 12500000 4543413909681 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911581783/5000000000 : ℝ)^4863 ≤ (2894683813553/25000000000000 : ℝ)^3839 := by
    have hnat : (911581783 : ℕ)^4863*25000000000000^3839 ≤ 2894683813553^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911581783 5000000000 2894683813553 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027013589/2000000000 : ℝ)^4863 ≤ (42987125634607/100000000000000 : ℝ)^3839 := by
    have hnat : (1027013589 : ℕ)^4863*100000000000000^3839 ≤ 42987125634607^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027013589 2000000000 42987125634607 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6705593/12500000 : ℝ), (-911581783/5000000000 : ℝ), (1027013589/2000000000 : ℝ)] ![(4543413909681/10000000000000 : ℝ), (2894683813553/25000000000000 : ℝ), (42987125634607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6705593/12500000 : ℝ)|^4863 ≤ (4543413909681/10000000000000 : ℝ)^3839
        have hw : |(6705593/12500000 : ℝ)|=(6705593/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-911581783/5000000000 : ℝ)|^4863 ≤ (2894683813553/25000000000000 : ℝ)^3839
        have hw : |(-911581783/5000000000 : ℝ)|=(911581783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027013589/2000000000 : ℝ)|^4863 ≤ (42987125634607/100000000000000 : ℝ)^3839
        have hw : |(1027013589/2000000000 : ℝ)|=(1027013589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s1_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364475379/10000000000 : ℝ)*x 0 + (256753339/500000000 : ℝ)*x 1 + (-455790949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364475379/10000000000 : ℝ)^4863 ≤ (45434149600067/100000000000000 : ℝ)^3839 := by
    have hnat : (5364475379 : ℕ)^4863*100000000000000^3839 ≤ 45434149600067^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364475379 10000000000 45434149600067 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256753339/500000000 : ℝ)^4863 ≤ (42987113280701/100000000000000 : ℝ)^3839 := by
    have hnat : (256753339 : ℕ)^4863*100000000000000^3839 ≤ 42987113280701^3839*500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256753339 500000000 42987113280701 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455790949/2500000000 : ℝ)^4863 ≤ (361835534517/3125000000000 : ℝ)^3839 := by
    have hnat : (455790949 : ℕ)^4863*3125000000000^3839 ≤ 361835534517^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455790949 2500000000 361835534517 3125000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364475379/10000000000 : ℝ), (256753339/500000000 : ℝ), (-455790949/2500000000 : ℝ)] ![(45434149600067/100000000000000 : ℝ), (42987113280701/100000000000000 : ℝ), (361835534517/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364475379/10000000000 : ℝ)|^4863 ≤ (45434149600067/100000000000000 : ℝ)^3839
        have hw : |(5364475379/10000000000 : ℝ)|=(5364475379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256753339/500000000 : ℝ)|^4863 ≤ (42987113280701/100000000000000 : ℝ)^3839
        have hw : |(256753339/500000000 : ℝ)|=(256753339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-455790949/2500000000 : ℝ)|^4863 ≤ (361835534517/3125000000000 : ℝ)^3839
        have hw : |(-455790949/2500000000 : ℝ)|=(455790949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s1_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183030709/10000000000 : ℝ)*x 0 + (932461969/2500000000 : ℝ)*x 1 + (93514017/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183030709/10000000000 : ℝ)^4863 ≤ (51802302961/156250000000 : ℝ)^3839 := by
    have hnat : (4183030709 : ℕ)^4863*156250000000^3839 ≤ 51802302961^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183030709 10000000000 51802302961 156250000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932461969/2500000000 : ℝ)^4863 ≤ (28671186534697/100000000000000 : ℝ)^3839 := by
    have hnat : (932461969 : ℕ)^4863*100000000000000^3839 ≤ 28671186534697^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932461969 2500000000 28671186534697 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93514017/200000000 : ℝ)^4863 ≤ (38175339559819/100000000000000 : ℝ)^3839 := by
    have hnat : (93514017 : ℕ)^4863*100000000000000^3839 ≤ 38175339559819^3839*200000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93514017 200000000 38175339559819 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183030709/10000000000 : ℝ), (932461969/2500000000 : ℝ), (93514017/200000000 : ℝ)] ![(51802302961/156250000000 : ℝ), (28671186534697/100000000000000 : ℝ), (38175339559819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183030709/10000000000 : ℝ)|^4863 ≤ (51802302961/156250000000 : ℝ)^3839
        have hw : |(4183030709/10000000000 : ℝ)|=(4183030709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932461969/2500000000 : ℝ)|^4863 ≤ (28671186534697/100000000000000 : ℝ)^3839
        have hw : |(932461969/2500000000 : ℝ)|=(932461969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(93514017/200000000 : ℝ)|^4863 ≤ (38175339559819/100000000000000 : ℝ)^3839
        have hw : |(93514017/200000000 : ℝ)|=(93514017/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s1_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50921947/312500000 : ℝ)*x 0 + (642366429/1250000000 : ℝ)*x 1 + (2751642431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50921947/312500000 : ℝ)^4863 ≤ (10043418827961/100000000000000 : ℝ)^3839 := by
    have hnat : (50921947 : ℕ)^4863*100000000000000^3839 ≤ 10043418827961^3839*312500000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50921947 312500000 10043418827961 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642366429/1250000000 : ℝ)^4863 ≤ (10757024744253/25000000000000 : ℝ)^3839 := by
    have hnat : (642366429 : ℕ)^4863*25000000000000^3839 ≤ 10757024744253^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642366429 1250000000 10757024744253 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751642431/5000000000 : ℝ)^4863 ≤ (46928482180483/100000000000000 : ℝ)^3839 := by
    have hnat : (2751642431 : ℕ)^4863*100000000000000^3839 ≤ 46928482180483^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751642431 5000000000 46928482180483 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50921947/312500000 : ℝ), (642366429/1250000000 : ℝ), (2751642431/5000000000 : ℝ)] ![(10043418827961/100000000000000 : ℝ), (10757024744253/25000000000000 : ℝ), (46928482180483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50921947/312500000 : ℝ)|^4863 ≤ (10043418827961/100000000000000 : ℝ)^3839
        have hw : |(-50921947/312500000 : ℝ)|=(50921947/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642366429/1250000000 : ℝ)|^4863 ≤ (10757024744253/25000000000000 : ℝ)^3839
        have hw : |(642366429/1250000000 : ℝ)|=(642366429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751642431/5000000000 : ℝ)|^4863 ≤ (46928482180483/100000000000000 : ℝ)^3839
        have hw : |(2751642431/5000000000 : ℝ)|=(2751642431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s1_5 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265128143/10000000000 : ℝ)*x 0 + (-145494633/1000000000 : ℝ)*x 1 + (5503284851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265128143/10000000000 : ℝ)^4863 ≤ (5546367713/12500000000 : ℝ)^3839 := by
    have hnat : (5265128143 : ℕ)^4863*12500000000^3839 ≤ 5546367713^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265128143 10000000000 5546367713 12500000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145494633/1000000000 : ℝ)^4863 ≤ (8700576211459/100000000000000 : ℝ)^3839 := by
    have hnat : (145494633 : ℕ)^4863*100000000000000^3839 ≤ 8700576211459^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145494633 1000000000 8700576211459 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5503284851/10000000000 : ℝ)^4863 ≤ (23464241030831/50000000000000 : ℝ)^3839 := by
    have hnat : (5503284851 : ℕ)^4863*50000000000000^3839 ≤ 23464241030831^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503284851 10000000000 23464241030831 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265128143/10000000000 : ℝ), (-145494633/1000000000 : ℝ), (5503284851/10000000000 : ℝ)] ![(5546367713/12500000000 : ℝ), (8700576211459/100000000000000 : ℝ), (23464241030831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265128143/10000000000 : ℝ)|^4863 ≤ (5546367713/12500000000 : ℝ)^3839
        have hw : |(5265128143/10000000000 : ℝ)|=(5265128143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145494633/1000000000 : ℝ)|^4863 ≤ (8700576211459/100000000000000 : ℝ)^3839
        have hw : |(-145494633/1000000000 : ℝ)|=(145494633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5503284851/10000000000 : ℝ)|^4863 ≤ (23464241030831/50000000000000 : ℝ)^3839
        have hw : |(5503284851/10000000000 : ℝ)|=(5503284851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s1_6 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632564017/5000000000 : ℝ)*x 0 + (2751642511/5000000000 : ℝ)*x 1 + (-4546707/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632564017/5000000000 : ℝ)^4863 ≤ (11092735135101/25000000000000 : ℝ)^3839 := by
    have hnat : (2632564017 : ℕ)^4863*25000000000000^3839 ≤ 11092735135101^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632564017 5000000000 11092735135101 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751642511/5000000000 : ℝ)^4863 ≤ (46928483908789/100000000000000 : ℝ)^3839 := by
    have hnat : (2751642511 : ℕ)^4863*100000000000000^3839 ≤ 46928483908789^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751642511 5000000000 46928483908789 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4546707/31250000 : ℝ)^4863 ≤ (8700575529701/100000000000000 : ℝ)^3839 := by
    have hnat : (4546707 : ℕ)^4863*100000000000000^3839 ≤ 8700575529701^3839*31250000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546707 31250000 8700575529701 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632564017/5000000000 : ℝ), (2751642511/5000000000 : ℝ), (-4546707/31250000 : ℝ)] ![(11092735135101/25000000000000 : ℝ), (46928483908789/100000000000000 : ℝ), (8700575529701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632564017/5000000000 : ℝ)|^4863 ≤ (11092735135101/25000000000000 : ℝ)^3839
        have hw : |(2632564017/5000000000 : ℝ)|=(2632564017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751642511/5000000000 : ℝ)|^4863 ≤ (46928483908789/100000000000000 : ℝ)^3839
        have hw : |(2751642511/5000000000 : ℝ)|=(2751642511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4546707/31250000 : ℝ)|^4863 ≤ (8700575529701/100000000000000 : ℝ)^3839
        have hw : |(-4546707/31250000 : ℝ)|=(4546707/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s1_7 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2091738199/5000000000 : ℝ)*x 0 + (4665880473/10000000000 : ℝ)*x 1 + (3739812479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091738199/5000000000 : ℝ)^4863 ≤ (16578974288807/50000000000000 : ℝ)^3839 := by
    have hnat : (2091738199 : ℕ)^4863*50000000000000^3839 ≤ 16578974288807^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091738199 5000000000 16578974288807 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4665880473/10000000000 : ℝ)^4863 ≤ (9518450379823/25000000000000 : ℝ)^3839 := by
    have hnat : (4665880473 : ℕ)^4863*25000000000000^3839 ≤ 9518450379823^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4665880473 10000000000 9518450379823 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3739812479/10000000000 : ℝ)^4863 ≤ (28768249893921/100000000000000 : ℝ)^3839 := by
    have hnat : (3739812479 : ℕ)^4863*100000000000000^3839 ≤ 28768249893921^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739812479 10000000000 28768249893921 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091738199/5000000000 : ℝ), (4665880473/10000000000 : ℝ), (3739812479/10000000000 : ℝ)] ![(16578974288807/50000000000000 : ℝ), (9518450379823/25000000000000 : ℝ), (28768249893921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091738199/5000000000 : ℝ)|^4863 ≤ (16578974288807/50000000000000 : ℝ)^3839
        have hw : |(2091738199/5000000000 : ℝ)|=(2091738199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4665880473/10000000000 : ℝ)|^4863 ≤ (9518450379823/25000000000000 : ℝ)^3839
        have hw : |(4665880473/10000000000 : ℝ)|=(4665880473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3739812479/10000000000 : ℝ)|^4863 ≤ (28768249893921/100000000000000 : ℝ)^3839
        have hw : |(3739812479/10000000000 : ℝ)|=(3739812479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23659/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4567/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4779/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17457/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23659/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4567/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23659/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4567/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23659/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4567/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23659/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4567/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23659/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4567/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23659/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4567/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4567/100000 : ℝ) ^ (4859/1024 : ℝ) ≤ (43630689434267/100000000000000000000 : ℝ) := by
    have hpowers : (4567/100000 : ℝ)^4859 ≤ (43630689434267/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4567 : ℕ)^4859*100000000000000000000^1024 ≤ 43630689434267^1024*100000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4567 100000 43630689434267 100000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4567/100000 : ℝ)) (X := (43630689434267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23659/100000 : ℝ) ^ (4859/1024 : ℝ) ≤ (107038369154187479/100000000000000000000 : ℝ) := by
    have hpowers : (23659/100000 : ℝ)^4859 ≤ (107038369154187479/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23659 : ℕ)^4859*100000000000000000000^1024 ≤ 107038369154187479^1024*100000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23659 100000 107038369154187479 100000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23659/100000 : ℝ)) (X := (107038369154187479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000043630689434267/50000000000000000000 : ℝ) ≤ (5000000919485709/5000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50000043630689434267/50000000000000000000 : ℝ)^1024 ≤ (5000000919485709/5000000000000000 : ℝ)^4859 := by
      have hnat : (50000043630689434267 : ℕ)^1024*5000000000000000^4859 ≤ 5000000919485709^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000043630689434267 50000000000000000000 5000000919485709 5000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000919485709/5000000000000000 : ℝ)) (X := (50000043630689434267/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50053540999921810873/50000000000000000000 : ℝ) ≤ (2000451144931501/2000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50053540999921810873/50000000000000000000 : ℝ)^1024 ≤ (2000451144931501/2000000000000000 : ℝ)^4859 := by
      have hnat : (50053540999921810873 : ℕ)^1024*2000000000000000^4859 ≤ 2000451144931501^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053540999921810873 50000000000000000000 2000451144931501 2000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000451144931501/2000000000000000 : ℝ)) (X := (50053540999921810873/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50107038369154187479/50000000000000000000 : ℝ) ≤ (1250563701292949/1250000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50107038369154187479/50000000000000000000 : ℝ)^1024 ≤ (1250563701292949/1250000000000000 : ℝ)^4859 := by
      have hnat : (50107038369154187479 : ℕ)^1024*1250000000000000^4859 ≤ 1250563701292949^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50107038369154187479 50000000000000000000 1250563701292949 1250000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250563701292949/1250000000000000 : ℝ)) (X := (50107038369154187479/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(43630689434267/100000000000000000000 : ℝ) ≤ ((95449724058892796899/95460000000000000000 : ℝ)+2*(2253885686087/1909200000000000 : ℝ)*(4567/100000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (95449724058892796899/95460000000000000000 : ℝ)+2*(2253885686087/1909200000000000 : ℝ)*(4567/100000 : ℝ)=(5000000919485709/5000000000000000 : ℝ) by norm_num, show 1+2*(43630689434267/100000000000000000000 : ℝ)=(50000043630689434267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(107038369154187479/100000000000000000000 : ℝ)+(43630689434267/100000000000000000000 : ℝ) ≤ ((95449724058892796899/95460000000000000000 : ℝ)+(2253885686087/1909200000000000 : ℝ)*((23659/100000 : ℝ)+(4567/100000 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (95449724058892796899/95460000000000000000 : ℝ)+(2253885686087/1909200000000000 : ℝ)*((23659/100000 : ℝ)+(4567/100000 : ℝ))=(2000451144931501/2000000000000000 : ℝ) by norm_num, show 1+(107038369154187479/100000000000000000000 : ℝ)+(43630689434267/100000000000000000000 : ℝ)=(50053540999921810873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(107038369154187479/100000000000000000000 : ℝ) ≤ ((95449724058892796899/95460000000000000000 : ℝ)+2*(2253885686087/1909200000000000 : ℝ)*(23659/100000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (95449724058892796899/95460000000000000000 : ℝ)+2*(2253885686087/1909200000000000 : ℝ)*(23659/100000 : ℝ)=(1250563701292949/1250000000000000 : ℝ) by norm_num, show 1+2*(107038369154187479/100000000000000000000 : ℝ)=(50107038369154187479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (95449724058892796899/95460000000000000000 : ℝ)*(X 1 0+X 2 0)+(2253885686087/1909200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (4567/100000 : ℝ)) (hi := (23659/100000 : ℝ)) (c := (95449724058892796899/95460000000000000000 : ℝ)) (alpha := (2253885686087/1909200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (95449724058892796899/95460000000000000000 : ℝ)*(X 0 1+X 2 1)+(2253885686087/1909200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (4567/100000 : ℝ)) (hi := (23659/100000 : ℝ)) (c := (95449724058892796899/95460000000000000000 : ℝ)) (alpha := (2253885686087/1909200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (95449724058892796899/95460000000000000000 : ℝ)*(X 0 2+X 1 2)+(2253885686087/1909200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (4567/100000 : ℝ)) (hi := (23659/100000 : ℝ)) (c := (95449724058892796899/95460000000000000000 : ℝ)) (alpha := (2253885686087/1909200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-407331451/2500000000 : ℝ)*X 0 0+(2753602501/5000000000 : ℝ)*X 0 1+(1283767041/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((6705593/12500000 : ℝ)*X 1 0+(-911581783/5000000000 : ℝ)*X 1 1+(1027013589/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364475379/10000000000 : ℝ)*X 2 0+(256753339/500000000 : ℝ)*X 2 1+(-455790949/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183030709/10000000000 : ℝ)*X 0 0+(932461969/2500000000 : ℝ)*X 0 1+(93514017/200000000 : ℝ)*X 0 2+(4183030709/10000000000 : ℝ)*X 1 0+(932461969/2500000000 : ℝ)*X 1 1+(93514017/200000000 : ℝ)*X 1 2+(4183030709/10000000000 : ℝ)*X 2 0+(932461969/2500000000 : ℝ)*X 2 1+(93514017/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50921947/312500000 : ℝ)*X 0 0+(642366429/1250000000 : ℝ)*X 0 1+(2751642431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265128143/10000000000 : ℝ)*X 1 0+(-145494633/1000000000 : ℝ)*X 1 1+(5503284851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632564017/5000000000 : ℝ)*X 2 0+(2751642511/5000000000 : ℝ)*X 2 1+(-4546707/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2091738199/5000000000 : ℝ)*X 0 0+(4665880473/10000000000 : ℝ)*X 0 1+(3739812479/10000000000 : ℝ)*X 0 2+(2091738199/5000000000 : ℝ)*X 1 0+(4665880473/10000000000 : ℝ)*X 1 1+(3739812479/10000000000 : ℝ)*X 1 2+(2091738199/5000000000 : ℝ)*X 2 0+(4665880473/10000000000 : ℝ)*X 2 1+(3739812479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152410775411941604440361141/79550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12535189/100000000000000 : ℝ)*(base1) + (134197543/100000000000000 : ℝ)*(base19) + (739640723/100000000000000 : ℝ)*(base23) + (3307837/3125000000000 : ℝ)*(lower2) + (167564171/100000000000000 : ℝ)*(lower4) + (35689783/100000000000000 : ℝ)*(upper5) + (93610763784041/5000000000000 : ℝ)*(major0) + (93610763784041/5000000000000 : ℝ)*(major1) + (93610763784041/5000000000000 : ℝ)*(major2) + (671795530476221/25000000000000 : ℝ)*(sp0) + (335897746896519/12500000000000 : ℝ)*(sp1) + (671795342432243/25000000000000 : ℝ)*(sp2) + (1057247489634459/100000000000000 : ℝ)*(sp3) + (87595857/10000000000000 : ℝ)*(sp7) + (528624189064109/50000000000000 : ℝ)*(f.failure) + (537436421873939/20000000000000 : ℝ)*(f.sum) + (611010859007/74578125000000000000000000 : ℝ)*base66 + (2826848113923761141/477300000000000000000000000000000 : ℝ)*base68 + (206056558330038859/477300000000000000000000000000000 : ℝ)*base69 + (2624448394545461141/477300000000000000000000000000000 : ℝ)*base72 + (31781686826159/4773000000000000000000000000 : ℝ)*base74 + (1768090177202838859/477300000000000000000000000000000 : ℝ)*base75 + (1575757436502138859/477300000000000000000000000000000 : ℝ)*base77 + (1570172942974638859/477300000000000000000000000000000 : ℝ)*base79 + (721574547197/4773000000000000000000000000 : ℝ)*base82 + (4346821/5000000000000000000000 : ℝ)*base89 + (4346821/5000000000000000000000 : ℝ)*base91 + (4346821/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (184430434193810012403181253/15910000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2077711923/100000000000000 : ℝ)*(base19) + (417059073/20000000000000 : ℝ)*(base23) + (54658747/20000000000000 : ℝ)*(upper3) + (4807719/20000000000000 : ℝ)*(lower4) + (275777001/100000000000000 : ℝ)*(upper5) + (19122110544349/1000000000000 : ℝ)*(major0) + (19122110544349/1000000000000 : ℝ)*(major1) + (19122110544349/1000000000000 : ℝ)*(major2) + (17869225319/100000000000000 : ℝ)*(sp1) + (3772506067/20000000000000 : ℝ)*(sp2) + (2744587548372639/100000000000000 : ℝ)*(sp4) + (2744567601435397/100000000000000 : ℝ)*(sp5) + (2744566600546939/100000000000000 : ℝ)*(sp6) + (539917087046781/50000000000000 : ℝ)*(sp7) + (539917087046781/50000000000000 : ℝ)*(f.failure) + (2744587548372639/100000000000000 : ℝ)*(f.sum) + (5987959747969/954600000000000000000000000 : ℝ)*base66 + (609288401204716249/95460000000000000000000000000000 : ℝ)*base68 + (372093893380036249/95460000000000000000000000000000 : ℝ)*base70 + (1223951252939296249/95460000000000000000000000000000 : ℝ)*base72 + (5388253599289/4773000000000000000000000000 : ℝ)*base73 + (1021305848922676249/95460000000000000000000000000000 : ℝ)*base76 + (1077085901658496249/95460000000000000000000000000000 : ℝ)*base78 + (743078446413316249/95460000000000000000000000000000 : ℝ)*base80 + (17092580735221/4773000000000000000000000000 : ℝ)*base81 + (58797589/5000000000000000000000 : ℝ)*base89 + (58797589/5000000000000000000000 : ℝ)*base91 + (58797589/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1636_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23659/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4567/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4779/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17457/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1636_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1636_s2_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1640047683/10000000000 : ℝ)*x 0 + (5456233617/10000000000 : ℝ)*x 1 + (5178984633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1640047683/10000000000 : ℝ)^4863 ≤ (10125822967857/100000000000000 : ℝ)^3839 := by
    have hnat : (1640047683 : ℕ)^4863*100000000000000^3839 ≤ 10125822967857^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640047683 10000000000 10125822967857 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456233617/10000000000 : ℝ)^4863 ≤ (9284163894089/20000000000000 : ℝ)^3839 := by
    have hnat : (5456233617 : ℕ)^4863*20000000000000^3839 ≤ 9284163894089^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456233617 10000000000 9284163894089 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178984633/10000000000 : ℝ)^4863 ≤ (4345335754589/10000000000000 : ℝ)^3839 := by
    have hnat : (5178984633 : ℕ)^4863*10000000000000^3839 ≤ 4345335754589^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178984633 10000000000 4345335754589 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1640047683/10000000000 : ℝ), (5456233617/10000000000 : ℝ), (5178984633/10000000000 : ℝ)] ![(10125822967857/100000000000000 : ℝ), (9284163894089/20000000000000 : ℝ), (4345335754589/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1640047683/10000000000 : ℝ)|^4863 ≤ (10125822967857/100000000000000 : ℝ)^3839
        have hw : |(-1640047683/10000000000 : ℝ)|=(1640047683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456233617/10000000000 : ℝ)|^4863 ≤ (9284163894089/20000000000000 : ℝ)^3839
        have hw : |(5456233617/10000000000 : ℝ)|=(5456233617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178984633/10000000000 : ℝ)|^4863 ≤ (4345335754589/10000000000000 : ℝ)^3839
        have hw : |(5178984633/10000000000 : ℝ)|=(5178984633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s2_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351050203/10000000000 : ℝ)*x 0 + (-891493307/5000000000 : ℝ)*x 1 + (1294746333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351050203/10000000000 : ℝ)^4863 ≤ (45290164939773/100000000000000 : ℝ)^3839 := by
    have hnat : (5351050203 : ℕ)^4863*100000000000000^3839 ≤ 45290164939773^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351050203 10000000000 45290164939773 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891493307/5000000000 : ℝ)^4863 ≤ (140705875861/1250000000000 : ℝ)^3839 := by
    have hnat : (891493307 : ℕ)^4863*1250000000000^3839 ≤ 140705875861^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891493307 5000000000 140705875861 1250000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294746333/2500000000 : ℝ)^4863 ≤ (4345336497509/10000000000000 : ℝ)^3839 := by
    have hnat : (1294746333 : ℕ)^4863*10000000000000^3839 ≤ 4345336497509^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294746333 2500000000 4345336497509 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351050203/10000000000 : ℝ), (-891493307/5000000000 : ℝ), (1294746333/2500000000 : ℝ)] ![(45290164939773/100000000000000 : ℝ), (140705875861/1250000000000 : ℝ), (4345336497509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351050203/10000000000 : ℝ)|^4863 ≤ (45290164939773/100000000000000 : ℝ)^3839
        have hw : |(5351050203/10000000000 : ℝ)|=(5351050203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-891493307/5000000000 : ℝ)|^4863 ≤ (140705875861/1250000000000 : ℝ)^3839
        have hw : |(-891493307/5000000000 : ℝ)|=(891493307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294746333/2500000000 : ℝ)|^4863 ≤ (4345336497509/10000000000000 : ℝ)^3839
        have hw : |(1294746333/2500000000 : ℝ)|=(1294746333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s2_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351052897/10000000000 : ℝ)*x 0 + (5178984029/10000000000 : ℝ)*x 1 + (-891492367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351052897/10000000000 : ℝ)^4863 ≤ (11322548455799/25000000000000 : ℝ)^3839 := by
    have hnat : (5351052897 : ℕ)^4863*25000000000000^3839 ≤ 11322548455799^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351052897 10000000000 11322548455799 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178984029/10000000000 : ℝ)^4863 ≤ (43453351126381/100000000000000 : ℝ)^3839 := by
    have hnat : (5178984029 : ℕ)^4863*100000000000000^3839 ≤ 43453351126381^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178984029 10000000000 43453351126381 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891492367/5000000000 : ℝ)^4863 ≤ (5628227517033/50000000000000 : ℝ)^3839 := by
    have hnat : (891492367 : ℕ)^4863*50000000000000^3839 ≤ 5628227517033^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891492367 5000000000 5628227517033 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351052897/10000000000 : ℝ), (5178984029/10000000000 : ℝ), (-891492367/5000000000 : ℝ)] ![(11322548455799/25000000000000 : ℝ), (43453351126381/100000000000000 : ℝ), (5628227517033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351052897/10000000000 : ℝ)|^4863 ≤ (11322548455799/25000000000000 : ℝ)^3839
        have hw : |(5351052897/10000000000 : ℝ)|=(5351052897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178984029/10000000000 : ℝ)|^4863 ≤ (43453351126381/100000000000000 : ℝ)^3839
        have hw : |(5178984029/10000000000 : ℝ)|=(5178984029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-891492367/5000000000 : ℝ)|^4863 ≤ (5628227517033/50000000000000 : ℝ)^3839
        have hw : |(-891492367/5000000000 : ℝ)|=(891492367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s2_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419099653/1000000000 : ℝ)*x 0 + (3849620493/10000000000 : ℝ)*x 1 + (227714923/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419099653/1000000000 : ℝ)^4863 ≤ (33233469278387/100000000000000 : ℝ)^3839 := by
    have hnat : (419099653 : ℕ)^4863*100000000000000^3839 ≤ 33233469278387^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419099653 1000000000 33233469278387 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3849620493/10000000000 : ℝ)^4863 ≤ (116571915379/390625000000 : ℝ)^3839 := by
    have hnat : (3849620493 : ℕ)^4863*390625000000^3839 ≤ 116571915379^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3849620493 10000000000 116571915379 390625000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227714923/500000000 : ℝ)^4863 ≤ (36924120369447/100000000000000 : ℝ)^3839 := by
    have hnat : (227714923 : ℕ)^4863*100000000000000^3839 ≤ 36924120369447^3839*500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227714923 500000000 36924120369447 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419099653/1000000000 : ℝ), (3849620493/10000000000 : ℝ), (227714923/500000000 : ℝ)] ![(33233469278387/100000000000000 : ℝ), (116571915379/390625000000 : ℝ), (36924120369447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419099653/1000000000 : ℝ)|^4863 ≤ (33233469278387/100000000000000 : ℝ)^3839
        have hw : |(419099653/1000000000 : ℝ)|=(419099653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3849620493/10000000000 : ℝ)|^4863 ≤ (116571915379/390625000000 : ℝ)^3839
        have hw : |(3849620493/10000000000 : ℝ)|=(3849620493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227714923/500000000 : ℝ)|^4863 ≤ (36924120369447/100000000000000 : ℝ)^3839
        have hw : |(227714923/500000000 : ℝ)|=(227714923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s2_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1640119453/10000000000 : ℝ)*x 0 + (5181136053/10000000000 : ℝ)*x 1 + (13635149/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1640119453/10000000000 : ℝ)^4863 ≤ (2025276856273/20000000000000 : ℝ)^3839 := by
    have hnat : (1640119453 : ℕ)^4863*20000000000000^3839 ≤ 2025276856273^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640119453 10000000000 2025276856273 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181136053/10000000000 : ℝ)^4863 ≤ (8695244961221/20000000000000 : ℝ)^3839 := by
    have hnat : (5181136053 : ℕ)^4863*20000000000000^3839 ≤ 8695244961221^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181136053 10000000000 8695244961221 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13635149/25000000 : ℝ)^4863 ≤ (9279478179267/20000000000000 : ℝ)^3839 := by
    have hnat : (13635149 : ℕ)^4863*20000000000000^3839 ≤ 9279478179267^3839*25000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13635149 25000000 9279478179267 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1640119453/10000000000 : ℝ), (5181136053/10000000000 : ℝ), (13635149/25000000 : ℝ)] ![(2025276856273/20000000000000 : ℝ), (8695244961221/20000000000000 : ℝ), (9279478179267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1640119453/10000000000 : ℝ)|^4863 ≤ (2025276856273/20000000000000 : ℝ)^3839
        have hw : |(-1640119453/10000000000 : ℝ)|=(1640119453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181136053/10000000000 : ℝ)|^4863 ≤ (8695244961221/20000000000000 : ℝ)^3839
        have hw : |(5181136053/10000000000 : ℝ)|=(5181136053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13635149/25000000 : ℝ)|^4863 ≤ (9279478179267/20000000000000 : ℝ)^3839
        have hw : |(13635149/25000000 : ℝ)|=(13635149/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s2_5 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638555289/5000000000 : ℝ)*x 0 + (-753955051/5000000000 : ℝ)*x 1 + (681757473/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638555289/5000000000 : ℝ)^4863 ≤ (44498895349497/100000000000000 : ℝ)^3839 := by
    have hnat : (2638555289 : ℕ)^4863*100000000000000^3839 ≤ 44498895349497^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638555289 5000000000 44498895349497 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (753955051/5000000000 : ℝ)^4863 ≤ (1820742352217/20000000000000 : ℝ)^3839 := by
    have hnat : (753955051 : ℕ)^4863*20000000000000^3839 ≤ 1820742352217^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753955051 5000000000 1820742352217 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681757473/1250000000 : ℝ)^4863 ≤ (46397392879129/100000000000000 : ℝ)^3839 := by
    have hnat : (681757473 : ℕ)^4863*100000000000000^3839 ≤ 46397392879129^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681757473 1250000000 46397392879129 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638555289/5000000000 : ℝ), (-753955051/5000000000 : ℝ), (681757473/1250000000 : ℝ)] ![(44498895349497/100000000000000 : ℝ), (1820742352217/20000000000000 : ℝ), (46397392879129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638555289/5000000000 : ℝ)|^4863 ≤ (44498895349497/100000000000000 : ℝ)^3839
        have hw : |(2638555289/5000000000 : ℝ)|=(2638555289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-753955051/5000000000 : ℝ)|^4863 ≤ (1820742352217/20000000000000 : ℝ)^3839
        have hw : |(-753955051/5000000000 : ℝ)|=(753955051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681757473/1250000000 : ℝ)|^4863 ≤ (46397392879129/100000000000000 : ℝ)^3839
        have hw : |(681757473/1250000000 : ℝ)|=(681757473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s2_6 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527711147/1000000000 : ℝ)*x 0 + (1090811773/2000000000 : ℝ)*x 1 + (-1507910151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527711147/1000000000 : ℝ)^4863 ≤ (11124726219387/25000000000000 : ℝ)^3839 := by
    have hnat : (527711147 : ℕ)^4863*25000000000000^3839 ≤ 11124726219387^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527711147 1000000000 11124726219387 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090811773/2000000000 : ℝ)^4863 ≤ (23198691487967/50000000000000 : ℝ)^3839 := by
    have hnat : (1090811773 : ℕ)^4863*50000000000000^3839 ≤ 23198691487967^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090811773 2000000000 23198691487967 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507910151/10000000000 : ℝ)^4863 ≤ (9103712135821/100000000000000 : ℝ)^3839 := by
    have hnat : (1507910151 : ℕ)^4863*100000000000000^3839 ≤ 9103712135821^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507910151 10000000000 9103712135821 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527711147/1000000000 : ℝ), (1090811773/2000000000 : ℝ), (-1507910151/10000000000 : ℝ)] ![(11124726219387/25000000000000 : ℝ), (23198691487967/50000000000000 : ℝ), (9103712135821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527711147/1000000000 : ℝ)|^4863 ≤ (11124726219387/25000000000000 : ℝ)^3839
        have hw : |(527711147/1000000000 : ℝ)|=(527711147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090811773/2000000000 : ℝ)|^4863 ≤ (23198691487967/50000000000000 : ℝ)^3839
        have hw : |(1090811773/2000000000 : ℝ)|=(1090811773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1507910151/10000000000 : ℝ)|^4863 ≤ (9103712135821/100000000000000 : ℝ)^3839
        have hw : |(-1507910151/10000000000 : ℝ)|=(1507910151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s2_7 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095590501/5000000000 : ℝ)*x 0 + (142151017/312500000 : ℝ)*x 1 + (385514639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095590501/5000000000 : ℝ)^4863 ≤ (8308830571861/25000000000000 : ℝ)^3839 := by
    have hnat : (2095590501 : ℕ)^4863*25000000000000^3839 ≤ 8308830571861^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095590501 5000000000 8308830571861 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142151017/312500000 : ℝ)^4863 ≤ (36867993833403/100000000000000 : ℝ)^3839 := by
    have hnat : (142151017 : ℕ)^4863*100000000000000^3839 ≤ 36867993833403^3839*312500000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142151017 312500000 36867993833403 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385514639/1000000000 : ℝ)^4863 ≤ (29896683861871/100000000000000 : ℝ)^3839 := by
    have hnat : (385514639 : ℕ)^4863*100000000000000^3839 ≤ 29896683861871^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385514639 1000000000 29896683861871 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095590501/5000000000 : ℝ), (142151017/312500000 : ℝ), (385514639/1000000000 : ℝ)] ![(8308830571861/25000000000000 : ℝ), (36867993833403/100000000000000 : ℝ), (29896683861871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095590501/5000000000 : ℝ)|^4863 ≤ (8308830571861/25000000000000 : ℝ)^3839
        have hw : |(2095590501/5000000000 : ℝ)|=(2095590501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142151017/312500000 : ℝ)|^4863 ≤ (36867993833403/100000000000000 : ℝ)^3839
        have hw : |(142151017/312500000 : ℝ)|=(142151017/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385514639/1000000000 : ℝ)|^4863 ≤ (29896683861871/100000000000000 : ℝ)^3839
        have hw : |(385514639/1000000000 : ℝ)|=(385514639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17457/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4779/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5253/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16393/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17457/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4779/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17457/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4779/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17457/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4779/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17457/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4779/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17457/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4779/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17457/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4779/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4779/50000 : ℝ) ^ (4859/1024 : ℝ) ≤ (362795640432693/25000000000000000000 : ℝ) := by
    have hpowers : (4779/50000 : ℝ)^4859 ≤ (362795640432693/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4779 : ℕ)^4859*25000000000000000000^1024 ≤ 362795640432693^1024*50000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4779 50000 362795640432693 25000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4779/50000 : ℝ)) (X := (362795640432693/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17457/100000 : ℝ) ^ (4859/1024 : ℝ) ≤ (25296298470004713/100000000000000000000 : ℝ) := by
    have hpowers : (17457/100000 : ℝ)^4859 ≤ (25296298470004713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17457 : ℕ)^4859*100000000000000000000^1024 ≤ 25296298470004713^1024*100000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17457 100000 25296298470004713 100000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17457/100000 : ℝ)) (X := (25296298470004713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500362795640432693/12500000000000000000 : ℝ) ≤ (10000061164598617/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (12500362795640432693/12500000000000000000 : ℝ)^1024 ≤ (10000061164598617/10000000000000000 : ℝ)^4859 := by
      have hnat : (12500362795640432693 : ℕ)^1024*10000000000000000^4859 ≤ 10000061164598617^4859*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500362795640432693 12500000000000000000 10000061164598617 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061164598617/10000000000000000 : ℝ)) (X := (12500362795640432693/12500000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005349496206347097/20000000000000000000 : ℝ) ≤ (10000563624819859/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (20005349496206347097/20000000000000000000 : ℝ)^1024 ≤ (10000563624819859/10000000000000000 : ℝ)^4859 := by
      have hnat : (20005349496206347097 : ℕ)^1024*10000000000000000^4859 ≤ 10000563624819859^4859*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005349496206347097 20000000000000000000 10000563624819859 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000563624819859/10000000000000000 : ℝ)) (X := (20005349496206347097/20000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025296298470004713/50000000000000000000 : ℝ) ≤ (10001066085041101/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50025296298470004713/50000000000000000000 : ℝ)^1024 ≤ (10001066085041101/10000000000000000 : ℝ)^4859 := by
      have hnat : (50025296298470004713 : ℕ)^1024*10000000000000000^4859 ≤ 10001066085041101^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025296298470004713 50000000000000000000 10001066085041101 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001066085041101/10000000000000000 : ℝ)) (X := (50025296298470004713/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(362795640432693/25000000000000000000 : ℝ) ≤ ((26326959369858404537/26330000000000000000 : ℝ)+2*(83743370207/131650000000000 : ℝ)*(4779/50000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (26326959369858404537/26330000000000000000 : ℝ)+2*(83743370207/131650000000000 : ℝ)*(4779/50000 : ℝ)=(10000061164598617/10000000000000000 : ℝ) by norm_num, show 1+2*(362795640432693/25000000000000000000 : ℝ)=(12500362795640432693/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25296298470004713/100000000000000000000 : ℝ)+(362795640432693/25000000000000000000 : ℝ) ≤ ((26326959369858404537/26330000000000000000 : ℝ)+(83743370207/131650000000000 : ℝ)*((17457/100000 : ℝ)+(4779/50000 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (26326959369858404537/26330000000000000000 : ℝ)+(83743370207/131650000000000 : ℝ)*((17457/100000 : ℝ)+(4779/50000 : ℝ))=(10000563624819859/10000000000000000 : ℝ) by norm_num, show 1+(25296298470004713/100000000000000000000 : ℝ)+(362795640432693/25000000000000000000 : ℝ)=(20005349496206347097/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25296298470004713/100000000000000000000 : ℝ) ≤ ((26326959369858404537/26330000000000000000 : ℝ)+2*(83743370207/131650000000000 : ℝ)*(17457/100000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (26326959369858404537/26330000000000000000 : ℝ)+2*(83743370207/131650000000000 : ℝ)*(17457/100000 : ℝ)=(10001066085041101/10000000000000000 : ℝ) by norm_num, show 1+2*(25296298470004713/100000000000000000000 : ℝ)=(50025296298470004713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26326959369858404537/26330000000000000000 : ℝ)*(X 1 0+X 2 0)+(83743370207/131650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (4779/50000 : ℝ)) (hi := (17457/100000 : ℝ)) (c := (26326959369858404537/26330000000000000000 : ℝ)) (alpha := (83743370207/131650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26326959369858404537/26330000000000000000 : ℝ)*(X 0 1+X 2 1)+(83743370207/131650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (4779/50000 : ℝ)) (hi := (17457/100000 : ℝ)) (c := (26326959369858404537/26330000000000000000 : ℝ)) (alpha := (83743370207/131650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26326959369858404537/26330000000000000000 : ℝ)*(X 0 2+X 1 2)+(83743370207/131650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (4779/50000 : ℝ)) (hi := (17457/100000 : ℝ)) (c := (26326959369858404537/26330000000000000000 : ℝ)) (alpha := (83743370207/131650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1640047683/10000000000 : ℝ)*X 0 0+(5456233617/10000000000 : ℝ)*X 0 1+(5178984633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351050203/10000000000 : ℝ)*X 1 0+(-891493307/5000000000 : ℝ)*X 1 1+(1294746333/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351052897/10000000000 : ℝ)*X 2 0+(5178984029/10000000000 : ℝ)*X 2 1+(-891492367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419099653/1000000000 : ℝ)*X 0 0+(3849620493/10000000000 : ℝ)*X 0 1+(227714923/500000000 : ℝ)*X 0 2+(419099653/1000000000 : ℝ)*X 1 0+(3849620493/10000000000 : ℝ)*X 1 1+(227714923/500000000 : ℝ)*X 1 2+(419099653/1000000000 : ℝ)*X 2 0+(3849620493/10000000000 : ℝ)*X 2 1+(227714923/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1640119453/10000000000 : ℝ)*X 0 0+(5181136053/10000000000 : ℝ)*X 0 1+(13635149/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638555289/5000000000 : ℝ)*X 1 0+(-753955051/5000000000 : ℝ)*X 1 1+(681757473/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527711147/1000000000 : ℝ)*X 2 0+(1090811773/2000000000 : ℝ)*X 2 1+(-1507910151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2095590501/5000000000 : ℝ)*X 0 0+(142151017/312500000 : ℝ)*X 0 1+(385514639/1000000000 : ℝ)*X 0 2+(2095590501/5000000000 : ℝ)*X 1 0+(142151017/312500000 : ℝ)*X 1 1+(385514639/1000000000 : ℝ)*X 1 2+(2095590501/5000000000 : ℝ)*X 2 0+(142151017/312500000 : ℝ)*X 2 1+(385514639/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3085454508138416895397328271/658250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151218261/10000000000000 : ℝ)*(base23) + (14890469/20000000000000 : ℝ)*(lower2) + (41042479/20000000000000 : ℝ)*(upper4) + (229021977/50000000000000 : ℝ)*(upper5) + (2512996876268061/100000000000000 : ℝ)*(major0) + (2512996876268061/100000000000000 : ℝ)*(major1) + (2512996876268061/100000000000000 : ℝ)*(major2) + (1803433980210959/50000000000000 : ℝ)*(sp0) + (901719281489947/25000000000000 : ℝ)*(sp1) + (901722864266623/25000000000000 : ℝ)*(sp2) + (1419093845236427/100000000000000 : ℝ)*(sp3) + (1563051699/6250000000000 : ℝ)*(sp4) + (3168657863/20000000000000 : ℝ)*(sp5) + (1356361053/20000000000000 : ℝ)*(sp7) + (354775156760423/25000000000000 : ℝ)*(f.failure) + (1803446484624551/50000000000000 : ℝ)*(f.sum) + (10137817232343/1645625000000000000000000000 : ℝ)*base65 + (9687645622841007243/2633000000000000000000000000000000 : ℝ)*base68 + (7444522977196007243/2633000000000000000000000000000000 : ℝ)*base70 + (22166380621326007243/2633000000000000000000000000000000 : ℝ)*base72 + (55841861876731/13165000000000000000000000000 : ℝ)*base74 + (19392247798102007243/2633000000000000000000000000000000 : ℝ)*base76 + (8139143187103992757/2633000000000000000000000000000000 : ℝ)*base77 + (10990912454471007243/2633000000000000000000000000000000 : ℝ)*base80 + (145140578669/3291250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9874287/2500000000000000000000 : ℝ)*base89 + (9874287/2500000000000000000000 : ℝ)*base91 + (9874287/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1386722998578240838921270227/329125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252054831/100000000000000 : ℝ)*(base19) + (623376313/50000000000000 : ℝ)*(base23) + (32112143/20000000000000 : ℝ)*(lower4) + (51976591/100000000000000 : ℝ)*(lower5) + (638201134866819/25000000000000 : ℝ)*(major0) + (638201134866819/25000000000000 : ℝ)*(major1) + (638201134866819/25000000000000 : ℝ)*(major2) + (3308208857/50000000000000 : ℝ)*(sp1) + (2922671579/25000000000000 : ℝ)*(sp2) + (675007403/25000000000000 : ℝ)*(sp3) + (3664028745181127/100000000000000 : ℝ)*(sp4) + (1832010938354291/50000000000000 : ℝ)*(sp5) + (732803161548437/20000000000000 : ℝ)*(sp6) + (72078874663919/5000000000000 : ℝ)*(sp7) + (1441580193307991/100000000000000 : ℝ)*(f.failure) + (3664028745181127/100000000000000 : ℝ)*(f.sum) + (93576529196921/13165000000000000000000000000 : ℝ)*base66 + (8691157229550792197/658250000000000000000000000000000 : ℝ)*base68 + (6692384891463042197/658250000000000000000000000000000 : ℝ)*base70 + (5991114658601542197/658250000000000000000000000000000 : ℝ)*base72 + (19819315068069/3291250000000000000000000000 : ℝ)*base74 + (10057140441985042197/658250000000000000000000000000000 : ℝ)*base76 + (10525366480479542197/658250000000000000000000000000000 : ℝ)*base78 + (9501920764779292197/658250000000000000000000000000000 : ℝ)*base80 + (39646189004501/13165000000000000000000000000 : ℝ)*base82 + (24098079/10000000000000000000000 : ℝ)*base89 + (24098079/10000000000000000000000 : ℝ)*base91 + (24098079/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1636_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17457/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4779/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1636_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1636_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1636_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1636_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1636_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1636_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
