-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1329_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:47.242762+00:00
-- url     : https://prove2.me/submissions/2d4fbe13-734f-409d-9e62-7b25ad200f0c

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
theorem support_rectangle_w1329_s3_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-256669487/1250000000 : ℝ)*x 0 + (2714435981/5000000000 : ℝ)*x 1 + (5229952829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256669487/1250000000 : ℝ)^4289 ≤ (12497777728719/100000000000000 : ℝ)^3265 := by
    have hnat : (256669487 : ℕ)^4289*100000000000000^3265 ≤ 12497777728719^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256669487 1250000000 12497777728719 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714435981/5000000000 : ℝ)^4289 ≤ (44823599506169/100000000000000 : ℝ)^3265 := by
    have hnat : (2714435981 : ℕ)^4289*100000000000000^3265 ≤ 44823599506169^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714435981 5000000000 44823599506169 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229952829/10000000000 : ℝ)^4289 ≤ (133370696071/312500000000 : ℝ)^3265 := by
    have hnat : (5229952829 : ℕ)^4289*312500000000^3265 ≤ 133370696071^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229952829 10000000000 133370696071 312500000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256669487/1250000000 : ℝ), (2714435981/5000000000 : ℝ), (5229952829/10000000000 : ℝ)] ![(12497777728719/100000000000000 : ℝ), (44823599506169/100000000000000 : ℝ), (133370696071/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256669487/1250000000 : ℝ)|^4289 ≤ (12497777728719/100000000000000 : ℝ)^3265
        have hw : |(-256669487/1250000000 : ℝ)|=(256669487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714435981/5000000000 : ℝ)|^4289 ≤ (44823599506169/100000000000000 : ℝ)^3265
        have hw : |(2714435981/5000000000 : ℝ)|=(2714435981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229952829/10000000000 : ℝ)|^4289 ≤ (133370696071/312500000000 : ℝ)^3265
        have hw : |(5229952829/10000000000 : ℝ)|=(5229952829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s3_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133829037/250000000 : ℝ)*x 0 + (-431010613/2000000000 : ℝ)*x 1 + (5229952661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133829037/250000000 : ℝ)^4289 ≤ (2200212222441/5000000000000 : ℝ)^3265 := by
    have hnat : (133829037 : ℕ)^4289*5000000000000^3265 ≤ 2200212222441^3265*250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133829037 250000000 2200212222441 5000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431010613/2000000000 : ℝ)^4289 ≤ (2663426919577/20000000000000 : ℝ)^3265 := by
    have hnat : (431010613 : ℕ)^4289*20000000000000^3265 ≤ 2663426919577^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431010613 2000000000 2663426919577 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229952661/10000000000 : ℝ)^4289 ≤ (42678620941799/100000000000000 : ℝ)^3265 := by
    have hnat : (5229952661 : ℕ)^4289*100000000000000^3265 ≤ 42678620941799^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229952661 10000000000 42678620941799 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133829037/250000000 : ℝ), (-431010613/2000000000 : ℝ), (5229952661/10000000000 : ℝ)] ![(2200212222441/5000000000000 : ℝ), (2663426919577/20000000000000 : ℝ), (42678620941799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133829037/250000000 : ℝ)|^4289 ≤ (2200212222441/5000000000000 : ℝ)^3265
        have hw : |(133829037/250000000 : ℝ)|=(133829037/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431010613/2000000000 : ℝ)|^4289 ≤ (2663426919577/20000000000000 : ℝ)^3265
        have hw : |(-431010613/2000000000 : ℝ)|=(431010613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229952661/10000000000 : ℝ)|^4289 ≤ (42678620941799/100000000000000 : ℝ)^3265
        have hw : |(5229952661/10000000000 : ℝ)|=(5229952661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s3_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353161629/10000000000 : ℝ)*x 0 + (5229952393/10000000000 : ℝ)*x 1 + (-2155053221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353161629/10000000000 : ℝ)^4289 ≤ (44004246057773/100000000000000 : ℝ)^3265 := by
    have hnat : (5353161629 : ℕ)^4289*100000000000000^3265 ≤ 44004246057773^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353161629 10000000000 44004246057773 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229952393/10000000000 : ℝ)^4289 ≤ (426786180689/1000000000000 : ℝ)^3265 := by
    have hnat : (5229952393 : ℕ)^4289*1000000000000^3265 ≤ 426786180689^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229952393 10000000000 426786180689 1000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155053221/10000000000 : ℝ)^4289 ≤ (532685434569/4000000000000 : ℝ)^3265 := by
    have hnat : (2155053221 : ℕ)^4289*4000000000000^3265 ≤ 532685434569^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155053221 10000000000 532685434569 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353161629/10000000000 : ℝ), (5229952393/10000000000 : ℝ), (-2155053221/10000000000 : ℝ)] ![(44004246057773/100000000000000 : ℝ), (426786180689/1000000000000 : ℝ), (532685434569/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353161629/10000000000 : ℝ)|^4289 ≤ (44004246057773/100000000000000 : ℝ)^3265
        have hw : |(5353161629/10000000000 : ℝ)|=(5353161629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229952393/10000000000 : ℝ)|^4289 ≤ (426786180689/1000000000000 : ℝ)^3265
        have hw : |(5229952393/10000000000 : ℝ)|=(5229952393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155053221/10000000000 : ℝ)|^4289 ≤ (532685434569/4000000000000 : ℝ)^3265
        have hw : |(-2155053221/10000000000 : ℝ)|=(2155053221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s3_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541110359/1250000000 : ℝ)*x 0 + (515779897/1250000000 : ℝ)*x 1 + (908170573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541110359/1250000000 : ℝ)^4289 ≤ (8322860474747/25000000000000 : ℝ)^3265 := by
    have hnat : (541110359 : ℕ)^4289*25000000000000^3265 ≤ 8322860474747^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541110359 1250000000 8322860474747 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515779897/1250000000 : ℝ)^4289 ≤ (31259422727491/100000000000000 : ℝ)^3265 := by
    have hnat : (515779897 : ℕ)^4289*100000000000000^3265 ≤ 31259422727491^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515779897 1250000000 31259422727491 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (908170573/2000000000 : ℝ)^4289 ≤ (35449135363499/100000000000000 : ℝ)^3265 := by
    have hnat : (908170573 : ℕ)^4289*100000000000000^3265 ≤ 35449135363499^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908170573 2000000000 35449135363499 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541110359/1250000000 : ℝ), (515779897/1250000000 : ℝ), (908170573/2000000000 : ℝ)] ![(8322860474747/25000000000000 : ℝ), (31259422727491/100000000000000 : ℝ), (35449135363499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541110359/1250000000 : ℝ)|^4289 ≤ (8322860474747/25000000000000 : ℝ)^3265
        have hw : |(541110359/1250000000 : ℝ)|=(541110359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515779897/1250000000 : ℝ)|^4289 ≤ (31259422727491/100000000000000 : ℝ)^3265
        have hw : |(515779897/1250000000 : ℝ)|=(515779897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(908170573/2000000000 : ℝ)|^4289 ≤ (35449135363499/100000000000000 : ℝ)^3265
        have hw : |(908170573/2000000000 : ℝ)|=(908170573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s3_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2053376099/10000000000 : ℝ)*x 0 + (326924263/625000000 : ℝ)*x 1 + (1357007843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053376099/10000000000 : ℝ)^4289 ≤ (12497939260493/100000000000000 : ℝ)^3265 := by
    have hnat : (2053376099 : ℕ)^4289*100000000000000^3265 ≤ 12497939260493^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053376099 10000000000 12497939260493 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326924263/625000000 : ℝ)^4289 ≤ (42687578038123/100000000000000 : ℝ)^3265 := by
    have hnat : (326924263 : ℕ)^4289*100000000000000^3265 ≤ 42687578038123^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326924263 625000000 42687578038123 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357007843/2500000000 : ℝ)^4289 ≤ (44814482680207/100000000000000 : ℝ)^3265 := by
    have hnat : (1357007843 : ℕ)^4289*100000000000000^3265 ≤ 44814482680207^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357007843 2500000000 44814482680207 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2053376099/10000000000 : ℝ), (326924263/625000000 : ℝ), (1357007843/2500000000 : ℝ)] ![(12497939260493/100000000000000 : ℝ), (42687578038123/100000000000000 : ℝ), (44814482680207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2053376099/10000000000 : ℝ)|^4289 ≤ (12497939260493/100000000000000 : ℝ)^3265
        have hw : |(-2053376099/10000000000 : ℝ)|=(2053376099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326924263/625000000 : ℝ)|^4289 ≤ (42687578038123/100000000000000 : ℝ)^3265
        have hw : |(326924263/625000000 : ℝ)|=(326924263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357007843/2500000000 : ℝ)|^4289 ≤ (44814482680207/100000000000000 : ℝ)^3265
        have hw : |(1357007843/2500000000 : ℝ)|=(1357007843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s3_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331374983/625000000 : ℝ)*x 0 + (-978487311/5000000000 : ℝ)*x 1 + (339251973/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331374983/625000000 : ℝ)^4289 ≤ (43452612151069/100000000000000 : ℝ)^3265 := by
    have hnat : (331374983 : ℕ)^4289*100000000000000^3265 ≤ 43452612151069^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331374983 625000000 43452612151069 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978487311/5000000000 : ℝ)^4289 ≤ (11732903026229/100000000000000 : ℝ)^3265 := by
    have hnat : (978487311 : ℕ)^4289*100000000000000^3265 ≤ 11732903026229^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978487311 5000000000 11732903026229 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339251973/625000000 : ℝ)^4289 ≤ (22407242402961/50000000000000 : ℝ)^3265 := by
    have hnat : (339251973 : ℕ)^4289*50000000000000^3265 ≤ 22407242402961^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339251973 625000000 22407242402961 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331374983/625000000 : ℝ), (-978487311/5000000000 : ℝ), (339251973/625000000 : ℝ)] ![(43452612151069/100000000000000 : ℝ), (11732903026229/100000000000000 : ℝ), (22407242402961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331374983/625000000 : ℝ)|^4289 ≤ (43452612151069/100000000000000 : ℝ)^3265
        have hw : |(331374983/625000000 : ℝ)|=(331374983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978487311/5000000000 : ℝ)|^4289 ≤ (11732903026229/100000000000000 : ℝ)^3265
        have hw : |(-978487311/5000000000 : ℝ)|=(978487311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339251973/625000000 : ℝ)|^4289 ≤ (22407242402961/50000000000000 : ℝ)^3265
        have hw : |(339251973/625000000 : ℝ)|=(339251973/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s3_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651000707/5000000000 : ℝ)*x 0 + (1357007597/2500000000 : ℝ)*x 1 + (-1956973943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651000707/5000000000 : ℝ)^4289 ≤ (43452630302323/100000000000000 : ℝ)^3265 := by
    have hnat : (2651000707 : ℕ)^4289*100000000000000^3265 ≤ 43452630302323^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651000707 5000000000 43452630302323 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357007597/2500000000 : ℝ)^4289 ≤ (11203618002063/25000000000000 : ℝ)^3265 := by
    have hnat : (1357007597 : ℕ)^4289*25000000000000^3265 ≤ 11203618002063^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357007597 2500000000 11203618002063 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956973943/10000000000 : ℝ)^4289 ≤ (586644883929/5000000000000 : ℝ)^3265 := by
    have hnat : (1956973943 : ℕ)^4289*5000000000000^3265 ≤ 586644883929^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956973943 10000000000 586644883929 5000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651000707/5000000000 : ℝ), (1357007597/2500000000 : ℝ), (-1956973943/10000000000 : ℝ)] ![(43452630302323/100000000000000 : ℝ), (11203618002063/25000000000000 : ℝ), (586644883929/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651000707/5000000000 : ℝ)|^4289 ≤ (43452630302323/100000000000000 : ℝ)^3265
        have hw : |(2651000707/5000000000 : ℝ)|=(2651000707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357007597/2500000000 : ℝ)|^4289 ≤ (11203618002063/25000000000000 : ℝ)^3265
        have hw : |(1357007597/2500000000 : ℝ)|=(1357007597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1956973943/10000000000 : ℝ)|^4289 ≤ (586644883929/5000000000000 : ℝ)^3265
        have hw : |(-1956973943/10000000000 : ℝ)|=(1956973943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s3_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328924929/10000000000 : ℝ)*x 0 + (453911161/1000000000 : ℝ)*x 1 + (2063995297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328924929/10000000000 : ℝ)^4289 ≤ (33291866781233/100000000000000 : ℝ)^3265 := by
    have hnat : (4328924929 : ℕ)^4289*100000000000000^3265 ≤ 33291866781233^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328924929 10000000000 33291866781233 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453911161/1000000000 : ℝ)^4289 ≤ (35431279644791/100000000000000 : ℝ)^3265 := by
    have hnat : (453911161 : ℕ)^4289*100000000000000^3265 ≤ 35431279644791^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453911161 1000000000 35431279644791 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063995297/5000000000 : ℝ)^4289 ≤ (31276853559943/100000000000000 : ℝ)^3265 := by
    have hnat : (2063995297 : ℕ)^4289*100000000000000^3265 ≤ 31276853559943^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063995297 5000000000 31276853559943 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328924929/10000000000 : ℝ), (453911161/1000000000 : ℝ), (2063995297/5000000000 : ℝ)] ![(33291866781233/100000000000000 : ℝ), (35431279644791/100000000000000 : ℝ), (31276853559943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328924929/10000000000 : ℝ)|^4289 ≤ (33291866781233/100000000000000 : ℝ)^3265
        have hw : |(4328924929/10000000000 : ℝ)|=(4328924929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453911161/1000000000 : ℝ)|^4289 ≤ (35431279644791/100000000000000 : ℝ)^3265
        have hw : |(453911161/1000000000 : ℝ)|=(453911161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063995297/5000000000 : ℝ)|^4289 ≤ (31276853559943/100000000000000 : ℝ)^3265
        have hw : |(2063995297/5000000000 : ℝ)|=(2063995297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1953/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5407/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1953/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1953/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1953/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1953/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1953/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1953/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1953/20000 : ℝ) ^ (67/16 : ℝ) ≤ (5878310697392943/100000000000000000000 : ℝ) := by
    have hpowers : (1953/20000 : ℝ)^67 ≤ (5878310697392943/100000000000000000000 : ℝ)^16 := by
      have hnat : (1953 : ℕ)^67*100000000000000000000^16 ≤ 5878310697392943^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1953 20000 5878310697392943 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1953/20000 : ℝ)) (X := (5878310697392943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (16157/100000 : ℝ) ^ (67/16 : ℝ) ≤ (48418411359529149/100000000000000000000 : ℝ) := by
    have hpowers : (16157/100000 : ℝ)^67 ≤ (48418411359529149/100000000000000000000 : ℝ)^16 := by
      have hnat : (16157 : ℕ)^67*100000000000000000000^16 ≤ 48418411359529149^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16157 100000 48418411359529149 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16157/100000 : ℝ)) (X := (48418411359529149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005878310697392943/50000000000000000000 : ℝ) ≤ (5000140371288083/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50005878310697392943/50000000000000000000 : ℝ)^16 ≤ (5000140371288083/5000000000000000 : ℝ)^67 := by
      have hnat : (50005878310697392943 : ℕ)^16*5000000000000000^67 ≤ 5000140371288083^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005878310697392943 50000000000000000000 5000140371288083 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140371288083/5000000000000000 : ℝ)) (X := (50005878310697392943/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013574180514230523/25000000000000000000 : ℝ) ≤ (10001296370271573/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25013574180514230523/25000000000000000000 : ℝ)^16 ≤ (10001296370271573/10000000000000000 : ℝ)^67 := by
      have hnat : (25013574180514230523 : ℕ)^16*10000000000000000^67 ≤ 10001296370271573^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013574180514230523 25000000000000000000 10001296370271573 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001296370271573/10000000000000000 : ℝ)) (X := (25013574180514230523/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048418411359529149/50000000000000000000 : ℝ) ≤ (500115599898349/500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50048418411359529149/50000000000000000000 : ℝ)^16 ≤ (500115599898349/500000000000000 : ℝ)^67 := by
      have hnat : (50048418411359529149 : ℕ)^16*500000000000000^67 ≤ 500115599898349^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048418411359529149 50000000000000000000 500115599898349 500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500115599898349/500000000000000 : ℝ)) (X := (50048418411359529149/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5878310697392943/100000000000000000000 : ℝ) ≤ ((31950979648827777181/31960000000000000000 : ℝ)+2*(1015627695407/639200000000000 : ℝ)*(1953/20000 : ℝ))^(67/16 : ℝ) := by
    rw [show (31950979648827777181/31960000000000000000 : ℝ)+2*(1015627695407/639200000000000 : ℝ)*(1953/20000 : ℝ)=(5000140371288083/5000000000000000 : ℝ) by norm_num, show 1+2*(5878310697392943/100000000000000000000 : ℝ)=(50005878310697392943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48418411359529149/100000000000000000000 : ℝ)+(5878310697392943/100000000000000000000 : ℝ) ≤ ((31950979648827777181/31960000000000000000 : ℝ)+(1015627695407/639200000000000 : ℝ)*((16157/100000 : ℝ)+(1953/20000 : ℝ)))^(67/16 : ℝ) := by
    rw [show (31950979648827777181/31960000000000000000 : ℝ)+(1015627695407/639200000000000 : ℝ)*((16157/100000 : ℝ)+(1953/20000 : ℝ))=(10001296370271573/10000000000000000 : ℝ) by norm_num, show 1+(48418411359529149/100000000000000000000 : ℝ)+(5878310697392943/100000000000000000000 : ℝ)=(25013574180514230523/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48418411359529149/100000000000000000000 : ℝ) ≤ ((31950979648827777181/31960000000000000000 : ℝ)+2*(1015627695407/639200000000000 : ℝ)*(16157/100000 : ℝ))^(67/16 : ℝ) := by
    rw [show (31950979648827777181/31960000000000000000 : ℝ)+2*(1015627695407/639200000000000 : ℝ)*(16157/100000 : ℝ)=(500115599898349/500000000000000 : ℝ) by norm_num, show 1+2*(48418411359529149/100000000000000000000 : ℝ)=(50048418411359529149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31950979648827777181/31960000000000000000 : ℝ)*(X 1 0+X 2 0)+(1015627695407/639200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (1953/20000 : ℝ)) (hi := (16157/100000 : ℝ)) (c := (31950979648827777181/31960000000000000000 : ℝ)) (alpha := (1015627695407/639200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31950979648827777181/31960000000000000000 : ℝ)*(X 0 1+X 2 1)+(1015627695407/639200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (1953/20000 : ℝ)) (hi := (16157/100000 : ℝ)) (c := (31950979648827777181/31960000000000000000 : ℝ)) (alpha := (1015627695407/639200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31950979648827777181/31960000000000000000 : ℝ)*(X 0 2+X 1 2)+(1015627695407/639200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (1953/20000 : ℝ)) (hi := (16157/100000 : ℝ)) (c := (31950979648827777181/31960000000000000000 : ℝ)) (alpha := (1015627695407/639200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-256669487/1250000000 : ℝ)*X 0 0+(2714435981/5000000000 : ℝ)*X 0 1+(5229952829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133829037/250000000 : ℝ)*X 1 0+(-431010613/2000000000 : ℝ)*X 1 1+(5229952661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353161629/10000000000 : ℝ)*X 2 0+(5229952393/10000000000 : ℝ)*X 2 1+(-2155053221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((541110359/1250000000 : ℝ)*X 0 0+(515779897/1250000000 : ℝ)*X 0 1+(908170573/2000000000 : ℝ)*X 0 2+(541110359/1250000000 : ℝ)*X 1 0+(515779897/1250000000 : ℝ)*X 1 1+(908170573/2000000000 : ℝ)*X 1 2+(541110359/1250000000 : ℝ)*X 2 0+(515779897/1250000000 : ℝ)*X 2 1+(908170573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2053376099/10000000000 : ℝ)*X 0 0+(326924263/625000000 : ℝ)*X 0 1+(1357007843/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331374983/625000000 : ℝ)*X 1 0+(-978487311/5000000000 : ℝ)*X 1 1+(339251973/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651000707/5000000000 : ℝ)*X 2 0+(1357007597/2500000000 : ℝ)*X 2 1+(-1956973943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328924929/10000000000 : ℝ)*X 0 0+(453911161/1000000000 : ℝ)*X 0 1+(2063995297/5000000000 : ℝ)*X 0 2+(4328924929/10000000000 : ℝ)*X 1 0+(453911161/1000000000 : ℝ)*X 1 1+(2063995297/5000000000 : ℝ)*X 1 2+(4328924929/10000000000 : ℝ)*X 2 0+(453911161/1000000000 : ℝ)*X 2 1+(2063995297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (833452957083572964071507367/399500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259802363/50000000000000 : ℝ)*(base19) + (324792949/50000000000000 : ℝ)*(base23) + (8218401/20000000000000 : ℝ)*(lower2) + (146248351/100000000000000 : ℝ)*(upper3) + (2235509/6250000000000 : ℝ)*(lower4) + (1859765319301369/50000000000000 : ℝ)*(major0) + (1859765319301369/50000000000000 : ℝ)*(major1) + (1859765319301369/50000000000000 : ℝ)*(major2) + (2513586528613577/50000000000000 : ℝ)*(sp0) + (201086936135687/4000000000000 : ℝ)*(sp1) + (2513586636705501/50000000000000 : ℝ)*(sp2) + (301485540775029/12500000000000 : ℝ)*(sp3) + (865769747/100000000000000 : ℝ)*(sp4) + (591693399/20000000000000 : ℝ)*(sp7) + (2411887284667227/100000000000000 : ℝ)*(f.failure) + (5027173922996901/100000000000000 : ℝ)*(f.sum) + (112010529914623/15980000000000000000000000000 : ℝ)*base65 + (10496124619258589211/1598000000000000000000000000000000 : ℝ)*base68 + (11351903083750589211/1598000000000000000000000000000000 : ℝ)*base70 + (2868332657352589211/1598000000000000000000000000000000 : ℝ)*base72 + (55248504288323/15980000000000000000000000000 : ℝ)*base73 + (13693622071500589211/1598000000000000000000000000000000 : ℝ)*base76 + (1764791023636589211/1598000000000000000000000000000000 : ℝ)*base78 + (2422062218065410789/1598000000000000000000000000000000 : ℝ)*base79 + (30550318730457/15980000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (66630119/10000000000000000000000 : ℝ)*base90 + (66630119/10000000000000000000000 : ℝ)*base92 + (66630119/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73728305133864905140023537/9987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (441120823/25000000000000 : ℝ)*(base19) + (1934527761/50000000000000 : ℝ)*(base23) + (181778563/50000000000000 : ℝ)*(upper3) + (100795547/100000000000000 : ℝ)*(lower4) + (103759901/50000000000000 : ℝ)*(upper5) + (23444595191647/625000000000 : ℝ)*(major0) + (23444595191647/625000000000 : ℝ)*(major1) + (23444595191647/625000000000 : ℝ)*(major2) + (27389533991/100000000000000 : ℝ)*(sp1) + (58716634313/100000000000000 : ℝ)*(sp2) + (5069889292781797/100000000000000 : ℝ)*(sp4) + (5069860138764513/100000000000000 : ℝ)*(sp5) + (5069826707091961/100000000000000 : ℝ)*(sp6) + (608095230619157/25000000000000 : ℝ)*(sp7) + (608095230619157/25000000000000 : ℝ)*(f.failure) + (5069889292781797/100000000000000 : ℝ)*(f.sum) + (3368176349/6392000000000000000000000 : ℝ)*base65 + (29097372376257107/19975000000000000000000000000000 : ℝ)*base67 + (198993303467757107/19975000000000000000000000000000 : ℝ)*base69 + (20546520318757107/19975000000000000000000000000000 : ℝ)*base71 + (192862005539/159800000000000000000000000 : ℝ)*base73 + (406812984721532107/19975000000000000000000000000000 : ℝ)*base75 + (150933540818432107/19975000000000000000000000000000 : ℝ)*base77 + (222173283408782107/19975000000000000000000000000000 : ℝ)*base79 + (165708432661/24968750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (20736329/2500000000000000000000 : ℝ)*base90 + (20736329/2500000000000000000000 : ℝ)*base92 + (20736329/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1329_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1953/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1329_s4_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-410984671/2000000000 : ℝ)*x 0 + (5416186653/10000000000 : ℝ)*x 1 + (2620804753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410984671/2000000000 : ℝ)^4289 ≤ (2502062345183/20000000000000 : ℝ)^3265 := by
    have hnat : (410984671 : ℕ)^4289*20000000000000^3265 ≤ 2502062345183^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410984671 2000000000 2502062345183 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416186653/10000000000 : ℝ)^4289 ≤ (44686064961791/100000000000000 : ℝ)^3265 := by
    have hnat : (5416186653 : ℕ)^4289*100000000000000^3265 ≤ 44686064961791^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416186653 10000000000 44686064961791 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620804753/5000000000 : ℝ)^4289 ≤ (4280362329603/10000000000000 : ℝ)^3265 := by
    have hnat : (2620804753 : ℕ)^4289*10000000000000^3265 ≤ 4280362329603^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620804753 5000000000 4280362329603 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410984671/2000000000 : ℝ), (5416186653/10000000000 : ℝ), (2620804753/5000000000 : ℝ)] ![(2502062345183/20000000000000 : ℝ), (44686064961791/100000000000000 : ℝ), (4280362329603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410984671/2000000000 : ℝ)|^4289 ≤ (2502062345183/20000000000000 : ℝ)^3265
        have hw : |(-410984671/2000000000 : ℝ)|=(410984671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416186653/10000000000 : ℝ)|^4289 ≤ (44686064961791/100000000000000 : ℝ)^3265
        have hw : |(5416186653/10000000000 : ℝ)|=(5416186653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620804753/5000000000 : ℝ)|^4289 ≤ (4280362329603/10000000000000 : ℝ)^3265
        have hw : |(2620804753/5000000000 : ℝ)|=(2620804753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s4_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349935813/10000000000 : ℝ)*x 0 + (-2143935813/10000000000 : ℝ)*x 1 + (524160933/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349935813/10000000000 : ℝ)^4289 ≤ (2198470794231/5000000000000 : ℝ)^3265 := by
    have hnat : (5349935813 : ℕ)^4289*5000000000000^3265 ≤ 2198470794231^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349935813 10000000000 2198470794231 5000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143935813/10000000000 : ℝ)^4289 ≤ (13226962692389/100000000000000 : ℝ)^3265 := by
    have hnat : (2143935813 : ℕ)^4289*100000000000000^3265 ≤ 13226962692389^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143935813 10000000000 13226962692389 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524160933/1000000000 : ℝ)^4289 ≤ (42803621408033/100000000000000 : ℝ)^3265 := by
    have hnat : (524160933 : ℕ)^4289*100000000000000^3265 ≤ 42803621408033^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524160933 1000000000 42803621408033 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349935813/10000000000 : ℝ), (-2143935813/10000000000 : ℝ), (524160933/1000000000 : ℝ)] ![(2198470794231/5000000000000 : ℝ), (13226962692389/100000000000000 : ℝ), (42803621408033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349935813/10000000000 : ℝ)|^4289 ≤ (2198470794231/5000000000000 : ℝ)^3265
        have hw : |(5349935813/10000000000 : ℝ)|=(5349935813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2143935813/10000000000 : ℝ)|^4289 ≤ (13226962692389/100000000000000 : ℝ)^3265
        have hw : |(-2143935813/10000000000 : ℝ)|=(2143935813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524160933/1000000000 : ℝ)|^4289 ≤ (42803621408033/100000000000000 : ℝ)^3265
        have hw : |(524160933/1000000000 : ℝ)|=(524160933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s4_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349935879/10000000000 : ℝ)*x 0 + (5241609107/10000000000 : ℝ)*x 1 + (-2143936019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349935879/10000000000 : ℝ)^4289 ≤ (1758776663887/4000000000000 : ℝ)^3265 := by
    have hnat : (5349935879 : ℕ)^4289*4000000000000^3265 ≤ 1758776663887^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349935879 10000000000 1758776663887 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241609107/10000000000 : ℝ)^4289 ≤ (8560723803171/20000000000000 : ℝ)^3265 := by
    have hnat : (5241609107 : ℕ)^4289*20000000000000^3265 ≤ 8560723803171^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241609107 10000000000 8560723803171 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2143936019/10000000000 : ℝ)^4289 ≤ (13226964361897/100000000000000 : ℝ)^3265 := by
    have hnat : (2143936019 : ℕ)^4289*100000000000000^3265 ≤ 13226964361897^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143936019 10000000000 13226964361897 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349935879/10000000000 : ℝ), (5241609107/10000000000 : ℝ), (-2143936019/10000000000 : ℝ)] ![(1758776663887/4000000000000 : ℝ), (8560723803171/20000000000000 : ℝ), (13226964361897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349935879/10000000000 : ℝ)|^4289 ≤ (1758776663887/4000000000000 : ℝ)^3265
        have hw : |(5349935879/10000000000 : ℝ)|=(5349935879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241609107/10000000000 : ℝ)|^4289 ≤ (8560723803171/20000000000000 : ℝ)^3265
        have hw : |(5241609107/10000000000 : ℝ)|=(5241609107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2143936019/10000000000 : ℝ)|^4289 ≤ (13226964361897/100000000000000 : ℝ)^3265
        have hw : |(-2143936019/10000000000 : ℝ)|=(2143936019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s4_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216491741/500000000 : ℝ)*x 0 + (4151488891/10000000000 : ℝ)*x 1 + (112884159/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216491741/500000000 : ℝ)^4289 ≤ (33301059302373/100000000000000 : ℝ)^3265 := by
    have hnat : (216491741 : ℕ)^4289*100000000000000^3265 ≤ 33301059302373^3265*500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216491741 500000000 33301059302373 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4151488891/10000000000 : ℝ)^4289 ≤ (31510942344483/100000000000000 : ℝ)^3265 := by
    have hnat : (4151488891 : ℕ)^4289*100000000000000^3265 ≤ 31510942344483^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151488891 10000000000 31510942344483 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112884159/250000000 : ℝ)^4289 ≤ (35187998337339/100000000000000 : ℝ)^3265 := by
    have hnat : (112884159 : ℕ)^4289*100000000000000^3265 ≤ 35187998337339^3265*250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112884159 250000000 35187998337339 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216491741/500000000 : ℝ), (4151488891/10000000000 : ℝ), (112884159/250000000 : ℝ)] ![(33301059302373/100000000000000 : ℝ), (31510942344483/100000000000000 : ℝ), (35187998337339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216491741/500000000 : ℝ)|^4289 ≤ (33301059302373/100000000000000 : ℝ)^3265
        have hw : |(216491741/500000000 : ℝ)|=(216491741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4151488891/10000000000 : ℝ)|^4289 ≤ (31510942344483/100000000000000 : ℝ)^3265
        have hw : |(4151488891/10000000000 : ℝ)|=(4151488891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112884159/250000000 : ℝ)|^4289 ≤ (35187998337339/100000000000000 : ℝ)^3265
        have hw : |(112884159/250000000 : ℝ)|=(112884159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s4_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2054937/10000000 : ℝ)*x 0 + (131056337/250000000 : ℝ)*x 1 + (5415539169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054937/10000000 : ℝ)^4289 ≤ (3127605212421/25000000000000 : ℝ)^3265 := by
    have hnat : (2054937 : ℕ)^4289*25000000000000^3265 ≤ 3127605212421^3265*10000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054937 10000000 3127605212421 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131056337/250000000 : ℝ)^4289 ≤ (21405265752217/50000000000000 : ℝ)^3265 := by
    have hnat : (131056337 : ℕ)^4289*50000000000000^3265 ≤ 21405265752217^3265*250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131056337 250000000 21405265752217 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415539169/10000000000 : ℝ)^4289 ≤ (22339523813073/50000000000000 : ℝ)^3265 := by
    have hnat : (5415539169 : ℕ)^4289*50000000000000^3265 ≤ 22339523813073^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415539169 10000000000 22339523813073 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2054937/10000000 : ℝ), (131056337/250000000 : ℝ), (5415539169/10000000000 : ℝ)] ![(3127605212421/25000000000000 : ℝ), (21405265752217/50000000000000 : ℝ), (22339523813073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2054937/10000000 : ℝ)|^4289 ≤ (3127605212421/25000000000000 : ℝ)^3265
        have hw : |(-2054937/10000000 : ℝ)|=(2054937/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131056337/250000000 : ℝ)|^4289 ≤ (21405265752217/50000000000000 : ℝ)^3265
        have hw : |(131056337/250000000 : ℝ)|=(131056337/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415539169/10000000000 : ℝ)|^4289 ≤ (22339523813073/50000000000000 : ℝ)^3265
        have hw : |(5415539169/10000000000 : ℝ)|=(5415539169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s4_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305036551/10000000000 : ℝ)*x 0 + (-1970006133/10000000000 : ℝ)*x 1 + (169235599/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305036551/10000000000 : ℝ)^4289 ≤ (10871327280657/25000000000000 : ℝ)^3265 := by
    have hnat : (5305036551 : ℕ)^4289*25000000000000^3265 ≤ 10871327280657^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305036551 10000000000 10871327280657 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1970006133/10000000000 : ℝ)^4289 ≤ (11835643248663/100000000000000 : ℝ)^3265 := by
    have hnat : (1970006133 : ℕ)^4289*100000000000000^3265 ≤ 11835643248663^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970006133 10000000000 11835643248663 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169235599/312500000 : ℝ)^4289 ≤ (11169761903827/25000000000000 : ℝ)^3265 := by
    have hnat : (169235599 : ℕ)^4289*25000000000000^3265 ≤ 11169761903827^3265*312500000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169235599 312500000 11169761903827 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305036551/10000000000 : ℝ), (-1970006133/10000000000 : ℝ), (169235599/312500000 : ℝ)] ![(10871327280657/25000000000000 : ℝ), (11835643248663/100000000000000 : ℝ), (11169761903827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305036551/10000000000 : ℝ)|^4289 ≤ (10871327280657/25000000000000 : ℝ)^3265
        have hw : |(5305036551/10000000000 : ℝ)|=(5305036551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1970006133/10000000000 : ℝ)|^4289 ≤ (11835643248663/100000000000000 : ℝ)^3265
        have hw : |(-1970006133/10000000000 : ℝ)|=(1970006133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169235599/312500000 : ℝ)|^4289 ≤ (11169761903827/25000000000000 : ℝ)^3265
        have hw : |(169235599/312500000 : ℝ)|=(169235599/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s4_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061007313/2000000000 : ℝ)*x 0 + (5415539149/10000000000 : ℝ)*x 1 + (-1970006139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061007313/2000000000 : ℝ)^4289 ≤ (43485309273377/100000000000000 : ℝ)^3265 := by
    have hnat : (1061007313 : ℕ)^4289*100000000000000^3265 ≤ 43485309273377^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061007313 2000000000 43485309273377 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415539149/10000000000 : ℝ)^4289 ≤ (44679047409393/100000000000000 : ℝ)^3265 := by
    have hnat : (5415539149 : ℕ)^4289*100000000000000^3265 ≤ 44679047409393^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415539149 10000000000 44679047409393 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970006139/10000000000 : ℝ)^4289 ≤ (739727706001/6250000000000 : ℝ)^3265 := by
    have hnat : (1970006139 : ℕ)^4289*6250000000000^3265 ≤ 739727706001^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970006139 10000000000 739727706001 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061007313/2000000000 : ℝ), (5415539149/10000000000 : ℝ), (-1970006139/10000000000 : ℝ)] ![(43485309273377/100000000000000 : ℝ), (44679047409393/100000000000000 : ℝ), (739727706001/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061007313/2000000000 : ℝ)|^4289 ≤ (43485309273377/100000000000000 : ℝ)^3265
        have hw : |(1061007313/2000000000 : ℝ)|=(1061007313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415539149/10000000000 : ℝ)|^4289 ≤ (44679047409393/100000000000000 : ℝ)^3265
        have hw : |(5415539149/10000000000 : ℝ)|=(5415539149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970006139/10000000000 : ℝ)|^4289 ≤ (739727706001/6250000000000 : ℝ)^3265
        have hw : |(-1970006139/10000000000 : ℝ)|=(1970006139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s4_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082465731/2500000000 : ℝ)*x 0 + (2257011843/5000000000 : ℝ)*x 1 + (830567761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082465731/2500000000 : ℝ)^4289 ≤ (33301343243407/100000000000000 : ℝ)^3265 := by
    have hnat : (1082465731 : ℕ)^4289*100000000000000^3265 ≤ 33301343243407^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082465731 2500000000 33301343243407 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257011843/5000000000 : ℝ)^4289 ≤ (7034850793983/20000000000000 : ℝ)^3265 := by
    have hnat : (2257011843 : ℕ)^4289*20000000000000^3265 ≤ 7034850793983^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257011843 5000000000 7034850793983 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830567761/2000000000 : ℝ)^4289 ≤ (15762201382311/50000000000000 : ℝ)^3265 := by
    have hnat : (830567761 : ℕ)^4289*50000000000000^3265 ≤ 15762201382311^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830567761 2000000000 15762201382311 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082465731/2500000000 : ℝ), (2257011843/5000000000 : ℝ), (830567761/2000000000 : ℝ)] ![(33301343243407/100000000000000 : ℝ), (7034850793983/20000000000000 : ℝ), (15762201382311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082465731/2500000000 : ℝ)|^4289 ≤ (33301343243407/100000000000000 : ℝ)^3265
        have hw : |(1082465731/2500000000 : ℝ)|=(1082465731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257011843/5000000000 : ℝ)|^4289 ≤ (7034850793983/20000000000000 : ℝ)^3265
        have hw : |(2257011843/5000000000 : ℝ)|=(2257011843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830567761/2000000000 : ℝ)|^4289 ≤ (15762201382311/50000000000000 : ℝ)^3265
        have hw : |(830567761/2000000000 : ℝ)|=(830567761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11063/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5407/50000 : ℝ) ^ (67/16 : ℝ) ≤ (9011931966139273/100000000000000000000 : ℝ) := by
    have hpowers : (5407/50000 : ℝ)^67 ≤ (9011931966139273/100000000000000000000 : ℝ)^16 := by
      have hnat : (5407 : ℕ)^67*100000000000000000000^16 ≤ 9011931966139273^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5407 50000 9011931966139273 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5407/50000 : ℝ)) (X := (9011931966139273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (15023/100000 : ℝ) ^ (67/16 : ℝ) ≤ (7140005392099353/20000000000000000000 : ℝ) := by
    have hpowers : (15023/100000 : ℝ)^67 ≤ (7140005392099353/20000000000000000000 : ℝ)^16 := by
      have hnat : (15023 : ℕ)^67*20000000000000000000^16 ≤ 7140005392099353^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15023 100000 7140005392099353 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15023/100000 : ℝ)) (X := (7140005392099353/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009011931966139273/50000000000000000000 : ℝ) ≤ (78128362430533/78125000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50009011931966139273/50000000000000000000 : ℝ)^16 ≤ (78128362430533/78125000000000 : ℝ)^67 := by
      have hnat : (50009011931966139273 : ℕ)^16*78125000000000^67 ≤ 78128362430533^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009011931966139273 50000000000000000000 78128362430533 78125000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78128362430533/78125000000000 : ℝ)) (X := (50009011931966139273/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022355979463318019/50000000000000000000 : ℝ) ≤ (10001067566619289/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50022355979463318019/50000000000000000000 : ℝ)^16 ≤ (10001067566619289/10000000000000000 : ℝ)^67 := by
      have hnat : (50022355979463318019 : ℕ)^16*10000000000000000^67 ≤ 10001067566619289^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022355979463318019 50000000000000000000 10001067566619289 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001067566619289/10000000000000000 : ℝ)) (X := (50022355979463318019/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007140005392099353/10000000000000000000 : ℝ) ≤ (5000852371065177/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (10007140005392099353/10000000000000000000 : ℝ)^16 ≤ (5000852371065177/5000000000000000 : ℝ)^67 := by
      have hnat : (10007140005392099353 : ℕ)^16*5000000000000000^67 ≤ 5000852371065177^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007140005392099353 10000000000000000000 5000852371065177 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000852371065177/5000000000000000 : ℝ)) (X := (10007140005392099353/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9011931966139273/100000000000000000000 : ℝ) ≤ ((10519507671055300249/10522500000000000000 : ℝ)+2*(127435102213/84180000000000 : ℝ)*(5407/50000 : ℝ))^(67/16 : ℝ) := by
    rw [show (10519507671055300249/10522500000000000000 : ℝ)+2*(127435102213/84180000000000 : ℝ)*(5407/50000 : ℝ)=(78128362430533/78125000000000 : ℝ) by norm_num, show 1+2*(9011931966139273/100000000000000000000 : ℝ)=(50009011931966139273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7140005392099353/20000000000000000000 : ℝ)+(9011931966139273/100000000000000000000 : ℝ) ≤ ((10519507671055300249/10522500000000000000 : ℝ)+(127435102213/84180000000000 : ℝ)*((15023/100000 : ℝ)+(5407/50000 : ℝ)))^(67/16 : ℝ) := by
    rw [show (10519507671055300249/10522500000000000000 : ℝ)+(127435102213/84180000000000 : ℝ)*((15023/100000 : ℝ)+(5407/50000 : ℝ))=(10001067566619289/10000000000000000 : ℝ) by norm_num, show 1+(7140005392099353/20000000000000000000 : ℝ)+(9011931966139273/100000000000000000000 : ℝ)=(50022355979463318019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7140005392099353/20000000000000000000 : ℝ) ≤ ((10519507671055300249/10522500000000000000 : ℝ)+2*(127435102213/84180000000000 : ℝ)*(15023/100000 : ℝ))^(67/16 : ℝ) := by
    rw [show (10519507671055300249/10522500000000000000 : ℝ)+2*(127435102213/84180000000000 : ℝ)*(15023/100000 : ℝ)=(5000852371065177/5000000000000000 : ℝ) by norm_num, show 1+2*(7140005392099353/20000000000000000000 : ℝ)=(10007140005392099353/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10519507671055300249/10522500000000000000 : ℝ)*(X 1 0+X 2 0)+(127435102213/84180000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (15023/100000 : ℝ)) (c := (10519507671055300249/10522500000000000000 : ℝ)) (alpha := (127435102213/84180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10519507671055300249/10522500000000000000 : ℝ)*(X 0 1+X 2 1)+(127435102213/84180000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (15023/100000 : ℝ)) (c := (10519507671055300249/10522500000000000000 : ℝ)) (alpha := (127435102213/84180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10519507671055300249/10522500000000000000 : ℝ)*(X 0 2+X 1 2)+(127435102213/84180000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (15023/100000 : ℝ)) (c := (10519507671055300249/10522500000000000000 : ℝ)) (alpha := (127435102213/84180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-410984671/2000000000 : ℝ)*X 0 0+(5416186653/10000000000 : ℝ)*X 0 1+(2620804753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349935813/10000000000 : ℝ)*X 1 0+(-2143935813/10000000000 : ℝ)*X 1 1+(524160933/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349935879/10000000000 : ℝ)*X 2 0+(5241609107/10000000000 : ℝ)*X 2 1+(-2143936019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((216491741/500000000 : ℝ)*X 0 0+(4151488891/10000000000 : ℝ)*X 0 1+(112884159/250000000 : ℝ)*X 0 2+(216491741/500000000 : ℝ)*X 1 0+(4151488891/10000000000 : ℝ)*X 1 1+(112884159/250000000 : ℝ)*X 1 2+(216491741/500000000 : ℝ)*X 2 0+(4151488891/10000000000 : ℝ)*X 2 1+(112884159/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2054937/10000000 : ℝ)*X 0 0+(131056337/250000000 : ℝ)*X 0 1+(5415539169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305036551/10000000000 : ℝ)*X 1 0+(-1970006133/10000000000 : ℝ)*X 1 1+(169235599/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061007313/2000000000 : ℝ)*X 2 0+(5415539149/10000000000 : ℝ)*X 2 1+(-1970006139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1082465731/2500000000 : ℝ)*X 0 0+(2257011843/5000000000 : ℝ)*X 0 1+(830567761/2000000000 : ℝ)*X 0 2+(1082465731/2500000000 : ℝ)*X 1 0+(2257011843/5000000000 : ℝ)*X 1 1+(830567761/2000000000 : ℝ)*X 1 2+(1082465731/2500000000 : ℝ)*X 2 0+(2257011843/5000000000 : ℝ)*X 2 1+(830567761/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59728154706746646841767717/43843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80934827/20000000000000 : ℝ)*(base19) + (639804443/100000000000000 : ℝ)*(base23) + (3480843/12500000000000 : ℝ)*(upper3) + (19411621/20000000000000 : ℝ)*(lower4) + (1059540602338511/25000000000000 : ℝ)*(major0) + (1059540602338511/25000000000000 : ℝ)*(major1) + (1059540602338511/25000000000000 : ℝ)*(major2) + (1145626589856291/20000000000000 : ℝ)*(sp0) + (1145627243676119/20000000000000 : ℝ)*(sp1) + (1145626792608369/20000000000000 : ℝ)*(sp2) + (2748183043928543/100000000000000 : ℝ)*(sp3) + (918443319/25000000000000 : ℝ)*(sp4) + (1010104221/50000000000000 : ℝ)*(sp6) + (2553157473/50000000000000 : ℝ)*(sp7) + (2748188150243489/100000000000000 : ℝ)*(f.failure) + (5728136623054731/100000000000000 : ℝ)*(f.sum) + (11986273746979/4209000000000000000000000000 : ℝ)*base66 + (1323793971565428587/87687500000000000000000000000000 : ℝ)*base68 + (1098428724162928587/87687500000000000000000000000000 : ℝ)*base70 + (1021809685390741087/87687500000000000000000000000000 : ℝ)*base72 + (1748659622867/2104500000000000000000000000 : ℝ)*base74 + (190160939402178587/87687500000000000000000000000000 : ℝ)*base76 + (690420186593866087/87687500000000000000000000000000 : ℝ)*base78 + (412892510455053587/87687500000000000000000000000000 : ℝ)*base80 + (25845318244681/4209000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (96447867/10000000000000000000000 : ℝ)*base89 + (96447867/10000000000000000000000 : ℝ)*base91 + (96447867/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (432490926342775323694575561/43843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1749964657/100000000000000 : ℝ)*(base19) + (950111203/50000000000000 : ℝ)*(base23) + (201331949/100000000000000 : ℝ)*(upper3) + (12543169/20000000000000 : ℝ)*(lower4) + (210969313/100000000000000 : ℝ)*(upper5) + (1067435150859189/25000000000000 : ℝ)*(major0) + (1067435150859189/25000000000000 : ℝ)*(major1) + (1067435150859189/25000000000000 : ℝ)*(major2) + (34517102927/100000000000000 : ℝ)*(sp1) + (2281445553/6250000000000 : ℝ)*(sp2) + (288540810373829/5000000000000 : ℝ)*(sp4) + (1442694985102249/25000000000000 : ℝ)*(sp5) + (2885388902062663/50000000000000 : ℝ)*(sp6) + (276866467058463/10000000000000 : ℝ)*(sp7) + (276866467058463/10000000000000 : ℝ)*(f.failure) + (288540810373829/5000000000000 : ℝ)*(f.sum) + (1063675262171/350750000000000000000000000 : ℝ)*base66 + (504541016901162313/87687500000000000000000000000000 : ℝ)*base68 + (81491321886787313/87687500000000000000000000000000 : ℝ)*base70 + (52647956573724813/87687500000000000000000000000000 : ℝ)*base72 + (7721445218907/1403000000000000000000000000 : ℝ)*base74 + (157858560127662313/87687500000000000000000000000000 : ℝ)*base76 + (288101710650962687/87687500000000000000000000000000 : ℝ)*base77 + (652661458240712687/87687500000000000000000000000000 : ℝ)*base79 + (26446970497/43843750000000000000000000 : ℝ)*base81 + (6261189/1000000000000000000000 : ℝ)*base89 + (6261189/1000000000000000000000 : ℝ)*base91 + (6261189/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1329_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11063/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1329_s5_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027599773/5000000000 : ℝ)*x 0 + (2706906699/5000000000 : ℝ)*x 1 + (163868783/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027599773/5000000000 : ℝ)^4289 ≤ (6256260282401/50000000000000 : ℝ)^3265 := by
    have hnat : (1027599773 : ℕ)^4289*50000000000000^3265 ≤ 6256260282401^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027599773 5000000000 6256260282401 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706906699/5000000000 : ℝ)^4289 ≤ (44660345261147/100000000000000 : ℝ)^3265 := by
    have hnat : (2706906699 : ℕ)^4289*100000000000000^3265 ≤ 44660345261147^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706906699 5000000000 44660345261147 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163868783/312500000 : ℝ)^4289 ≤ (21413567079899/50000000000000 : ℝ)^3265 := by
    have hnat : (163868783 : ℕ)^4289*50000000000000^3265 ≤ 21413567079899^3265*312500000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163868783 312500000 21413567079899 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027599773/5000000000 : ℝ), (2706906699/5000000000 : ℝ), (163868783/312500000 : ℝ)] ![(6256260282401/50000000000000 : ℝ), (44660345261147/100000000000000 : ℝ), (21413567079899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027599773/5000000000 : ℝ)|^4289 ≤ (6256260282401/50000000000000 : ℝ)^3265
        have hw : |(-1027599773/5000000000 : ℝ)|=(1027599773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706906699/5000000000 : ℝ)|^4289 ≤ (44660345261147/100000000000000 : ℝ)^3265
        have hw : |(2706906699/5000000000 : ℝ)|=(2706906699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163868783/312500000 : ℝ)|^4289 ≤ (21413567079899/50000000000000 : ℝ)^3265
        have hw : |(163868783/312500000 : ℝ)|=(163868783/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s5_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337332621/2500000000 : ℝ)*x 0 + (-2141840633/10000000000 : ℝ)*x 1 + (5243801059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337332621/2500000000 : ℝ)^4289 ≤ (43962880686473/100000000000000 : ℝ)^3265 := by
    have hnat : (1337332621 : ℕ)^4289*100000000000000^3265 ≤ 43962880686473^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337332621 2500000000 43962880686473 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141840633/10000000000 : ℝ)^4289 ≤ (13209985104981/100000000000000 : ℝ)^3265 := by
    have hnat : (2141840633 : ℕ)^4289*100000000000000^3265 ≤ 13209985104981^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141840633 10000000000 13209985104981 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243801059/10000000000 : ℝ)^4289 ≤ (2676695886999/6250000000000 : ℝ)^3265 := by
    have hnat : (5243801059 : ℕ)^4289*6250000000000^3265 ≤ 2676695886999^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243801059 10000000000 2676695886999 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337332621/2500000000 : ℝ), (-2141840633/10000000000 : ℝ), (5243801059/10000000000 : ℝ)] ![(43962880686473/100000000000000 : ℝ), (13209985104981/100000000000000 : ℝ), (2676695886999/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337332621/2500000000 : ℝ)|^4289 ≤ (43962880686473/100000000000000 : ℝ)^3265
        have hw : |(1337332621/2500000000 : ℝ)|=(1337332621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141840633/10000000000 : ℝ)|^4289 ≤ (13209985104981/100000000000000 : ℝ)^3265
        have hw : |(-2141840633/10000000000 : ℝ)|=(2141840633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243801059/10000000000 : ℝ)|^4289 ≤ (2676695886999/6250000000000 : ℝ)^3265
        have hw : |(5243801059/10000000000 : ℝ)|=(5243801059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s5_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668666313/1250000000 : ℝ)*x 0 + (163868783/312500000 : ℝ)*x 1 + (-214184061/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668666313/1250000000 : ℝ)^4289 ≤ (5495360112799/12500000000000 : ℝ)^3265 := by
    have hnat : (668666313 : ℕ)^4289*12500000000000^3265 ≤ 5495360112799^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668666313 1250000000 5495360112799 12500000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163868783/312500000 : ℝ)^4289 ≤ (21413567079899/50000000000000 : ℝ)^3265 := by
    have hnat : (163868783 : ℕ)^4289*50000000000000^3265 ≤ 21413567079899^3265*312500000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163868783 312500000 21413567079899 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214184061/1000000000 : ℝ)^4289 ≤ (13209984918637/100000000000000 : ℝ)^3265 := by
    have hnat : (214184061 : ℕ)^4289*100000000000000^3265 ≤ 13209984918637^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214184061 1000000000 13209984918637 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668666313/1250000000 : ℝ), (163868783/312500000 : ℝ), (-214184061/1000000000 : ℝ)] ![(5495360112799/12500000000000 : ℝ), (21413567079899/50000000000000 : ℝ), (13209984918637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668666313/1250000000 : ℝ)|^4289 ≤ (5495360112799/12500000000000 : ℝ)^3265
        have hw : |(668666313/1250000000 : ℝ)|=(668666313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163868783/312500000 : ℝ)|^4289 ≤ (21413567079899/50000000000000 : ℝ)^3265
        have hw : |(163868783/312500000 : ℝ)|=(163868783/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214184061/1000000000 : ℝ)|^4289 ≤ (13209984918637/100000000000000 : ℝ)^3265
        have hw : |(-214184061/1000000000 : ℝ)|=(214184061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s5_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329999501/10000000000 : ℝ)*x 0 + (2078113037/5000000000 : ℝ)*x 1 + (1127647057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329999501/10000000000 : ℝ)^4289 ≤ (33302723119791/100000000000000 : ℝ)^3265 := by
    have hnat : (4329999501 : ℕ)^4289*100000000000000^3265 ≤ 33302723119791^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329999501 10000000000 33302723119791 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078113037/5000000000 : ℝ)^4289 ≤ (31558184338287/100000000000000 : ℝ)^3265 := by
    have hnat : (2078113037 : ℕ)^4289*100000000000000^3265 ≤ 31558184338287^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078113037 5000000000 31558184338287 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127647057/2500000000 : ℝ)^4289 ≤ (7027818504861/20000000000000 : ℝ)^3265 := by
    have hnat : (1127647057 : ℕ)^4289*20000000000000^3265 ≤ 7027818504861^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127647057 2500000000 7027818504861 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329999501/10000000000 : ℝ), (2078113037/5000000000 : ℝ), (1127647057/2500000000 : ℝ)] ![(33302723119791/100000000000000 : ℝ), (31558184338287/100000000000000 : ℝ), (7027818504861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329999501/10000000000 : ℝ)|^4289 ≤ (33302723119791/100000000000000 : ℝ)^3265
        have hw : |(4329999501/10000000000 : ℝ)|=(4329999501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078113037/5000000000 : ℝ)|^4289 ≤ (31558184338287/100000000000000 : ℝ)^3265
        have hw : |(2078113037/5000000000 : ℝ)|=(2078113037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127647057/2500000000 : ℝ)|^4289 ≤ (7027818504861/20000000000000 : ℝ)^3265
        have hw : |(1127647057/2500000000 : ℝ)|=(1127647057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s5_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-102760631/500000000 : ℝ)*x 0 + (5244411959/10000000000 : ℝ)*x 1 + (2706599453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102760631/500000000 : ℝ)^4289 ≤ (12512625126489/100000000000000 : ℝ)^3265 := by
    have hnat : (102760631 : ℕ)^4289*100000000000000^3265 ≤ 12512625126489^3265*500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102760631 500000000 12512625126489 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244411959/10000000000 : ℝ)^4289 ≤ (2677105528307/6250000000000 : ℝ)^3265 := by
    have hnat : (5244411959 : ℕ)^4289*6250000000000^3265 ≤ 2677105528307^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244411959 10000000000 2677105528307 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706599453/5000000000 : ℝ)^4289 ≤ (279085539981/625000000000 : ℝ)^3265 := by
    have hnat : (2706599453 : ℕ)^4289*625000000000^3265 ≤ 279085539981^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706599453 5000000000 279085539981 625000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102760631/500000000 : ℝ), (5244411959/10000000000 : ℝ), (2706599453/5000000000 : ℝ)] ![(12512625126489/100000000000000 : ℝ), (2677105528307/6250000000000 : ℝ), (279085539981/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102760631/500000000 : ℝ)|^4289 ≤ (12512625126489/100000000000000 : ℝ)^3265
        have hw : |(-102760631/500000000 : ℝ)|=(102760631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244411959/10000000000 : ℝ)|^4289 ≤ (2677105528307/6250000000000 : ℝ)^3265
        have hw : |(5244411959/10000000000 : ℝ)|=(5244411959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706599453/5000000000 : ℝ)|^4289 ≤ (279085539981/625000000000 : ℝ)^3265
        have hw : |(2706599453/5000000000 : ℝ)|=(2706599453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s5_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605877/10000000000 : ℝ)*x 0 + (-1972442411/10000000000 : ℝ)*x 1 + (2706599427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605877/10000000000 : ℝ)^4289 ≤ (43491439615163/100000000000000 : ℝ)^3265 := by
    have hnat : (5305605877 : ℕ)^4289*100000000000000^3265 ≤ 43491439615163^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605877 10000000000 43491439615163 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972442411/10000000000 : ℝ)^4289 ≤ (2370974905661/20000000000000 : ℝ)^3265 := by
    have hnat : (1972442411 : ℕ)^4289*20000000000000^3265 ≤ 2370974905661^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972442411 10000000000 2370974905661 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706599427/5000000000 : ℝ)^4289 ≤ (44653685833479/100000000000000 : ℝ)^3265 := by
    have hnat : (2706599427 : ℕ)^4289*100000000000000^3265 ≤ 44653685833479^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706599427 5000000000 44653685833479 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605877/10000000000 : ℝ), (-1972442411/10000000000 : ℝ), (2706599427/5000000000 : ℝ)] ![(43491439615163/100000000000000 : ℝ), (2370974905661/20000000000000 : ℝ), (44653685833479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605877/10000000000 : ℝ)|^4289 ≤ (43491439615163/100000000000000 : ℝ)^3265
        have hw : |(5305605877/10000000000 : ℝ)|=(5305605877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972442411/10000000000 : ℝ)|^4289 ≤ (2370974905661/20000000000000 : ℝ)^3265
        have hw : |(-1972442411/10000000000 : ℝ)|=(1972442411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706599427/5000000000 : ℝ)|^4289 ≤ (44653685833479/100000000000000 : ℝ)^3265
        have hw : |(2706599427/5000000000 : ℝ)|=(2706599427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s5_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605397/10000000000 : ℝ)*x 0 + (135329981/250000000 : ℝ)*x 1 + (-1972442537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605397/10000000000 : ℝ)^4289 ≤ (8698286889289/20000000000000 : ℝ)^3265 := by
    have hnat : (5305605397 : ℕ)^4289*20000000000000^3265 ≤ 8698286889289^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605397 10000000000 8698286889289 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135329981/250000000 : ℝ)^4289 ≤ (11163422504061/25000000000000 : ℝ)^3265 := by
    have hnat : (135329981 : ℕ)^4289*25000000000000^3265 ≤ 11163422504061^3265*250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135329981 250000000 11163422504061 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972442537/10000000000 : ℝ)^4289 ≤ (2370975104621/20000000000000 : ℝ)^3265 := by
    have hnat : (1972442537 : ℕ)^4289*20000000000000^3265 ≤ 2370975104621^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972442537 10000000000 2370975104621 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605397/10000000000 : ℝ), (135329981/250000000 : ℝ), (-1972442537/10000000000 : ℝ)] ![(8698286889289/20000000000000 : ℝ), (11163422504061/25000000000000 : ℝ), (2370975104621/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605397/10000000000 : ℝ)|^4289 ≤ (8698286889289/20000000000000 : ℝ)^3265
        have hw : |(5305605397/10000000000 : ℝ)|=(5305605397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135329981/250000000 : ℝ)|^4289 ≤ (11163422504061/25000000000000 : ℝ)^3265
        have hw : |(135329981/250000000 : ℝ)|=(135329981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972442537/10000000000 : ℝ)|^4289 ≤ (2370975104621/20000000000000 : ℝ)^3265
        have hw : |(-1972442537/10000000000 : ℝ)|=(1972442537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s5_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4330025313/10000000000 : ℝ)*x 0 + (901862999/2000000000 : ℝ)*x 1 + (4157506137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330025313/10000000000 : ℝ)^4289 ≤ (16651491953661/50000000000000 : ℝ)^3265 := by
    have hnat : (4330025313 : ℕ)^4289*50000000000000^3265 ≤ 16651491953661^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330025313 10000000000 16651491953661 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901862999/2000000000 : ℝ)^4289 ≤ (17563031645203/50000000000000 : ℝ)^3265 := by
    have hnat : (901862999 : ℕ)^4289*50000000000000^3265 ≤ 17563031645203^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901862999 2000000000 17563031645203 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4157506137/10000000000 : ℝ)^4289 ≤ (6314190556741/20000000000000 : ℝ)^3265 := by
    have hnat : (4157506137 : ℕ)^4289*20000000000000^3265 ≤ 6314190556741^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157506137 10000000000 6314190556741 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330025313/10000000000 : ℝ), (901862999/2000000000 : ℝ), (4157506137/10000000000 : ℝ)] ![(16651491953661/50000000000000 : ℝ), (17563031645203/50000000000000 : ℝ), (6314190556741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330025313/10000000000 : ℝ)|^4289 ≤ (16651491953661/50000000000000 : ℝ)^3265
        have hw : |(4330025313/10000000000 : ℝ)|=(4330025313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901862999/2000000000 : ℝ)|^4289 ≤ (17563031645203/50000000000000 : ℝ)^3265
        have hw : |(901862999/2000000000 : ℝ)|=(901862999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4157506137/10000000000 : ℝ)|^4289 ≤ (6314190556741/20000000000000 : ℝ)^3265
        have hw : |(4157506137/10000000000 : ℝ)|=(4157506137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11063/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3677/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11063/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11063/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11063/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11063/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11063/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11063/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11063/100000 : ℝ) ^ (67/16 : ℝ) ≤ (4956645109251677/50000000000000000000 : ℝ) := by
    have hpowers : (11063/100000 : ℝ)^67 ≤ (4956645109251677/50000000000000000000 : ℝ)^16 := by
      have hnat : (11063 : ℕ)^67*50000000000000000000^16 ≤ 4956645109251677^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11063 100000 4956645109251677 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11063/100000 : ℝ)) (X := (4956645109251677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (67/16 : ℝ) ≤ (33136198366137991/100000000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^67 ≤ (33136198366137991/100000000000000000000 : ℝ)^16 := by
      have hnat : (7379 : ℕ)^67*100000000000000000000^16 ≤ 33136198366137991^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 33136198366137991 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (33136198366137991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004956645109251677/25000000000000000000 : ℝ) ≤ (5000236717426983/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25004956645109251677/25000000000000000000 : ℝ)^16 ≤ (5000236717426983/5000000000000000 : ℝ)^67 := by
      have hnat : (25004956645109251677 : ℕ)^16*5000000000000000^67 ≤ 5000236717426983^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004956645109251677 25000000000000000000 5000236717426983 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000236717426983/5000000000000000 : ℝ)) (X := (25004956645109251677/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008609897716928269/20000000000000000000 : ℝ) ≤ (2000205575818127/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (20008609897716928269/20000000000000000000 : ℝ)^16 ≤ (2000205575818127/2000000000000000 : ℝ)^67 := by
      have hnat : (20008609897716928269 : ℕ)^16*2000000000000000^67 ≤ 2000205575818127^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008609897716928269 20000000000000000000 2000205575818127 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000205575818127/2000000000000000 : ℝ)) (X := (20008609897716928269/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033136198366137991/50000000000000000000 : ℝ) ≤ (1250197790415913/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50033136198366137991/50000000000000000000 : ℝ)^16 ≤ (1250197790415913/1250000000000000 : ℝ)^67 := by
      have hnat : (50033136198366137991 : ℕ)^16*1250000000000000^67 ≤ 1250197790415913^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033136198366137991 50000000000000000000 1250197790415913 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250197790415913/1250000000000000 : ℝ)) (X := (50033136198366137991/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4956645109251677/50000000000000000000 : ℝ) ≤ ((9234870427151216519/9237500000000000000 : ℝ)+2*(554444236669/369500000000000 : ℝ)*(11063/100000 : ℝ))^(67/16 : ℝ) := by
    rw [show (9234870427151216519/9237500000000000000 : ℝ)+2*(554444236669/369500000000000 : ℝ)*(11063/100000 : ℝ)=(5000236717426983/5000000000000000 : ℝ) by norm_num, show 1+2*(4956645109251677/50000000000000000000 : ℝ)=(25004956645109251677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33136198366137991/100000000000000000000 : ℝ)+(4956645109251677/50000000000000000000 : ℝ) ≤ ((9234870427151216519/9237500000000000000 : ℝ)+(554444236669/369500000000000 : ℝ)*((7379/50000 : ℝ)+(11063/100000 : ℝ)))^(67/16 : ℝ) := by
    rw [show (9234870427151216519/9237500000000000000 : ℝ)+(554444236669/369500000000000 : ℝ)*((7379/50000 : ℝ)+(11063/100000 : ℝ))=(2000205575818127/2000000000000000 : ℝ) by norm_num, show 1+(33136198366137991/100000000000000000000 : ℝ)+(4956645109251677/50000000000000000000 : ℝ)=(20008609897716928269/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33136198366137991/100000000000000000000 : ℝ) ≤ ((9234870427151216519/9237500000000000000 : ℝ)+2*(554444236669/369500000000000 : ℝ)*(7379/50000 : ℝ))^(67/16 : ℝ) := by
    rw [show (9234870427151216519/9237500000000000000 : ℝ)+2*(554444236669/369500000000000 : ℝ)*(7379/50000 : ℝ)=(1250197790415913/1250000000000000 : ℝ) by norm_num, show 1+2*(33136198366137991/100000000000000000000 : ℝ)=(50033136198366137991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9234870427151216519/9237500000000000000 : ℝ)*(X 1 0+X 2 0)+(554444236669/369500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11063/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (9234870427151216519/9237500000000000000 : ℝ)) (alpha := (554444236669/369500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9234870427151216519/9237500000000000000 : ℝ)*(X 0 1+X 2 1)+(554444236669/369500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11063/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (9234870427151216519/9237500000000000000 : ℝ)) (alpha := (554444236669/369500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9234870427151216519/9237500000000000000 : ℝ)*(X 0 2+X 1 2)+(554444236669/369500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11063/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (9234870427151216519/9237500000000000000 : ℝ)) (alpha := (554444236669/369500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1027599773/5000000000 : ℝ)*X 0 0+(2706906699/5000000000 : ℝ)*X 0 1+(163868783/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337332621/2500000000 : ℝ)*X 1 0+(-2141840633/10000000000 : ℝ)*X 1 1+(5243801059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668666313/1250000000 : ℝ)*X 2 0+(163868783/312500000 : ℝ)*X 2 1+(-214184061/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329999501/10000000000 : ℝ)*X 0 0+(2078113037/5000000000 : ℝ)*X 0 1+(1127647057/2500000000 : ℝ)*X 0 2+(4329999501/10000000000 : ℝ)*X 1 0+(2078113037/5000000000 : ℝ)*X 1 1+(1127647057/2500000000 : ℝ)*X 1 2+(4329999501/10000000000 : ℝ)*X 2 0+(2078113037/5000000000 : ℝ)*X 2 1+(1127647057/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-102760631/500000000 : ℝ)*X 0 0+(5244411959/10000000000 : ℝ)*X 0 1+(2706599453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305605877/10000000000 : ℝ)*X 1 0+(-1972442411/10000000000 : ℝ)*X 1 1+(2706599427/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305605397/10000000000 : ℝ)*X 2 0+(135329981/250000000 : ℝ)*X 2 1+(-1972442537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330025313/10000000000 : ℝ)*X 0 0+(901862999/2000000000 : ℝ)*X 0 1+(4157506137/10000000000 : ℝ)*X 0 2+(4330025313/10000000000 : ℝ)*X 1 0+(901862999/2000000000 : ℝ)*X 1 1+(4157506137/10000000000 : ℝ)*X 1 2+(4330025313/10000000000 : ℝ)*X 2 0+(901862999/2000000000 : ℝ)*X 2 1+(4157506137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2176496368470721966345600797/230937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1801691953/100000000000000 : ℝ)*(base19) + (340266909/20000000000000 : ℝ)*(base23) + (16362123/25000000000000 : ℝ)*(lower2) + (230882323/100000000000000 : ℝ)*(upper3) + (4299123/2500000000000 : ℝ)*(upper5) + (2176002025704393/50000000000000 : ℝ)*(major0) + (2176002025704393/50000000000000 : ℝ)*(major1) + (2176002025704393/50000000000000 : ℝ)*(major2) + (2940981630603591/50000000000000 : ℝ)*(sp0) + (5881998520364147/100000000000000 : ℝ)*(sp1) + (1470499655180389/25000000000000 : ℝ)*(sp2) + (2821988839417717/100000000000000 : ℝ)*(sp3) + (37060848919/100000000000000 : ℝ)*(sp4) + (18627190003/100000000000000 : ℝ)*(sp7) + (70550186665193/2500000000000 : ℝ)*(f.failure) + (5882000322056101/100000000000000 : ℝ)*(f.sum) + (17735566450033/9237500000000000000000000000 : ℝ)*base66 + (2541648054255392967/461875000000000000000000000000000 : ℝ)*base67 + (3579732488676017967/461875000000000000000000000000000 : ℝ)*base69 + (6224423375845392967/461875000000000000000000000000000 : ℝ)*base71 + (26265058151683/9237500000000000000000000000 : ℝ)*base74 + (4256026090730392967/461875000000000000000000000000000 : ℝ)*base75 + (6375277720117892967/461875000000000000000000000000000 : ℝ)*base77 + (6341255176704767967/461875000000000000000000000000000 : ℝ)*base79 + (79415522607491/18475000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2200621/250000000000000000000 : ℝ)*base90 + (2200621/250000000000000000000 : ℝ)*base92 + (2200621/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (821925268859624286955032207/230937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51229287/3125000000000 : ℝ)*(base19) + (241007463/12500000000000 : ℝ)*(base23) + (15345207/4000000000000 : ℝ)*(upper2) + (75526011/25000000000000 : ℝ)*(upper3) + (148307269/100000000000000 : ℝ)*(upper5) + (2191765317133817/50000000000000 : ℝ)*(major0) + (2191765317133817/50000000000000 : ℝ)*(major1) + (2191765317133817/50000000000000 : ℝ)*(major2) + (12367910389/50000000000000 : ℝ)*(sp1) + (18535373317/50000000000000 : ℝ)*(sp2) + (592461062966073/10000000000000 : ℝ)*(sp4) + (370286515906423/6250000000000 : ℝ)*(sp5) + (740571453856799/12500000000000 : ℝ)*(sp6) + (88826578757453/3125000000000 : ℝ)*(sp7) + (88826578757453/3125000000000 : ℝ)*(f.failure) + (592461062966073/10000000000000 : ℝ)*(f.sum) + (2632614700327/9237500000000000000000000000 : ℝ)*base66 + (2867066887628001977/461875000000000000000000000000000 : ℝ)*base68 + (9290405809714251977/461875000000000000000000000000000 : ℝ)*base70 + (6327940485311751977/461875000000000000000000000000000 : ℝ)*base72 + (7309718894613/2309375000000000000000000000 : ℝ)*base74 + (1993182822943001977/461875000000000000000000000000000 : ℝ)*base76 + (4063973835441751977/461875000000000000000000000000000 : ℝ)*base78 + (2348860464406751977/461875000000000000000000000000000 : ℝ)*base80 + (37780693079577/9237500000000000000000000000 : ℝ)*base82 + (6342159/312500000000000000000 : ℝ)*base89 + (6342159/312500000000000000000 : ℝ)*base91 + (6342159/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1329_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11063/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1329_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1953/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1329_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1329_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1329_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1953/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1329_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
