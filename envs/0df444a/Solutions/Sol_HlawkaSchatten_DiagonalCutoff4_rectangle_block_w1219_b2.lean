-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1219_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:10:28.539394+00:00
-- url     : https://prove2.me/submissions/1fffe5d9-d675-437e-897c-54334dcc3b05

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
theorem support_rectangle_w1219_s6_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130578331/10000000000 : ℝ)*x 0 + (5391850313/10000000000 : ℝ)*x 1 + (2633343707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130578331/10000000000 : ℝ)^2103 ≤ (12953918657961/100000000000000 : ℝ)^1591 := by
    have hnat : (2130578331 : ℕ)^2103*100000000000000^1591 ≤ 12953918657961^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130578331 10000000000 12953918657961 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391850313/10000000000 : ℝ)^2103 ≤ (44198581164953/100000000000000 : ℝ)^1591 := by
    have hnat : (5391850313 : ℕ)^2103*100000000000000^1591 ≤ 44198581164953^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391850313 10000000000 44198581164953 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633343707/5000000000 : ℝ)^2103 ≤ (21423750079187/50000000000000 : ℝ)^1591 := by
    have hnat : (2633343707 : ℕ)^2103*50000000000000^1591 ≤ 21423750079187^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633343707 5000000000 21423750079187 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130578331/10000000000 : ℝ), (5391850313/10000000000 : ℝ), (2633343707/5000000000 : ℝ)] ![(12953918657961/100000000000000 : ℝ), (44198581164953/100000000000000 : ℝ), (21423750079187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130578331/10000000000 : ℝ)|^2103 ≤ (12953918657961/100000000000000 : ℝ)^1591
        have hw : |(-2130578331/10000000000 : ℝ)|=(2130578331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391850313/10000000000 : ℝ)|^2103 ≤ (44198581164953/100000000000000 : ℝ)^1591
        have hw : |(5391850313/10000000000 : ℝ)|=(5391850313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633343707/5000000000 : ℝ)|^2103 ≤ (21423750079187/50000000000000 : ℝ)^1591
        have hw : |(2633343707/5000000000 : ℝ)|=(2633343707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s6_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344483269/10000000000 : ℝ)*x 0 + (-2194047343/10000000000 : ℝ)*x 1 + (1316671933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344483269/10000000000 : ℝ)^2103 ≤ (10921518386919/25000000000000 : ℝ)^1591 := by
    have hnat : (5344483269 : ℕ)^2103*25000000000000^1591 ≤ 10921518386919^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344483269 10000000000 10921518386919 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194047343/10000000000 : ℝ)^2103 ≤ (3366605717183/25000000000000 : ℝ)^1591 := by
    have hnat : (2194047343 : ℕ)^2103*25000000000000^1591 ≤ 3366605717183^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194047343 10000000000 3366605717183 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316671933/2500000000 : ℝ)^2103 ≤ (42847503578043/100000000000000 : ℝ)^1591 := by
    have hnat : (1316671933 : ℕ)^2103*100000000000000^1591 ≤ 42847503578043^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316671933 2500000000 42847503578043 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344483269/10000000000 : ℝ), (-2194047343/10000000000 : ℝ), (1316671933/2500000000 : ℝ)] ![(10921518386919/25000000000000 : ℝ), (3366605717183/25000000000000 : ℝ), (42847503578043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344483269/10000000000 : ℝ)|^2103 ≤ (10921518386919/25000000000000 : ℝ)^1591
        have hw : |(5344483269/10000000000 : ℝ)|=(5344483269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194047343/10000000000 : ℝ)|^2103 ≤ (3366605717183/25000000000000 : ℝ)^1591
        have hw : |(-2194047343/10000000000 : ℝ)|=(2194047343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316671933/2500000000 : ℝ)|^2103 ≤ (42847503578043/100000000000000 : ℝ)^1591
        have hw : |(1316671933/2500000000 : ℝ)|=(1316671933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s6_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344483379/10000000000 : ℝ)*x 0 + (5266687527/10000000000 : ℝ)*x 1 + (-548511867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344483379/10000000000 : ℝ)^2103 ≤ (2730379671011/6250000000000 : ℝ)^1591 := by
    have hnat : (5344483379 : ℕ)^2103*6250000000000^1591 ≤ 2730379671011^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344483379 10000000000 2730379671011 6250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266687527/10000000000 : ℝ)^2103 ≤ (42847501373539/100000000000000 : ℝ)^1591 := by
    have hnat : (5266687527 : ℕ)^2103*100000000000000^1591 ≤ 42847501373539^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266687527 10000000000 42847501373539 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548511867/2500000000 : ℝ)^2103 ≤ (13466423882843/100000000000000 : ℝ)^1591 := by
    have hnat : (548511867 : ℕ)^2103*100000000000000^1591 ≤ 13466423882843^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548511867 2500000000 13466423882843 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344483379/10000000000 : ℝ), (5266687527/10000000000 : ℝ), (-548511867/2500000000 : ℝ)] ![(2730379671011/6250000000000 : ℝ), (42847501373539/100000000000000 : ℝ), (13466423882843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344483379/10000000000 : ℝ)|^2103 ≤ (2730379671011/6250000000000 : ℝ)^1591
        have hw : |(5344483379/10000000000 : ℝ)|=(5344483379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266687527/10000000000 : ℝ)|^2103 ≤ (42847501373539/100000000000000 : ℝ)^1591
        have hw : |(5266687527/10000000000 : ℝ)|=(5266687527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548511867/2500000000 : ℝ)|^2103 ≤ (13466423882843/100000000000000 : ℝ)^1591
        have hw : |(-548511867/2500000000 : ℝ)|=(548511867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s6_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1088481567/2500000000 : ℝ)*x 0 + (1057332957/2500000000 : ℝ)*x 1 + (4482106323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088481567/2500000000 : ℝ)^2103 ≤ (1332690533657/4000000000000 : ℝ)^1591 := by
    have hnat : (1088481567 : ℕ)^2103*4000000000000^1591 ≤ 1332690533657^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088481567 2500000000 1332690533657 4000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057332957/2500000000 : ℝ)^2103 ≤ (2003928515327/6250000000000 : ℝ)^1591 := by
    have hnat : (1057332957 : ℕ)^2103*6250000000000^1591 ≤ 2003928515327^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057332957 2500000000 2003928515327 6250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482106323/10000000000 : ℝ)^2103 ≤ (17309940196877/50000000000000 : ℝ)^1591 := by
    have hnat : (4482106323 : ℕ)^2103*50000000000000^1591 ≤ 17309940196877^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482106323 10000000000 17309940196877 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088481567/2500000000 : ℝ), (1057332957/2500000000 : ℝ), (4482106323/10000000000 : ℝ)] ![(1332690533657/4000000000000 : ℝ), (2003928515327/6250000000000 : ℝ), (17309940196877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088481567/2500000000 : ℝ)|^2103 ≤ (1332690533657/4000000000000 : ℝ)^1591
        have hw : |(1088481567/2500000000 : ℝ)|=(1088481567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057332957/2500000000 : ℝ)|^2103 ≤ (2003928515327/6250000000000 : ℝ)^1591
        have hw : |(1057332957/2500000000 : ℝ)|=(1057332957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482106323/10000000000 : ℝ)|^2103 ≤ (17309940196877/50000000000000 : ℝ)^1591
        have hw : |(4482106323/10000000000 : ℝ)|=(4482106323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s6_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130582987/10000000000 : ℝ)*x 0 + (2633501989/5000000000 : ℝ)*x 1 + (5391532673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130582987/10000000000 : ℝ)^2103 ≤ (6476978038209/50000000000000 : ℝ)^1591 := by
    have hnat : (2130582987 : ℕ)^2103*50000000000000^1591 ≤ 6476978038209^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130582987 10000000000 6476978038209 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633501989/5000000000 : ℝ)^2103 ≤ (8570180883741/20000000000000 : ℝ)^1591 := by
    have hnat : (2633501989 : ℕ)^2103*20000000000000^1591 ≤ 8570180883741^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633501989 5000000000 8570180883741 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391532673/10000000000 : ℝ)^2103 ≤ (44195139483553/100000000000000 : ℝ)^1591 := by
    have hnat : (5391532673 : ℕ)^2103*100000000000000^1591 ≤ 44195139483553^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391532673 10000000000 44195139483553 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130582987/10000000000 : ℝ), (2633501989/5000000000 : ℝ), (5391532673/10000000000 : ℝ)] ![(6476978038209/50000000000000 : ℝ), (8570180883741/20000000000000 : ℝ), (44195139483553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130582987/10000000000 : ℝ)|^2103 ≤ (6476978038209/50000000000000 : ℝ)^1591
        have hw : |(-2130582987/10000000000 : ℝ)|=(2130582987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633501989/5000000000 : ℝ)|^2103 ≤ (8570180883741/20000000000000 : ℝ)^1591
        have hw : |(2633501989/5000000000 : ℝ)|=(2633501989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391532673/10000000000 : ℝ)|^2103 ≤ (44195139483553/100000000000000 : ℝ)^1591
        have hw : |(5391532673/10000000000 : ℝ)|=(5391532673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s6_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656298849/5000000000 : ℝ)*x 0 + (-2069202267/10000000000 : ℝ)*x 1 + (2695766339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656298849/5000000000 : ℝ)^2103 ≤ (43341895705301/100000000000000 : ℝ)^1591 := by
    have hnat : (2656298849 : ℕ)^2103*100000000000000^1591 ≤ 43341895705301^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656298849 5000000000 43341895705301 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069202267/10000000000 : ℝ)^2103 ≤ (12462964751927/100000000000000 : ℝ)^1591 := by
    have hnat : (2069202267 : ℕ)^2103*100000000000000^1591 ≤ 12462964751927^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069202267 10000000000 12462964751927 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695766339/5000000000 : ℝ)^2103 ≤ (690549055277/1562500000000 : ℝ)^1591 := by
    have hnat : (2695766339 : ℕ)^2103*1562500000000^1591 ≤ 690549055277^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695766339 5000000000 690549055277 1562500000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656298849/5000000000 : ℝ), (-2069202267/10000000000 : ℝ), (2695766339/5000000000 : ℝ)] ![(43341895705301/100000000000000 : ℝ), (12462964751927/100000000000000 : ℝ), (690549055277/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656298849/5000000000 : ℝ)|^2103 ≤ (43341895705301/100000000000000 : ℝ)^1591
        have hw : |(2656298849/5000000000 : ℝ)|=(2656298849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069202267/10000000000 : ℝ)|^2103 ≤ (12462964751927/100000000000000 : ℝ)^1591
        have hw : |(-2069202267/10000000000 : ℝ)|=(2069202267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695766339/5000000000 : ℝ)|^2103 ≤ (690549055277/1562500000000 : ℝ)^1591
        have hw : |(2695766339/5000000000 : ℝ)|=(2695766339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s6_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312597707/10000000000 : ℝ)*x 0 + (5391532669/10000000000 : ℝ)*x 1 + (-413840453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312597707/10000000000 : ℝ)^2103 ≤ (8668379160471/20000000000000 : ℝ)^1591 := by
    have hnat : (5312597707 : ℕ)^2103*20000000000000^1591 ≤ 8668379160471^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312597707 10000000000 8668379160471 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391532669/10000000000 : ℝ)^2103 ≤ (44195139440213/100000000000000 : ℝ)^1591 := by
    have hnat : (5391532669 : ℕ)^2103*100000000000000^1591 ≤ 44195139440213^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391532669 10000000000 44195139440213 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413840453/2000000000 : ℝ)^2103 ≤ (3115741184001/25000000000000 : ℝ)^1591 := by
    have hnat : (413840453 : ℕ)^2103*25000000000000^1591 ≤ 3115741184001^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413840453 2000000000 3115741184001 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312597707/10000000000 : ℝ), (5391532669/10000000000 : ℝ), (-413840453/2000000000 : ℝ)] ![(8668379160471/20000000000000 : ℝ), (44195139440213/100000000000000 : ℝ), (3115741184001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312597707/10000000000 : ℝ)|^2103 ≤ (8668379160471/20000000000000 : ℝ)^1591
        have hw : |(5312597707/10000000000 : ℝ)|=(5312597707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391532669/10000000000 : ℝ)|^2103 ≤ (44195139440213/100000000000000 : ℝ)^1591
        have hw : |(5391532669/10000000000 : ℝ)|=(5391532669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413840453/2000000000 : ℝ)|^2103 ≤ (3115741184001/25000000000000 : ℝ)^1591
        have hw : |(-413840453/2000000000 : ℝ)|=(413840453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s6_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (34015123/78125000 : ℝ)*x 0 + (4481467227/10000000000 : ℝ)*x 1 + (4229973379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34015123/78125000 : ℝ)^2103 ≤ (33317359189313/100000000000000 : ℝ)^1591 := by
    have hnat : (34015123 : ℕ)^2103*100000000000000^1591 ≤ 33317359189313^1591*78125000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34015123 78125000 33317359189313 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481467227/10000000000 : ℝ)^2103 ≤ (17306677786117/50000000000000 : ℝ)^1591 := by
    have hnat : (4481467227 : ℕ)^2103*50000000000000^1591 ≤ 17306677786117^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481467227 10000000000 17306677786117 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229973379/10000000000 : ℝ)^2103 ≤ (32069285214151/100000000000000 : ℝ)^1591 := by
    have hnat : (4229973379 : ℕ)^2103*100000000000000^1591 ≤ 32069285214151^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229973379 10000000000 32069285214151 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34015123/78125000 : ℝ), (4481467227/10000000000 : ℝ), (4229973379/10000000000 : ℝ)] ![(33317359189313/100000000000000 : ℝ), (17306677786117/50000000000000 : ℝ), (32069285214151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34015123/78125000 : ℝ)|^2103 ≤ (33317359189313/100000000000000 : ℝ)^1591
        have hw : |(34015123/78125000 : ℝ)|=(34015123/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481467227/10000000000 : ℝ)|^2103 ≤ (17306677786117/50000000000000 : ℝ)^1591
        have hw : |(4481467227/10000000000 : ℝ)|=(4481467227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229973379/10000000000 : ℝ)|^2103 ≤ (32069285214151/100000000000000 : ℝ)^1591
        have hw : |(4229973379/10000000000 : ℝ)|=(4229973379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5723/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11423/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (13500994345714103/100000000000000000000 : ℝ) := by
    have hpowers : (11423/100000 : ℝ)^8411 ≤ (13500994345714103/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11423 : ℕ)^8411*100000000000000000000^2048 ≤ 13500994345714103^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11423 100000 13500994345714103 100000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11423/100000 : ℝ)) (X := (13500994345714103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (1290071738118463/4000000000000000000 : ℝ) := by
    have hpowers : (14121/100000 : ℝ)^8411 ≤ (1290071738118463/4000000000000000000 : ℝ)^2048 := by
      have hnat : (14121 : ℕ)^8411*4000000000000000000^2048 ≤ 1290071738118463^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 100000 1290071738118463 4000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/100000 : ℝ)) (X := (1290071738118463/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013500994345714103/50000000000000000000 : ℝ) ≤ (10000657406082381/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (50013500994345714103/50000000000000000000 : ℝ)^2048 ≤ (10000657406082381/10000000000000000 : ℝ)^8411 := by
      have hnat : (50013500994345714103 : ℕ)^2048*10000000000000000^8411 ≤ 10000657406082381^8411*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013500994345714103 50000000000000000000 10000657406082381 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000657406082381/10000000000000000 : ℝ)) (X := (50013500994345714103/50000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022876393899337839/50000000000000000000 : ℝ) ≤ (625069615308483/625000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (50022876393899337839/50000000000000000000 : ℝ)^2048 ≤ (625069615308483/625000000000000 : ℝ)^8411 := by
      have hnat : (50022876393899337839 : ℕ)^2048*625000000000000^8411 ≤ 625069615308483^8411*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022876393899337839 50000000000000000000 625069615308483 625000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625069615308483/625000000000000 : ℝ)) (X := (50022876393899337839/50000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001290071738118463/2000000000000000000 : ℝ) ≤ (400062811351563/400000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (2001290071738118463/2000000000000000000 : ℝ)^2048 ≤ (400062811351563/400000000000000 : ℝ)^8411 := by
      have hnat : (2001290071738118463 : ℕ)^2048*400000000000000^8411 ≤ 400062811351563^8411*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001290071738118463 2000000000000000000 400062811351563 400000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400062811351563/400000000000000 : ℝ)) (X := (2001290071738118463/2000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13500994345714103/100000000000000000000 : ℝ) ≤ ((3371418234945837297/3372500000000000000 : ℝ)+2*(456438853347/269800000000000 : ℝ)*(11423/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (3371418234945837297/3372500000000000000 : ℝ)+2*(456438853347/269800000000000 : ℝ)*(11423/100000 : ℝ)=(10000657406082381/10000000000000000 : ℝ) by norm_num, show 1+2*(13500994345714103/100000000000000000000 : ℝ)=(50013500994345714103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1290071738118463/4000000000000000000 : ℝ)+(13500994345714103/100000000000000000000 : ℝ) ≤ ((3371418234945837297/3372500000000000000 : ℝ)+(456438853347/269800000000000 : ℝ)*((14121/100000 : ℝ)+(11423/100000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (3371418234945837297/3372500000000000000 : ℝ)+(456438853347/269800000000000 : ℝ)*((14121/100000 : ℝ)+(11423/100000 : ℝ))=(625069615308483/625000000000000 : ℝ) by norm_num, show 1+(1290071738118463/4000000000000000000 : ℝ)+(13500994345714103/100000000000000000000 : ℝ)=(50022876393899337839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1290071738118463/4000000000000000000 : ℝ) ≤ ((3371418234945837297/3372500000000000000 : ℝ)+2*(456438853347/269800000000000 : ℝ)*(14121/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (3371418234945837297/3372500000000000000 : ℝ)+2*(456438853347/269800000000000 : ℝ)*(14121/100000 : ℝ)=(400062811351563/400000000000000 : ℝ) by norm_num, show 1+2*(1290071738118463/4000000000000000000 : ℝ)=(2001290071738118463/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3371418234945837297/3372500000000000000 : ℝ)*(X 1 0+X 2 0)+(456438853347/269800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (3371418234945837297/3372500000000000000 : ℝ)) (alpha := (456438853347/269800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3371418234945837297/3372500000000000000 : ℝ)*(X 0 1+X 2 1)+(456438853347/269800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (3371418234945837297/3372500000000000000 : ℝ)) (alpha := (456438853347/269800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3371418234945837297/3372500000000000000 : ℝ)*(X 0 2+X 1 2)+(456438853347/269800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (3371418234945837297/3372500000000000000 : ℝ)) (alpha := (456438853347/269800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2130578331/10000000000 : ℝ)*X 0 0+(5391850313/10000000000 : ℝ)*X 0 1+(2633343707/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344483269/10000000000 : ℝ)*X 1 0+(-2194047343/10000000000 : ℝ)*X 1 1+(1316671933/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344483379/10000000000 : ℝ)*X 2 0+(5266687527/10000000000 : ℝ)*X 2 1+(-548511867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088481567/2500000000 : ℝ)*X 0 0+(1057332957/2500000000 : ℝ)*X 0 1+(4482106323/10000000000 : ℝ)*X 0 2+(1088481567/2500000000 : ℝ)*X 1 0+(1057332957/2500000000 : ℝ)*X 1 1+(4482106323/10000000000 : ℝ)*X 1 2+(1088481567/2500000000 : ℝ)*X 2 0+(1057332957/2500000000 : ℝ)*X 2 1+(4482106323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2130582987/10000000000 : ℝ)*X 0 0+(2633501989/5000000000 : ℝ)*X 0 1+(5391532673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656298849/5000000000 : ℝ)*X 1 0+(-2069202267/10000000000 : ℝ)*X 1 1+(2695766339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312597707/10000000000 : ℝ)*X 2 0+(5391532669/10000000000 : ℝ)*X 2 1+(-413840453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34015123/78125000 : ℝ)*X 0 0+(4481467227/10000000000 : ℝ)*X 0 1+(4229973379/10000000000 : ℝ)*X 0 2+(34015123/78125000 : ℝ)*X 1 0+(4481467227/10000000000 : ℝ)*X 1 1+(4229973379/10000000000 : ℝ)*X 1 2+(34015123/78125000 : ℝ)*X 2 0+(4481467227/10000000000 : ℝ)*X 2 1+(4229973379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45316696529917926477088671/10539062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (738332041/100000000000000 : ℝ)*(base19) + (225494383/25000000000000 : ℝ)*(base23) + (240164547/100000000000000 : ℝ)*(upper3) + (426117/100000000000000 : ℝ)*(upper4) + (65226277/100000000000000 : ℝ)*(upper5) + (1493222294751787/25000000000000 : ℝ)*(major0) + (1493222294751787/25000000000000 : ℝ)*(major1) + (1493222294751787/25000000000000 : ℝ)*(major2) + (7989624071390739/100000000000000 : ℝ)*(sp0) + (998706554956669/12500000000000 : ℝ)*(sp1) + (7989652276007861/100000000000000 : ℝ)*(sp2) + (3956107946531561/100000000000000 : ℝ)*(sp3) + (14553297327/50000000000000 : ℝ)*(sp4) + (2136271003/12500000000000 : ℝ)*(sp7) + (61814453698431/1562500000000 : ℝ)*(f.failure) + (7989653177985393/100000000000000 : ℝ)*(f.sum) + (14139414037913/6745000000000000000000000000 : ℝ)*base65 + (1174664414320325261/84312500000000000000000000000000 : ℝ)*base68 + (716335299738325261/84312500000000000000000000000000 : ℝ)*base70 + (47718584253637761/84312500000000000000000000000000 : ℝ)*base72 + (3395710613361/3372500000000000000000000000 : ℝ)*base74 + (710896180302325261/84312500000000000000000000000000 : ℝ)*base76 + (655104123420174739/84312500000000000000000000000000 : ℝ)*base77 + (652657467631075261/84312500000000000000000000000000 : ℝ)*base80 + (28594756020317/6745000000000000000000000000 : ℝ)*base82 + (957199/156250000000000000000 : ℝ)*base90 + (957199/156250000000000000000 : ℝ)*base92 + (957199/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57419268569565049654683/13490000000000000000000000000 : ℝ) := by norm_num
    linear_combination (767276443/100000000000000 : ℝ)*(base19) + (843787043/100000000000000 : ℝ)*(base23) + (84624519/100000000000000 : ℝ)*(upper3) + (14046721/50000000000000 : ℝ)*(lower4) + (85268053/100000000000000 : ℝ)*(upper5) + (6003258770383207/100000000000000 : ℝ)*(major0) + (6003258770383207/100000000000000 : ℝ)*(major1) + (6003258770383207/100000000000000 : ℝ)*(major2) + (10933060127/50000000000000 : ℝ)*(sp1) + (147103077/625000000000 : ℝ)*(sp2) + (2007569288856151/25000000000000 : ℝ)*(sp4) + (8030254522027907/100000000000000 : ℝ)*(sp5) + (200756319378631/2500000000000 : ℝ)*(sp6) + (1988120121730367/50000000000000 : ℝ)*(sp7) + (1988120121730367/50000000000000 : ℝ)*(f.failure) + (2007569288856151/25000000000000 : ℝ)*(f.sum) + (47603895885309/13490000000000000000000000000 : ℝ)*base65 + (680070901918433979/337250000000000000000000000000000 : ℝ)*base67 + (1246182166194566021/337250000000000000000000000000000 : ℝ)*base70 + (2117253285637933979/337250000000000000000000000000000 : ℝ)*base71 + (8563156272599/13490000000000000000000000000 : ℝ)*base73 + (3924919249524066021/337250000000000000000000000000000 : ℝ)*base76 + (699501055425066021/337250000000000000000000000000000 : ℝ)*base78 + (3982401490590433979/337250000000000000000000000000000 : ℝ)*base79 + (101634920248911/13490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12144543/5000000000000000000000 : ℝ)*base90 + (12144543/5000000000000000000000 : ℝ)*base92 + (12144543/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1219_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1219_s7_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-213059737/1000000000 : ℝ)*x 0 + (1347906291/2500000000 : ℝ)*x 1 + (131672501/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213059737/1000000000 : ℝ)^2103 ≤ (12954071667149/100000000000000 : ℝ)^1591 := by
    have hnat : (213059737 : ℕ)^2103*100000000000000^1591 ≤ 12954071667149^1591*1000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213059737 1000000000 12954071667149 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347906291/2500000000 : ℝ)^2103 ≤ (22098070815973/50000000000000 : ℝ)^1591 := by
    have hnat : (1347906291 : ℕ)^2103*50000000000000^1591 ≤ 22098070815973^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347906291 2500000000 22098070815973 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131672501/250000000 : ℝ)^2103 ≤ (21424893342411/50000000000000 : ℝ)^1591 := by
    have hnat : (131672501 : ℕ)^2103*50000000000000^1591 ≤ 21424893342411^1591*250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131672501 250000000 21424893342411 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213059737/1000000000 : ℝ), (1347906291/2500000000 : ℝ), (131672501/250000000 : ℝ)] ![(12954071667149/100000000000000 : ℝ), (22098070815973/50000000000000 : ℝ), (21424893342411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213059737/1000000000 : ℝ)|^2103 ≤ (12954071667149/100000000000000 : ℝ)^1591
        have hw : |(-213059737/1000000000 : ℝ)|=(213059737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347906291/2500000000 : ℝ)|^2103 ≤ (22098070815973/50000000000000 : ℝ)^1591
        have hw : |(1347906291/2500000000 : ℝ)|=(1347906291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131672501/250000000 : ℝ)|^2103 ≤ (21424893342411/50000000000000 : ℝ)^1591
        have hw : |(131672501/250000000 : ℝ)|=(131672501/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s7_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336106623/2500000000 : ℝ)*x 0 + (-438768291/2000000000 : ℝ)*x 1 + (5266900101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336106623/2500000000 : ℝ)^2103 ≤ (43685460099213/100000000000000 : ℝ)^1591 := by
    have hnat : (1336106623 : ℕ)^2103*100000000000000^1591 ≤ 43685460099213^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336106623 2500000000 43685460099213 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438768291/2000000000 : ℝ)^2103 ≤ (1683094068523/12500000000000 : ℝ)^1591 := by
    have hnat : (438768291 : ℕ)^2103*12500000000000^1591 ≤ 1683094068523^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438768291 2000000000 1683094068523 12500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266900101/10000000000 : ℝ)^2103 ≤ (8569957468161/20000000000000 : ℝ)^1591 := by
    have hnat : (5266900101 : ℕ)^2103*20000000000000^1591 ≤ 8569957468161^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266900101 10000000000 8569957468161 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336106623/2500000000 : ℝ), (-438768291/2000000000 : ℝ), (5266900101/10000000000 : ℝ)] ![(43685460099213/100000000000000 : ℝ), (1683094068523/12500000000000 : ℝ), (8569957468161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336106623/2500000000 : ℝ)|^2103 ≤ (43685460099213/100000000000000 : ℝ)^1591
        have hw : |(1336106623/2500000000 : ℝ)|=(1336106623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438768291/2000000000 : ℝ)|^2103 ≤ (1683094068523/12500000000000 : ℝ)^1591
        have hw : |(-438768291/2000000000 : ℝ)|=(438768291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266900101/10000000000 : ℝ)|^2103 ≤ (8569957468161/20000000000000 : ℝ)^1591
        have hw : |(5266900101/10000000000 : ℝ)|=(5266900101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s7_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334026659/625000000 : ℝ)*x 0 + (210676003/400000000 : ℝ)*x 1 + (-2193841419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334026659/625000000 : ℝ)^2103 ≤ (43685460661047/100000000000000 : ℝ)^1591 := by
    have hnat : (334026659 : ℕ)^2103*100000000000000^1591 ≤ 43685460661047^1591*625000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334026659 625000000 43685460661047 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210676003/400000000 : ℝ)^2103 ≤ (21424893530603/50000000000000 : ℝ)^1591 := by
    have hnat : (210676003 : ℕ)^2103*50000000000000^1591 ≤ 21424893530603^1591*400000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210676003 400000000 21424893530603 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193841419/10000000000 : ℝ)^2103 ≤ (13464752256129/100000000000000 : ℝ)^1591 := by
    have hnat : (2193841419 : ℕ)^2103*100000000000000^1591 ≤ 13464752256129^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193841419 10000000000 13464752256129 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334026659/625000000 : ℝ), (210676003/400000000 : ℝ), (-2193841419/10000000000 : ℝ)] ![(43685460661047/100000000000000 : ℝ), (21424893530603/50000000000000 : ℝ), (13464752256129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334026659/625000000 : ℝ)|^2103 ≤ (43685460661047/100000000000000 : ℝ)^1591
        have hw : |(334026659/625000000 : ℝ)|=(334026659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210676003/400000000 : ℝ)|^2103 ≤ (21424893530603/50000000000000 : ℝ)^1591
        have hw : |(210676003/400000000 : ℝ)|=(210676003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2193841419/10000000000 : ℝ)|^2103 ≤ (13464752256129/100000000000000 : ℝ)^1591
        have hw : |(-2193841419/10000000000 : ℝ)|=(2193841419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s7_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2176968613/5000000000 : ℝ)*x 0 + (4229772457/10000000000 : ℝ)*x 1 + (224083149/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176968613/5000000000 : ℝ)^2103 ≤ (1665868708973/5000000000000 : ℝ)^1591 := by
    have hnat : (2176968613 : ℕ)^2103*5000000000000^1591 ≤ 1665868708973^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176968613 5000000000 1665868708973 5000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229772457/10000000000 : ℝ)^2103 ≤ (16033635872657/50000000000000 : ℝ)^1591 := by
    have hnat : (4229772457 : ℕ)^2103*50000000000000^1591 ≤ 16033635872657^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229772457 10000000000 16033635872657 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224083149/500000000 : ℝ)^2103 ≤ (17307677035883/50000000000000 : ℝ)^1591 := by
    have hnat : (224083149 : ℕ)^2103*50000000000000^1591 ≤ 17307677035883^1591*500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224083149 500000000 17307677035883 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176968613/5000000000 : ℝ), (4229772457/10000000000 : ℝ), (224083149/500000000 : ℝ)] ![(1665868708973/5000000000000 : ℝ), (16033635872657/50000000000000 : ℝ), (17307677035883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176968613/5000000000 : ℝ)|^2103 ≤ (1665868708973/5000000000000 : ℝ)^1591
        have hw : |(2176968613/5000000000 : ℝ)|=(2176968613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229772457/10000000000 : ℝ)|^2103 ≤ (16033635872657/50000000000000 : ℝ)^1591
        have hw : |(4229772457/10000000000 : ℝ)|=(4229772457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224083149/500000000 : ℝ)|^2103 ≤ (17307677035883/50000000000000 : ℝ)^1591
        have hw : |(224083149/500000000 : ℝ)|=(224083149/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s7_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-53265053/250000000 : ℝ)*x 0 + (1316803941/2500000000 : ℝ)*x 1 + (134782707/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53265053/250000000 : ℝ)^2103 ≤ (12954109841157/100000000000000 : ℝ)^1591 := by
    have hnat : (53265053 : ℕ)^2103*100000000000000^1591 ≤ 12954109841157^1591*250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53265053 250000000 12954109841157 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316803941/2500000000 : ℝ)^2103 ≤ (21426590977999/50000000000000 : ℝ)^1591 := by
    have hnat : (1316803941 : ℕ)^2103*50000000000000^1591 ≤ 21426590977999^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316803941 2500000000 21426590977999 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134782707/250000000 : ℝ)^2103 ≤ (44192708187993/100000000000000 : ℝ)^1591 := by
    have hnat : (134782707 : ℕ)^2103*100000000000000^1591 ≤ 44192708187993^1591*250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134782707 250000000 44192708187993 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53265053/250000000 : ℝ), (1316803941/2500000000 : ℝ), (134782707/250000000 : ℝ)] ![(12954109841157/100000000000000 : ℝ), (21426590977999/50000000000000 : ℝ), (44192708187993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53265053/250000000 : ℝ)|^2103 ≤ (12954109841157/100000000000000 : ℝ)^1591
        have hw : |(-53265053/250000000 : ℝ)|=(53265053/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316803941/2500000000 : ℝ)|^2103 ≤ (21426590977999/50000000000000 : ℝ)^1591
        have hw : |(1316803941/2500000000 : ℝ)|=(1316803941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134782707/250000000 : ℝ)|^2103 ≤ (44192708187993/100000000000000 : ℝ)^1591
        have hw : |(134782707/250000000 : ℝ)|=(134782707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s7_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312652111/10000000000 : ℝ)*x 0 + (-2069431381/10000000000 : ℝ)*x 1 + (5391310169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312652111/10000000000 : ℝ)^2103 ≤ (43342482482801/100000000000000 : ℝ)^1591 := by
    have hnat : (5312652111 : ℕ)^2103*100000000000000^1591 ≤ 43342482482801^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312652111 10000000000 43342482482801 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069431381/10000000000 : ℝ)^2103 ≤ (12464788844517/100000000000000 : ℝ)^1591 := by
    have hnat : (2069431381 : ℕ)^2103*100000000000000^1591 ≤ 12464788844517^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069431381 10000000000 12464788844517 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391310169/10000000000 : ℝ)^2103 ≤ (883854573103/2000000000000 : ℝ)^1591 := by
    have hnat : (5391310169 : ℕ)^2103*2000000000000^1591 ≤ 883854573103^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391310169 10000000000 883854573103 2000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312652111/10000000000 : ℝ), (-2069431381/10000000000 : ℝ), (5391310169/10000000000 : ℝ)] ![(43342482482801/100000000000000 : ℝ), (12464788844517/100000000000000 : ℝ), (883854573103/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312652111/10000000000 : ℝ)|^2103 ≤ (43342482482801/100000000000000 : ℝ)^1591
        have hw : |(5312652111/10000000000 : ℝ)|=(5312652111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069431381/10000000000 : ℝ)|^2103 ≤ (12464788844517/100000000000000 : ℝ)^1591
        have hw : |(-2069431381/10000000000 : ℝ)|=(2069431381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391310169/10000000000 : ℝ)|^2103 ≤ (883854573103/2000000000000 : ℝ)^1591
        have hw : |(5391310169/10000000000 : ℝ)|=(5391310169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s7_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656326503/5000000000 : ℝ)*x 0 + (134782717/250000000 : ℝ)*x 1 + (-413886439/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656326503/5000000000 : ℝ)^2103 ≤ (8668498426859/20000000000000 : ℝ)^1591 := by
    have hnat : (2656326503 : ℕ)^2103*20000000000000^1591 ≤ 8668498426859^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656326503 5000000000 8668498426859 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134782717/250000000 : ℝ)^2103 ≤ (44192712521959/100000000000000 : ℝ)^1591 := by
    have hnat : (134782717 : ℕ)^2103*100000000000000^1591 ≤ 44192712521959^1591*250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134782717 250000000 44192712521959 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413886439/2000000000 : ℝ)^2103 ≤ (12464795325299/100000000000000 : ℝ)^1591 := by
    have hnat : (413886439 : ℕ)^2103*100000000000000^1591 ≤ 12464795325299^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413886439 2000000000 12464795325299 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656326503/5000000000 : ℝ), (134782717/250000000 : ℝ), (-413886439/2000000000 : ℝ)] ![(8668498426859/20000000000000 : ℝ), (44192712521959/100000000000000 : ℝ), (12464795325299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656326503/5000000000 : ℝ)|^2103 ≤ (8668498426859/20000000000000 : ℝ)^1591
        have hw : |(2656326503/5000000000 : ℝ)|=(2656326503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134782717/250000000 : ℝ)|^2103 ≤ (44192712521959/100000000000000 : ℝ)^1591
        have hw : |(134782717/250000000 : ℝ)|=(134782717/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413886439/2000000000 : ℝ)|^2103 ≤ (12464795325299/100000000000000 : ℝ)^1591
        have hw : |(-413886439/2000000000 : ℝ)|=(413886439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s7_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4353945983/10000000000 : ℝ)*x 0 + (896205987/2000000000 : ℝ)*x 1 + (4230408527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353945983/10000000000 : ℝ)^2103 ≤ (33317462754873/100000000000000 : ℝ)^1591 := by
    have hnat : (4353945983 : ℕ)^2103*100000000000000^1591 ≤ 33317462754873^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353945983 10000000000 33317462754873 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896205987/2000000000 : ℝ)^2103 ≤ (34608891232001/100000000000000 : ℝ)^1591 := by
    have hnat : (896205987 : ℕ)^2103*100000000000000^1591 ≤ 34608891232001^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896205987 2000000000 34608891232001 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230408527/10000000000 : ℝ)^2103 ≤ (16036823000801/50000000000000 : ℝ)^1591 := by
    have hnat : (4230408527 : ℕ)^2103*50000000000000^1591 ≤ 16036823000801^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230408527 10000000000 16036823000801 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353945983/10000000000 : ℝ), (896205987/2000000000 : ℝ), (4230408527/10000000000 : ℝ)] ![(33317462754873/100000000000000 : ℝ), (34608891232001/100000000000000 : ℝ), (16036823000801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353945983/10000000000 : ℝ)|^2103 ≤ (33317462754873/100000000000000 : ℝ)^1591
        have hw : |(4353945983/10000000000 : ℝ)|=(4353945983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896205987/2000000000 : ℝ)|^2103 ≤ (34608891232001/100000000000000 : ℝ)^1591
        have hw : |(896205987/2000000000 : ℝ)|=(896205987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230408527/10000000000 : ℝ)|^2103 ≤ (16036823000801/50000000000000 : ℝ)^1591
        have hw : |(4230408527/10000000000 : ℝ)|=(4230408527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (229/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5723/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5723/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5723/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5723/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5723/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5723/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5723/50000 : ℝ) ^ (8411/2048 : ℝ) ≤ (6806493470738283/50000000000000000000 : ℝ) := by
    have hpowers : (5723/50000 : ℝ)^8411 ≤ (6806493470738283/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5723 : ℕ)^8411*50000000000000000000^2048 ≤ 6806493470738283^2048*50000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5723 50000 6806493470738283 50000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5723/50000 : ℝ)) (X := (6806493470738283/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (32027265435684801/100000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^8411 ≤ (32027265435684801/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14097 : ℕ)^8411*100000000000000000000^2048 ≤ 32027265435684801^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 32027265435684801 100000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (32027265435684801/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006806493470738283/25000000000000000000 : ℝ) ≤ (5000331429397163/5000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (25006806493470738283/25000000000000000000 : ℝ)^2048 ≤ (5000331429397163/5000000000000000 : ℝ)^8411 := by
      have hnat : (25006806493470738283 : ℕ)^2048*5000000000000000^8411 ≤ 5000331429397163^8411*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006806493470738283 25000000000000000000 5000331429397163 5000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000331429397163/5000000000000000 : ℝ)) (X := (25006806493470738283/25000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045640252377161367/100000000000000000000 : ℝ) ≤ (10001111105750123/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (100045640252377161367/100000000000000000000 : ℝ)^2048 ≤ (10001111105750123/10000000000000000 : ℝ)^8411 := by
      have hnat : (100045640252377161367 : ℕ)^2048*10000000000000000^8411 ≤ 10001111105750123^8411*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045640252377161367 100000000000000000000 10001111105750123 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001111105750123/10000000000000000 : ℝ)) (X := (100045640252377161367/100000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032027265435684801/50000000000000000000 : ℝ) ≤ (15627436488603/15625000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (50032027265435684801/50000000000000000000 : ℝ)^2048 ≤ (15627436488603/15625000000000 : ℝ)^8411 := by
      have hnat : (50032027265435684801 : ℕ)^2048*15625000000000^8411 ≤ 15627436488603^8411*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032027265435684801 50000000000000000000 15627436488603 15625000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15627436488603/15625000000000 : ℝ)) (X := (50032027265435684801/50000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6806493470738283/50000000000000000000 : ℝ) ≤ ((13250747984675826651/13255000000000000000 : ℝ)+2*(448246955797/265100000000000 : ℝ)*(5723/50000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (13250747984675826651/13255000000000000000 : ℝ)+2*(448246955797/265100000000000 : ℝ)*(5723/50000 : ℝ)=(5000331429397163/5000000000000000 : ℝ) by norm_num, show 1+2*(6806493470738283/50000000000000000000 : ℝ)=(25006806493470738283/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32027265435684801/100000000000000000000 : ℝ)+(6806493470738283/50000000000000000000 : ℝ) ≤ ((13250747984675826651/13255000000000000000 : ℝ)+(448246955797/265100000000000 : ℝ)*((14097/100000 : ℝ)+(5723/50000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (13250747984675826651/13255000000000000000 : ℝ)+(448246955797/265100000000000 : ℝ)*((14097/100000 : ℝ)+(5723/50000 : ℝ))=(10001111105750123/10000000000000000 : ℝ) by norm_num, show 1+(32027265435684801/100000000000000000000 : ℝ)+(6806493470738283/50000000000000000000 : ℝ)=(100045640252377161367/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32027265435684801/100000000000000000000 : ℝ) ≤ ((13250747984675826651/13255000000000000000 : ℝ)+2*(448246955797/265100000000000 : ℝ)*(14097/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (13250747984675826651/13255000000000000000 : ℝ)+2*(448246955797/265100000000000 : ℝ)*(14097/100000 : ℝ)=(15627436488603/15625000000000 : ℝ) by norm_num, show 1+2*(32027265435684801/100000000000000000000 : ℝ)=(50032027265435684801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13250747984675826651/13255000000000000000 : ℝ)*(X 1 0+X 2 0)+(448246955797/265100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (5723/50000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (13250747984675826651/13255000000000000000 : ℝ)) (alpha := (448246955797/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13250747984675826651/13255000000000000000 : ℝ)*(X 0 1+X 2 1)+(448246955797/265100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (5723/50000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (13250747984675826651/13255000000000000000 : ℝ)) (alpha := (448246955797/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13250747984675826651/13255000000000000000 : ℝ)*(X 0 2+X 1 2)+(448246955797/265100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (5723/50000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (13250747984675826651/13255000000000000000 : ℝ)) (alpha := (448246955797/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213059737/1000000000 : ℝ)*X 0 0+(1347906291/2500000000 : ℝ)*X 0 1+(131672501/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336106623/2500000000 : ℝ)*X 1 0+(-438768291/2000000000 : ℝ)*X 1 1+(5266900101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334026659/625000000 : ℝ)*X 2 0+(210676003/400000000 : ℝ)*X 2 1+(-2193841419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176968613/5000000000 : ℝ)*X 0 0+(4229772457/10000000000 : ℝ)*X 0 1+(224083149/500000000 : ℝ)*X 0 2+(2176968613/5000000000 : ℝ)*X 1 0+(4229772457/10000000000 : ℝ)*X 1 1+(224083149/500000000 : ℝ)*X 1 2+(2176968613/5000000000 : ℝ)*X 2 0+(4229772457/10000000000 : ℝ)*X 2 1+(224083149/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53265053/250000000 : ℝ)*X 0 0+(1316803941/2500000000 : ℝ)*X 0 1+(134782707/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312652111/10000000000 : ℝ)*X 1 0+(-2069431381/10000000000 : ℝ)*X 1 1+(5391310169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656326503/5000000000 : ℝ)*X 2 0+(134782717/250000000 : ℝ)*X 2 1+(-413886439/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353945983/10000000000 : ℝ)*X 0 0+(896205987/2000000000 : ℝ)*X 0 1+(4230408527/10000000000 : ℝ)*X 0 2+(4353945983/10000000000 : ℝ)*X 1 0+(896205987/2000000000 : ℝ)*X 1 1+(4230408527/10000000000 : ℝ)*X 1 2+(4353945983/10000000000 : ℝ)*X 2 0+(896205987/2000000000 : ℝ)*X 2 1+(4230408527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147525107880419761310433429/16568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1834145563/100000000000000 : ℝ)*(base19) + (238318953/12500000000000 : ℝ)*(base23) + (22167529/12500000000000 : ℝ)*(upper3) + (1497689/50000000000000 : ℝ)*(upper4) + (15346949/6250000000000 : ℝ)*(upper5) + (299694508101057/5000000000000 : ℝ)*(major0) + (299694508101057/5000000000000 : ℝ)*(major1) + (299694508101057/5000000000000 : ℝ)*(major2) + (4008842798331279/50000000000000 : ℝ)*(sp0) + (8017743218983179/100000000000000 : ℝ)*(sp1) + (4008871573288559/50000000000000 : ℝ)*(sp2) + (397000721092621/10000000000000 : ℝ)*(sp3) + (7432058273/12500000000000 : ℝ)*(sp4) + (27763193437/100000000000000 : ℝ)*(sp7) + (1985017487059823/50000000000000 : ℝ)*(f.failure) + (4008872526564371/50000000000000 : ℝ)*(f.sum) + (166265528637/106040000000000000000000000 : ℝ)*base66 + (408082551615745107/66275000000000000000000000000000 : ℝ)*base67 + (1011067063161095107/66275000000000000000000000000000 : ℝ)*base69 + (320910400842904893/66275000000000000000000000000000 : ℝ)*base72 + (1123212576851/662750000000000000000000000 : ℝ)*base74 + (1497757841196370107/66275000000000000000000000000000 : ℝ)*base75 + (140877752388995107/66275000000000000000000000000000 : ℝ)*base77 + (370945371139195107/66275000000000000000000000000000 : ℝ)*base79 + (5883578476009/2651000000000000000000000000 : ℝ)*base81 + (49893967/5000000000000000000000 : ℝ)*base90 + (49893967/5000000000000000000000 : ℝ)*base92 + (49893967/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (390298379652290570327760657/41421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306247183/20000000000000 : ℝ)*(base19) + (3395517753/100000000000000 : ℝ)*(base23) + (10414209/3125000000000 : ℝ)*(upper2) + (4547703/2500000000000 : ℝ)*(upper3) + (188261090797939/3125000000000 : ℝ)*(major0) + (188261090797939/3125000000000 : ℝ)*(major1) + (188261090797939/3125000000000 : ℝ)*(major2) + (4111485913/2500000000000 : ℝ)*(sp1) + (36075456927/25000000000000 : ℝ)*(sp2) + (62140128571/100000000000000 : ℝ)*(sp3) + (1007312036546753/12500000000000 : ℝ)*(sp4) + (2014582575425397/25000000000000 : ℝ)*(sp5) + (4029174297514281/50000000000000 : ℝ)*(sp6) + (1995075532240773/50000000000000 : ℝ)*(sp7) + (1995106602305059/50000000000000 : ℝ)*(f.failure) + (1007312036546753/12500000000000 : ℝ)*(f.sum) + (146458962209/3313750000000000000000000000 : ℝ)*base65 + (62958511395037293/20710937500000000000000000000000 : ℝ)*base68 + (44877784083378539/41421875000000000000000000000000 : ℝ)*base69 + (228116112359472289/41421875000000000000000000000000 : ℝ)*base71 + (666745097861/13255000000000000000000000000 : ℝ)*base73 + (22890300115066039/41421875000000000000000000000000 : ℝ)*base75 + (573802435784222289/41421875000000000000000000000000 : ℝ)*base77 + (209102809069618957/20710937500000000000000000000000 : ℝ)*base79 + (3644582949893/1656875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22372989/5000000000000000000000 : ℝ)*base89 + (22372989/5000000000000000000000 : ℝ)*base91 + (22372989/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1219_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1219_s8_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065300191/5000000000 : ℝ)*x 0 + (5391587457/10000000000 : ℝ)*x 1 + (5266935781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065300191/5000000000 : ℝ)^2103 ≤ (2590819174697/20000000000000 : ℝ)^1591 := by
    have hnat : (1065300191 : ℕ)^2103*20000000000000^1591 ≤ 2590819174697^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065300191 5000000000 2590819174697 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391587457/10000000000 : ℝ)^2103 ≤ (8839146614501/20000000000000 : ℝ)^1591 := by
    have hnat : (5391587457 : ℕ)^2103*20000000000000^1591 ≤ 8839146614501^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391587457 10000000000 8839146614501 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266935781/10000000000 : ℝ)^2103 ≤ (857003420749/2000000000000 : ℝ)^1591 := by
    have hnat : (5266935781 : ℕ)^2103*2000000000000^1591 ≤ 857003420749^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266935781 10000000000 857003420749 2000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065300191/5000000000 : ℝ), (5391587457/10000000000 : ℝ), (5266935781/10000000000 : ℝ)] ![(2590819174697/20000000000000 : ℝ), (8839146614501/20000000000000 : ℝ), (857003420749/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065300191/5000000000 : ℝ)|^2103 ≤ (2590819174697/20000000000000 : ℝ)^1591
        have hw : |(-1065300191/5000000000 : ℝ)|=(1065300191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391587457/10000000000 : ℝ)|^2103 ≤ (8839146614501/20000000000000 : ℝ)^1591
        have hw : |(5391587457/10000000000 : ℝ)|=(5391587457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266935781/10000000000 : ℝ)|^2103 ≤ (857003420749/2000000000000 : ℝ)^1591
        have hw : |(5266935781/10000000000 : ℝ)|=(5266935781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s8_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344416999/10000000000 : ℝ)*x 0 + (-2193806041/10000000000 : ℝ)*x 1 + (2633468177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344416999/10000000000 : ℝ)^2103 ≤ (43685357532071/100000000000000 : ℝ)^1591 := by
    have hnat : (5344416999 : ℕ)^2103*100000000000000^1591 ≤ 43685357532071^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344416999 10000000000 43685357532071 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193806041/10000000000 : ℝ)^2103 ≤ (336611631197/2500000000000 : ℝ)^1591 := by
    have hnat : (2193806041 : ℕ)^2103*2500000000000^1591 ≤ 336611631197^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193806041 10000000000 336611631197 2500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633468177/5000000000 : ℝ)^2103 ≤ (21425088599701/50000000000000 : ℝ)^1591 := by
    have hnat : (2633468177 : ℕ)^2103*50000000000000^1591 ≤ 21425088599701^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633468177 5000000000 21425088599701 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344416999/10000000000 : ℝ), (-2193806041/10000000000 : ℝ), (2633468177/5000000000 : ℝ)] ![(43685357532071/100000000000000 : ℝ), (336611631197/2500000000000 : ℝ), (21425088599701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344416999/10000000000 : ℝ)|^2103 ≤ (43685357532071/100000000000000 : ℝ)^1591
        have hw : |(5344416999/10000000000 : ℝ)|=(5344416999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193806041/10000000000 : ℝ)|^2103 ≤ (336611631197/2500000000000 : ℝ)^1591
        have hw : |(-2193806041/10000000000 : ℝ)|=(2193806041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633468177/5000000000 : ℝ)|^2103 ≤ (21425088599701/50000000000000 : ℝ)^1591
        have hw : |(2633468177/5000000000 : ℝ)|=(2633468177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s8_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (16701303/31250000 : ℝ)*x 0 + (1053387231/2000000000 : ℝ)*x 1 + (-1096903179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16701303/31250000 : ℝ)^2103 ≤ (8737071422139/20000000000000 : ℝ)^1591 := by
    have hnat : (16701303 : ℕ)^2103*20000000000000^1591 ≤ 8737071422139^1591*31250000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16701303 31250000 8737071422139 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053387231/2000000000 : ℝ)^2103 ≤ (42850175059387/100000000000000 : ℝ)^1591 := by
    have hnat : (1053387231 : ℕ)^2103*100000000000000^1591 ≤ 42850175059387^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053387231 2000000000 42850175059387 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096903179/5000000000 : ℝ)^2103 ≤ (6732233909787/50000000000000 : ℝ)^1591 := by
    have hnat : (1096903179 : ℕ)^2103*50000000000000^1591 ≤ 6732233909787^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096903179 5000000000 6732233909787 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16701303/31250000 : ℝ), (1053387231/2000000000 : ℝ), (-1096903179/5000000000 : ℝ)] ![(8737071422139/20000000000000 : ℝ), (42850175059387/100000000000000 : ℝ), (6732233909787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16701303/31250000 : ℝ)|^2103 ≤ (8737071422139/20000000000000 : ℝ)^1591
        have hw : |(16701303/31250000 : ℝ)|=(16701303/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053387231/2000000000 : ℝ)|^2103 ≤ (42850175059387/100000000000000 : ℝ)^1591
        have hw : |(1053387231/2000000000 : ℝ)|=(1053387231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1096903179/5000000000 : ℝ)|^2103 ≤ (6732233909787/50000000000000 : ℝ)^1591
        have hw : |(-1096903179/5000000000 : ℝ)|=(1096903179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s8_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (217696969/500000000 : ℝ)*x 0 + (2114923307/5000000000 : ℝ)*x 1 + (896317611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217696969/500000000 : ℝ)^2103 ≤ (33317395966761/100000000000000 : ℝ)^1591 := by
    have hnat : (217696969 : ℕ)^2103*100000000000000^1591 ≤ 33317395966761^1591*500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217696969 500000000 33317395966761 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114923307/5000000000 : ℝ)^2103 ≤ (16034007439953/50000000000000 : ℝ)^1591 := by
    have hnat : (2114923307 : ℕ)^2103*50000000000000^1591 ≤ 16034007439953^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114923307 5000000000 16034007439953 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896317611/2000000000 : ℝ)^2103 ≤ (17307294568623/50000000000000 : ℝ)^1591 := by
    have hnat : (896317611 : ℕ)^2103*50000000000000^1591 ≤ 17307294568623^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896317611 2000000000 17307294568623 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217696969/500000000 : ℝ), (2114923307/5000000000 : ℝ), (896317611/2000000000 : ℝ)] ![(33317395966761/100000000000000 : ℝ), (16034007439953/50000000000000 : ℝ), (17307294568623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217696969/500000000 : ℝ)|^2103 ≤ (33317395966761/100000000000000 : ℝ)^1591
        have hw : |(217696969/500000000 : ℝ)|=(217696969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114923307/5000000000 : ℝ)|^2103 ≤ (16034007439953/50000000000000 : ℝ)^1591
        have hw : |(2114923307/5000000000 : ℝ)|=(2114923307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896317611/2000000000 : ℝ)|^2103 ≤ (17307294568623/50000000000000 : ℝ)^1591
        have hw : |(896317611/2000000000 : ℝ)|=(896317611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s8_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-16645349/78125000 : ℝ)*x 0 + (2633624997/5000000000 : ℝ)*x 1 + (1347818103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16645349/78125000 : ℝ)^2103 ≤ (12954130350657/100000000000000 : ℝ)^1591 := by
    have hnat : (16645349 : ℕ)^2103*100000000000000^1591 ≤ 12954130350657^1591*78125000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16645349 78125000 12954130350657 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633624997/5000000000 : ℝ)^2103 ≤ (21426775033337/50000000000000 : ℝ)^1591 := by
    have hnat : (2633624997 : ℕ)^2103*50000000000000^1591 ≤ 21426775033337^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633624997 5000000000 21426775033337 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347818103/2500000000 : ℝ)^2103 ≤ (22096159780823/50000000000000 : ℝ)^1591 := by
    have hnat : (1347818103 : ℕ)^2103*50000000000000^1591 ≤ 22096159780823^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347818103 2500000000 22096159780823 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16645349/78125000 : ℝ), (2633624997/5000000000 : ℝ), (1347818103/2500000000 : ℝ)] ![(12954130350657/100000000000000 : ℝ), (21426775033337/50000000000000 : ℝ), (22096159780823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16645349/78125000 : ℝ)|^2103 ≤ (12954130350657/100000000000000 : ℝ)^1591
        have hw : |(-16645349/78125000 : ℝ)|=(16645349/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633624997/5000000000 : ℝ)|^2103 ≤ (21426775033337/50000000000000 : ℝ)^1591
        have hw : |(2633624997/5000000000 : ℝ)|=(2633624997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347818103/2500000000 : ℝ)|^2103 ≤ (22096159780823/50000000000000 : ℝ)^1591
        have hw : |(1347818103/2500000000 : ℝ)|=(1347818103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s8_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312661573/10000000000 : ℝ)*x 0 + (-2069469949/10000000000 : ℝ)*x 1 + (1347818103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312661573/10000000000 : ℝ)^2103 ≤ (43342584519069/100000000000000 : ℝ)^1591 := by
    have hnat : (5312661573 : ℕ)^2103*100000000000000^1591 ≤ 43342584519069^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312661573 10000000000 43342584519069 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069469949/10000000000 : ℝ)^2103 ≤ (12465095910289/100000000000000 : ℝ)^1591 := by
    have hnat : (2069469949 : ℕ)^2103*100000000000000^1591 ≤ 12465095910289^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069469949 10000000000 12465095910289 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347818103/2500000000 : ℝ)^2103 ≤ (22096159780823/50000000000000 : ℝ)^1591 := by
    have hnat : (1347818103 : ℕ)^2103*50000000000000^1591 ≤ 22096159780823^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347818103 2500000000 22096159780823 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312661573/10000000000 : ℝ), (-2069469949/10000000000 : ℝ), (1347818103/2500000000 : ℝ)] ![(43342584519069/100000000000000 : ℝ), (12465095910289/100000000000000 : ℝ), (22096159780823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312661573/10000000000 : ℝ)|^2103 ≤ (43342584519069/100000000000000 : ℝ)^1591
        have hw : |(5312661573/10000000000 : ℝ)|=(5312661573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069469949/10000000000 : ℝ)|^2103 ≤ (12465095910289/100000000000000 : ℝ)^1591
        have hw : |(-2069469949/10000000000 : ℝ)|=(2069469949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347818103/2500000000 : ℝ)|^2103 ≤ (22096159780823/50000000000000 : ℝ)^1591
        have hw : |(1347818103/2500000000 : ℝ)|=(1347818103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s8_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312661619/10000000000 : ℝ)*x 0 + (5391272381/10000000000 : ℝ)*x 1 + (-2069469927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312661619/10000000000 : ℝ)^2103 ≤ (10835646253781/25000000000000 : ℝ)^1591 := by
    have hnat : (5312661619 : ℕ)^2103*25000000000000^1591 ≤ 10835646253781^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312661619 10000000000 10835646253781 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391272381/10000000000 : ℝ)^2103 ≤ (8838463845153/20000000000000 : ℝ)^1591 := by
    have hnat : (5391272381 : ℕ)^2103*20000000000000^1591 ≤ 8838463845153^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391272381 10000000000 8838463845153 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069469927/10000000000 : ℝ)^2103 ≤ (3116273933783/25000000000000 : ℝ)^1591 := by
    have hnat : (2069469927 : ℕ)^2103*25000000000000^1591 ≤ 3116273933783^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069469927 10000000000 3116273933783 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312661619/10000000000 : ℝ), (5391272381/10000000000 : ℝ), (-2069469927/10000000000 : ℝ)] ![(10835646253781/25000000000000 : ℝ), (8838463845153/20000000000000 : ℝ), (3116273933783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312661619/10000000000 : ℝ)|^2103 ≤ (10835646253781/25000000000000 : ℝ)^1591
        have hw : |(5312661619/10000000000 : ℝ)|=(5312661619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391272381/10000000000 : ℝ)|^2103 ≤ (8838463845153/20000000000000 : ℝ)^1591
        have hw : |(5391272381/10000000000 : ℝ)|=(5391272381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069469927/10000000000 : ℝ)|^2103 ≤ (3116273933783/25000000000000 : ℝ)^1591
        have hw : |(-2069469927/10000000000 : ℝ)|=(2069469927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s8_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2176974273/5000000000 : ℝ)*x 0 + (56011929/125000000 : ℝ)*x 1 + (528810371/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176974273/5000000000 : ℝ)^2103 ≤ (8329372169787/25000000000000 : ℝ)^1591 := by
    have hnat : (2176974273 : ℕ)^2103*25000000000000^1591 ≤ 8329372169787^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176974273 5000000000 8329372169787 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56011929/125000000 : ℝ)^2103 ≤ (34608119288151/100000000000000 : ℝ)^1591 := by
    have hnat : (56011929 : ℕ)^2103*100000000000000^1591 ≤ 34608119288151^1591*125000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56011929 125000000 34608119288151 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528810371/1250000000 : ℝ)^2103 ≤ (32074392018293/100000000000000 : ℝ)^1591 := by
    have hnat : (528810371 : ℕ)^2103*100000000000000^1591 ≤ 32074392018293^1591*1250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528810371 1250000000 32074392018293 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176974273/5000000000 : ℝ), (56011929/125000000 : ℝ), (528810371/1250000000 : ℝ)] ![(8329372169787/25000000000000 : ℝ), (34608119288151/100000000000000 : ℝ), (32074392018293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176974273/5000000000 : ℝ)|^2103 ≤ (8329372169787/25000000000000 : ℝ)^1591
        have hw : |(2176974273/5000000000 : ℝ)|=(2176974273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56011929/125000000 : ℝ)|^2103 ≤ (34608119288151/100000000000000 : ℝ)^1591
        have hw : |(56011929/125000000 : ℝ)|=(56011929/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528810371/1250000000 : ℝ)|^2103 ≤ (32074392018293/100000000000000 : ℝ)^1591
        have hw : |(528810371/1250000000 : ℝ)|=(528810371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (229/2000 : ℝ) ^ (8411/2048 : ℝ) ≤ (681626771366569/5000000000000000000 : ℝ) := by
    have hpowers : (229/2000 : ℝ)^8411 ≤ (681626771366569/5000000000000000000 : ℝ)^2048 := by
      have hnat : (229 : ℕ)^8411*5000000000000000000^2048 ≤ 681626771366569^2048*2000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        229 2000 681626771366569 5000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (229/2000 : ℝ)) (X := (681626771366569/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (7997489843732973/25000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^8411 ≤ (7997489843732973/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14093 : ℕ)^8411*25000000000000000000^2048 ≤ 7997489843732973^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 7997489843732973 25000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (7997489843732973/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500681626771366569/2500000000000000000 : ℝ) ≤ (10000663810572929/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (2500681626771366569/2500000000000000000 : ℝ)^2048 ≤ (10000663810572929/10000000000000000 : ℝ)^8411 := by
      have hnat : (2500681626771366569 : ℕ)^2048*10000000000000000^8411 ≤ 10000663810572929^8411*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500681626771366569 2500000000000000000 10000663810572929 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000663810572929/10000000000000000 : ℝ)) (X := (2500681626771366569/2500000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505702811850282909/12500000000000000000 : ℝ) ≤ (10001110673518947/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (12505702811850282909/12500000000000000000 : ℝ)^2048 ≤ (10001110673518947/10000000000000000 : ℝ)^8411 := by
      have hnat : (12505702811850282909 : ℕ)^2048*10000000000000000^8411 ≤ 10001110673518947^8411*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505702811850282909 12500000000000000000 10001110673518947 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001110673518947/10000000000000000 : ℝ)) (X := (12505702811850282909/12500000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507997489843732973/12500000000000000000 : ℝ) ≤ (2000311507292993/2000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (12507997489843732973/12500000000000000000 : ℝ)^2048 ≤ (2000311507292993/2000000000000000 : ℝ)^8411 := by
      have hnat : (12507997489843732973 : ℕ)^2048*2000000000000000^8411 ≤ 2000311507292993^8411*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507997489843732973 12500000000000000000 2000311507292993 2000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000311507292993/2000000000000000 : ℝ)) (X := (12507997489843732973/12500000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(681626771366569/5000000000000000000 : ℝ) ≤ ((26421521289880439147/26430000000000000000 : ℝ)+2*(223431473009/132150000000000 : ℝ)*(229/2000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (26421521289880439147/26430000000000000000 : ℝ)+2*(223431473009/132150000000000 : ℝ)*(229/2000 : ℝ)=(10000663810572929/10000000000000000 : ℝ) by norm_num, show 1+2*(681626771366569/5000000000000000000 : ℝ)=(2500681626771366569/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7997489843732973/25000000000000000000 : ℝ)+(681626771366569/5000000000000000000 : ℝ) ≤ ((26421521289880439147/26430000000000000000 : ℝ)+(223431473009/132150000000000 : ℝ)*((14093/100000 : ℝ)+(229/2000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (26421521289880439147/26430000000000000000 : ℝ)+(223431473009/132150000000000 : ℝ)*((14093/100000 : ℝ)+(229/2000 : ℝ))=(10001110673518947/10000000000000000 : ℝ) by norm_num, show 1+(7997489843732973/25000000000000000000 : ℝ)+(681626771366569/5000000000000000000 : ℝ)=(12505702811850282909/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7997489843732973/25000000000000000000 : ℝ) ≤ ((26421521289880439147/26430000000000000000 : ℝ)+2*(223431473009/132150000000000 : ℝ)*(14093/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (26421521289880439147/26430000000000000000 : ℝ)+2*(223431473009/132150000000000 : ℝ)*(14093/100000 : ℝ)=(2000311507292993/2000000000000000 : ℝ) by norm_num, show 1+2*(7997489843732973/25000000000000000000 : ℝ)=(12507997489843732973/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26421521289880439147/26430000000000000000 : ℝ)*(X 1 0+X 2 0)+(223431473009/132150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (26421521289880439147/26430000000000000000 : ℝ)) (alpha := (223431473009/132150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26421521289880439147/26430000000000000000 : ℝ)*(X 0 1+X 2 1)+(223431473009/132150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (26421521289880439147/26430000000000000000 : ℝ)) (alpha := (223431473009/132150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26421521289880439147/26430000000000000000 : ℝ)*(X 0 2+X 1 2)+(223431473009/132150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (26421521289880439147/26430000000000000000 : ℝ)) (alpha := (223431473009/132150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1065300191/5000000000 : ℝ)*X 0 0+(5391587457/10000000000 : ℝ)*X 0 1+(5266935781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344416999/10000000000 : ℝ)*X 1 0+(-2193806041/10000000000 : ℝ)*X 1 1+(2633468177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((16701303/31250000 : ℝ)*X 2 0+(1053387231/2000000000 : ℝ)*X 2 1+(-1096903179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217696969/500000000 : ℝ)*X 0 0+(2114923307/5000000000 : ℝ)*X 0 1+(896317611/2000000000 : ℝ)*X 0 2+(217696969/500000000 : ℝ)*X 1 0+(2114923307/5000000000 : ℝ)*X 1 1+(896317611/2000000000 : ℝ)*X 1 2+(217696969/500000000 : ℝ)*X 2 0+(2114923307/5000000000 : ℝ)*X 2 1+(896317611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16645349/78125000 : ℝ)*X 0 0+(2633624997/5000000000 : ℝ)*X 0 1+(1347818103/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312661573/10000000000 : ℝ)*X 1 0+(-2069469949/10000000000 : ℝ)*X 1 1+(1347818103/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312661619/10000000000 : ℝ)*X 2 0+(5391272381/10000000000 : ℝ)*X 2 1+(-2069469927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176974273/5000000000 : ℝ)*X 0 0+(56011929/125000000 : ℝ)*X 0 1+(528810371/1250000000 : ℝ)*X 0 2+(2176974273/5000000000 : ℝ)*X 1 0+(56011929/125000000 : ℝ)*X 1 1+(528810371/1250000000 : ℝ)*X 1 2+(2176974273/5000000000 : ℝ)*X 2 0+(56011929/125000000 : ℝ)*X 2 1+(528810371/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24714413758015112427129/4405000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114394229/6250000000000 : ℝ)*(base19) + (1577157971/100000000000000 : ℝ)*(base23) + (30814263/100000000000000 : ℝ)*(upper2) + (668928507/100000000000000 : ℝ)*(upper3) + (26964061/20000000000000 : ℝ)*(upper4) + (2998719283531817/50000000000000 : ℝ)*(major0) + (2998719283531817/50000000000000 : ℝ)*(major1) + (2998719283531817/50000000000000 : ℝ)*(major2) + (8022438852700851/100000000000000 : ℝ)*(sp0) + (2005622466840413/25000000000000 : ℝ)*(sp1) + (1604498024102269/20000000000000 : ℝ)*(sp2) + (993087562236657/25000000000000 : ℝ)*(sp3) + (10568993693/20000000000000 : ℝ)*(sp4) + (8750123357/25000000000000 : ℝ)*(sp7) + (496548156180007/12500000000000 : ℝ)*(f.failure) + (8022491697669317/100000000000000 : ℝ)*(f.sum) + (15035101903361/6607500000000000000000000000 : ℝ)*base65 + (3921838323997980033/440500000000000000000000000000000 : ℝ)*base67 + (1879682520035019967/440500000000000000000000000000000 : ℝ)*base70 + (1546571407585519967/440500000000000000000000000000000 : ℝ)*base72 + (4163792010389/1651875000000000000000000000 : ℝ)*base73 + (763863877486480033/440500000000000000000000000000000 : ℝ)*base75 + (3800707053108480033/440500000000000000000000000000000 : ℝ)*base77 + (942124510201019967/440500000000000000000000000000000 : ℝ)*base80 + (21255676165301/6607500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3372103/1250000000000000000000 : ℝ)*base90 + (3372103/1250000000000000000000 : ℝ)*base92 + (3372103/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (258470592870135750484099427/27531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (791130737/50000000000000 : ℝ)*(base19) + (896790551/50000000000000 : ℝ)*(base23) + (558767959/100000000000000 : ℝ)*(lower1) + (85226629/50000000000000 : ℝ)*(upper3) + (30297153/50000000000000 : ℝ)*(lower4) + (185274237/100000000000000 : ℝ)*(upper5) + (753466466329759/12500000000000 : ℝ)*(major0) + (753466466329759/12500000000000 : ℝ)*(major1) + (753466466329759/12500000000000 : ℝ)*(major2) + (4592237809/100000000000000 : ℝ)*(sp2) + (4031506656927757/50000000000000 : ℝ)*(sp4) + (201575293289851/2500000000000 : ℝ)*(sp5) + (8063006928036603/100000000000000 : ℝ)*(sp6) + (3992449834478547/100000000000000 : ℝ)*(sp7) + (3992449834478547/100000000000000 : ℝ)*(f.failure) + (4031506656927757/50000000000000 : ℝ)*(f.sum) + (10137341587157/6607500000000000000000000000 : ℝ)*base66 + (1633383395079125191/110125000000000000000000000000000 : ℝ)*base67 + (627717124714374809/110125000000000000000000000000000 : ℝ)*base70 + (541303765265875191/110125000000000000000000000000000 : ℝ)*base71 + (13056080963137/1651875000000000000000000000 : ℝ)*base73 + (6348333288876625191/110125000000000000000000000000000 : ℝ)*base75 + (517708825798750191/110125000000000000000000000000000 : ℝ)*base77 + (19206470756375191/110125000000000000000000000000000 : ℝ)*base79 + (105266673388699/13215000000000000000000000000 : ℝ)*base82 + (12652237/10000000000000000000000 : ℝ)*base89 + (12652237/10000000000000000000000 : ℝ)*base91 + (12652237/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1219_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1219_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1219_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1219_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1219_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1219_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
