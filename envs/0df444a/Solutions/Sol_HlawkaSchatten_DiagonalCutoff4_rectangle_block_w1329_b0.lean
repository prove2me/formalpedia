-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1329_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:46.188003+00:00
-- url     : https://prove2.me/submissions/89bf1a75-682e-4f66-b0a3-f2dc3948fcff

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
theorem support_rectangle_w1329_s0_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-56776763/312500000 : ℝ)*x 0 + (93789851/156250000 : ℝ)*x 1 + (4807797843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56776763/312500000 : ℝ)^4289 ≤ (5320981825379/50000000000000 : ℝ)^3265 := by
    have hnat : (56776763 : ℕ)^4289*50000000000000^3265 ≤ 5320981825379^3265*312500000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56776763 312500000 5320981825379 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93789851/156250000 : ℝ)^4289 ≤ (25573220296827/50000000000000 : ℝ)^3265 := by
    have hnat : (93789851 : ℕ)^4289*50000000000000^3265 ≤ 25573220296827^3265*156250000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93789851 156250000 25573220296827 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4807797843/10000000000 : ℝ)^4289 ≤ (38211595733631/100000000000000 : ℝ)^3265 := by
    have hnat : (4807797843 : ℕ)^4289*100000000000000^3265 ≤ 38211595733631^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4807797843 10000000000 38211595733631 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56776763/312500000 : ℝ), (93789851/156250000 : ℝ), (4807797843/10000000000 : ℝ)] ![(5320981825379/50000000000000 : ℝ), (25573220296827/50000000000000 : ℝ), (38211595733631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56776763/312500000 : ℝ)|^4289 ≤ (5320981825379/50000000000000 : ℝ)^3265
        have hw : |(-56776763/312500000 : ℝ)|=(56776763/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93789851/156250000 : ℝ)|^4289 ≤ (25573220296827/50000000000000 : ℝ)^3265
        have hw : |(93789851/156250000 : ℝ)|=(93789851/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4807797843/10000000000 : ℝ)|^4289 ≤ (38211595733631/100000000000000 : ℝ)^3265
        have hw : |(4807797843/10000000000 : ℝ)|=(4807797843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s0_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5503269109/10000000000 : ℝ)*x 0 + (-2496592479/10000000000 : ℝ)*x 1 + (2403899077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5503269109/10000000000 : ℝ)^4289 ≤ (22816120162493/50000000000000 : ℝ)^3265 := by
    have hnat : (5503269109 : ℕ)^4289*50000000000000^3265 ≤ 22816120162493^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503269109 10000000000 22816120162493 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2496592479/10000000000 : ℝ)^4289 ≤ (2019520084833/12500000000000 : ℝ)^3265 := by
    have hnat : (2496592479 : ℕ)^4289*12500000000000^3265 ≤ 2019520084833^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496592479 10000000000 2019520084833 12500000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2403899077/5000000000 : ℝ)^4289 ≤ (3821159898063/10000000000000 : ℝ)^3265 := by
    have hnat : (2403899077 : ℕ)^4289*10000000000000^3265 ≤ 3821159898063^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403899077 5000000000 3821159898063 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5503269109/10000000000 : ℝ), (-2496592479/10000000000 : ℝ), (2403899077/5000000000 : ℝ)] ![(22816120162493/50000000000000 : ℝ), (2019520084833/12500000000000 : ℝ), (3821159898063/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5503269109/10000000000 : ℝ)|^4289 ≤ (22816120162493/50000000000000 : ℝ)^3265
        have hw : |(5503269109/10000000000 : ℝ)|=(5503269109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2496592479/10000000000 : ℝ)|^4289 ≤ (2019520084833/12500000000000 : ℝ)^3265
        have hw : |(-2496592479/10000000000 : ℝ)|=(2496592479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2403899077/5000000000 : ℝ)|^4289 ≤ (3821159898063/10000000000000 : ℝ)^3265
        have hw : |(2403899077/5000000000 : ℝ)|=(2403899077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s0_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5503268549/10000000000 : ℝ)*x 0 + (480779829/1000000000 : ℝ)*x 1 + (-249659303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5503268549/10000000000 : ℝ)^4289 ≤ (22816117112619/50000000000000 : ℝ)^3265 := by
    have hnat : (5503268549 : ℕ)^4289*50000000000000^3265 ≤ 22816117112619^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503268549 10000000000 22816117112619 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480779829/1000000000 : ℝ)^4289 ≤ (1910580020027/5000000000000 : ℝ)^3265 := by
    have hnat : (480779829 : ℕ)^4289*5000000000000^3265 ≤ 1910580020027^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480779829 1000000000 1910580020027 5000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249659303/1000000000 : ℝ)^4289 ≤ (16156165362643/100000000000000 : ℝ)^3265 := by
    have hnat : (249659303 : ℕ)^4289*100000000000000^3265 ≤ 16156165362643^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249659303 1000000000 16156165362643 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5503268549/10000000000 : ℝ), (480779829/1000000000 : ℝ), (-249659303/1000000000 : ℝ)] ![(22816117112619/50000000000000 : ℝ), (1910580020027/5000000000000 : ℝ), (16156165362643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5503268549/10000000000 : ℝ)|^4289 ≤ (22816117112619/50000000000000 : ℝ)^3265
        have hw : |(5503268549/10000000000 : ℝ)|=(5503268549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(480779829/1000000000 : ℝ)|^4289 ≤ (1910580020027/5000000000000 : ℝ)^3265
        have hw : |(480779829/1000000000 : ℝ)|=(480779829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249659303/1000000000 : ℝ)|^4289 ≤ (16156165362643/100000000000000 : ℝ)^3265
        have hw : |(-249659303/1000000000 : ℝ)|=(249659303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s0_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180699359/10000000000 : ℝ)*x 0 + (310723607/1000000000 : ℝ)*x 1 + (5597496053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180699359/10000000000 : ℝ)^4289 ≤ (1272100606709/4000000000000 : ℝ)^3265 := by
    have hnat : (4180699359 : ℕ)^4289*4000000000000^3265 ≤ 1272100606709^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180699359 10000000000 1272100606709 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310723607/1000000000 : ℝ)^4289 ≤ (10768070571729/50000000000000 : ℝ)^3265 := by
    have hnat : (310723607 : ℕ)^4289*50000000000000^3265 ≤ 10768070571729^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310723607 1000000000 10768070571729 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5597496053/10000000000 : ℝ)^4289 ≤ (23330671839991/50000000000000 : ℝ)^3265 := by
    have hnat : (5597496053 : ℕ)^4289*50000000000000^3265 ≤ 23330671839991^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597496053 10000000000 23330671839991 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180699359/10000000000 : ℝ), (310723607/1000000000 : ℝ), (5597496053/10000000000 : ℝ)] ![(1272100606709/4000000000000 : ℝ), (10768070571729/50000000000000 : ℝ), (23330671839991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180699359/10000000000 : ℝ)|^4289 ≤ (1272100606709/4000000000000 : ℝ)^3265
        have hw : |(4180699359/10000000000 : ℝ)|=(4180699359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(310723607/1000000000 : ℝ)|^4289 ≤ (10768070571729/50000000000000 : ℝ)^3265
        have hw : |(310723607/1000000000 : ℝ)|=(310723607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5597496053/10000000000 : ℝ)|^4289 ≤ (23330671839991/50000000000000 : ℝ)^3265
        have hw : |(5597496053/10000000000 : ℝ)|=(5597496053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s0_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-910690859/5000000000 : ℝ)*x 0 + (604821379/1250000000 : ℝ)*x 1 + (5970679169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910690859/5000000000 : ℝ)^4289 ≤ (106767966677/1000000000000 : ℝ)^3265 := by
    have hnat : (910690859 : ℕ)^4289*1000000000000^3265 ≤ 106767966677^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910690859 5000000000 106767966677 1000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604821379/1250000000 : ℝ)^4289 ≤ (308265644997/800000000000 : ℝ)^3265 := by
    have hnat : (604821379 : ℕ)^4289*800000000000^3265 ≤ 308265644997^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604821379 1250000000 308265644997 800000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5970679169/10000000000 : ℝ)^4289 ≤ (406319981541/800000000000 : ℝ)^3265 := by
    have hnat : (5970679169 : ℕ)^4289*800000000000^3265 ≤ 406319981541^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5970679169 10000000000 406319981541 800000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-910690859/5000000000 : ℝ), (604821379/1250000000 : ℝ), (5970679169/10000000000 : ℝ)] ![(106767966677/1000000000000 : ℝ), (308265644997/800000000000 : ℝ), (406319981541/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-910690859/5000000000 : ℝ)|^4289 ≤ (106767966677/1000000000000 : ℝ)^3265
        have hw : |(-910690859/5000000000 : ℝ)|=(910690859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604821379/1250000000 : ℝ)|^4289 ≤ (308265644997/800000000000 : ℝ)^3265
        have hw : |(604821379/1250000000 : ℝ)|=(604821379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5970679169/10000000000 : ℝ)|^4289 ≤ (406319981541/800000000000 : ℝ)^3265
        have hw : |(5970679169/10000000000 : ℝ)|=(5970679169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s0_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1294436367/2500000000 : ℝ)*x 0 + (-1333712827/10000000000 : ℝ)*x 1 + (1492669581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294436367/2500000000 : ℝ)^4289 ≤ (42119849895471/100000000000000 : ℝ)^3265 := by
    have hnat : (1294436367 : ℕ)^4289*100000000000000^3265 ≤ 42119849895471^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294436367 2500000000 42119849895471 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1333712827/10000000000 : ℝ)^4289 ≤ (7090161840231/100000000000000 : ℝ)^3265 := by
    have hnat : (1333712827 : ℕ)^4289*100000000000000^3265 ≤ 7090161840231^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333712827 10000000000 7090161840231 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1492669581/2500000000 : ℝ)^4289 ≤ (5078998825019/10000000000000 : ℝ)^3265 := by
    have hnat : (1492669581 : ℕ)^4289*10000000000000^3265 ≤ 5078998825019^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492669581 2500000000 5078998825019 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294436367/2500000000 : ℝ), (-1333712827/10000000000 : ℝ), (1492669581/2500000000 : ℝ)] ![(42119849895471/100000000000000 : ℝ), (7090161840231/100000000000000 : ℝ), (5078998825019/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294436367/2500000000 : ℝ)|^4289 ≤ (42119849895471/100000000000000 : ℝ)^3265
        have hw : |(1294436367/2500000000 : ℝ)|=(1294436367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1333712827/10000000000 : ℝ)|^4289 ≤ (7090161840231/100000000000000 : ℝ)^3265
        have hw : |(-1333712827/10000000000 : ℝ)|=(1333712827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1492669581/2500000000 : ℝ)|^4289 ≤ (5078998825019/10000000000000 : ℝ)^3265
        have hw : |(1492669581/2500000000 : ℝ)|=(1492669581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s0_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64721823/125000000 : ℝ)*x 0 + (2985339321/5000000000 : ℝ)*x 1 + (-1333711749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64721823/125000000 : ℝ)^4289 ≤ (21059926935349/50000000000000 : ℝ)^3265 := by
    have hnat : (64721823 : ℕ)^4289*50000000000000^3265 ≤ 21059926935349^3265*125000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64721823 125000000 21059926935349 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2985339321/5000000000 : ℝ)^4289 ≤ (25394995901837/50000000000000 : ℝ)^3265 := by
    have hnat : (2985339321 : ℕ)^4289*50000000000000^3265 ≤ 25394995901837^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985339321 5000000000 25394995901837 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1333711749/10000000000 : ℝ)^4289 ≤ (7090154312131/100000000000000 : ℝ)^3265 := by
    have hnat : (1333711749 : ℕ)^4289*100000000000000^3265 ≤ 7090154312131^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333711749 10000000000 7090154312131 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64721823/125000000 : ℝ), (2985339321/5000000000 : ℝ), (-1333711749/10000000000 : ℝ)] ![(21059926935349/50000000000000 : ℝ), (25394995901837/50000000000000 : ℝ), (7090154312131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64721823/125000000 : ℝ)|^4289 ≤ (21059926935349/50000000000000 : ℝ)^3265
        have hw : |(64721823/125000000 : ℝ)|=(64721823/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2985339321/5000000000 : ℝ)|^4289 ≤ (25394995901837/50000000000000 : ℝ)^3265
        have hw : |(2985339321/5000000000 : ℝ)|=(2985339321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1333711749/10000000000 : ℝ)|^4289 ≤ (7090154312131/100000000000000 : ℝ)^3265
        have hw : |(-1333711749/10000000000 : ℝ)|=(1333711749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s0_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838026053/2000000000 : ℝ)*x 0 + (5533354983/10000000000 : ℝ)*x 1 + (793416429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838026053/2000000000 : ℝ)^4289 ≤ (3189678925379/10000000000000 : ℝ)^3265 := by
    have hnat : (838026053 : ℕ)^4289*10000000000000^3265 ≤ 3189678925379^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838026053 2000000000 3189678925379 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5533354983/10000000000 : ℝ)^4289 ≤ (11490057132707/25000000000000 : ℝ)^3265 := by
    have hnat : (5533354983 : ℕ)^4289*25000000000000^3265 ≤ 11490057132707^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5533354983 10000000000 11490057132707 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793416429/2500000000 : ℝ)^4289 ≤ (22142982204781/100000000000000 : ℝ)^3265 := by
    have hnat : (793416429 : ℕ)^4289*100000000000000^3265 ≤ 22142982204781^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793416429 2500000000 22142982204781 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838026053/2000000000 : ℝ), (5533354983/10000000000 : ℝ), (793416429/2500000000 : ℝ)] ![(3189678925379/10000000000000 : ℝ), (11490057132707/25000000000000 : ℝ), (22142982204781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838026053/2000000000 : ℝ)|^4289 ≤ (3189678925379/10000000000000 : ℝ)^3265
        have hw : |(838026053/2000000000 : ℝ)|=(838026053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5533354983/10000000000 : ℝ)|^4289 ≤ (11490057132707/25000000000000 : ℝ)^3265
        have hw : |(5533354983/10000000000 : ℝ)|=(5533354983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(793416429/2500000000 : ℝ)|^4289 ≤ (22142982204781/100000000000000 : ℝ)^3265
        have hw : |(793416429/2500000000 : ℝ)|=(793416429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (329/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5393/20000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (67/16 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^67 ≤ (0 : ℝ)^16 := by
      have hnat : (0 : ℕ)^67*1^16 ≤ 0^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (67/16 : ℝ) ≤ (215588809188311019/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^67 ≤ (215588809188311019/10000000000000000000 : ℝ)^16 := by
      have hnat : (2 : ℕ)^67*10000000000000000000^16 ≤ 215588809188311019^16*5^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 215588809188311019 10000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (215588809188311019/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (1 : ℝ)^16 ≤ (1 : ℝ)^67 := by
      have hnat : (1 : ℕ)^16*1^67 ≤ 1^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (10215588809188311019/10000000000000000000 : ℝ) ≤ (10051066724993883/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (10215588809188311019/10000000000000000000 : ℝ)^16 ≤ (10051066724993883/10000000000000000 : ℝ)^67 := by
      have hnat : (10215588809188311019 : ℕ)^16*10000000000000000^67 ≤ 10051066724993883^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10215588809188311019 10000000000000000000 10051066724993883 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10051066724993883/10000000000000000 : ℝ)) (X := (10215588809188311019/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (5215588809188311019/5000000000000000000 : ℝ) ≤ (5051066724993883/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (5215588809188311019/5000000000000000000 : ℝ)^16 ≤ (5051066724993883/5000000000000000 : ℝ)^67 := by
      have hnat : (5215588809188311019 : ℕ)^16*5000000000000000^67 ≤ 5051066724993883^67*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5215588809188311019 5000000000000000000 5051066724993883 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051066724993883/5000000000000000 : ℝ)) (X := (5215588809188311019/5000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(51066724993883/4000000000000000 : ℝ)*(0 : ℝ))^(67/16 : ℝ) := by
    rw [show (1 : ℝ)+2*(51066724993883/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(215588809188311019/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(51066724993883/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(67/16 : ℝ) := by
    rw [show (1 : ℝ)+(51066724993883/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10051066724993883/10000000000000000 : ℝ) by norm_num, show 1+(215588809188311019/10000000000000000000 : ℝ)+(0 : ℝ)=(10215588809188311019/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(215588809188311019/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(51066724993883/4000000000000000 : ℝ)*(2/5 : ℝ))^(67/16 : ℝ) := by
    rw [show (1 : ℝ)+2*(51066724993883/4000000000000000 : ℝ)*(2/5 : ℝ)=(5051066724993883/5000000000000000 : ℝ) by norm_num, show 1+2*(215588809188311019/10000000000000000000 : ℝ)=(5215588809188311019/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(51066724993883/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51066724993883/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(51066724993883/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51066724993883/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(51066724993883/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51066724993883/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-56776763/312500000 : ℝ)*X 0 0+(93789851/156250000 : ℝ)*X 0 1+(4807797843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5503269109/10000000000 : ℝ)*X 1 0+(-2496592479/10000000000 : ℝ)*X 1 1+(2403899077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5503268549/10000000000 : ℝ)*X 2 0+(480779829/1000000000 : ℝ)*X 2 1+(-249659303/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4180699359/10000000000 : ℝ)*X 0 0+(310723607/1000000000 : ℝ)*X 0 1+(5597496053/10000000000 : ℝ)*X 0 2+(4180699359/10000000000 : ℝ)*X 1 0+(310723607/1000000000 : ℝ)*X 1 1+(5597496053/10000000000 : ℝ)*X 1 2+(4180699359/10000000000 : ℝ)*X 2 0+(310723607/1000000000 : ℝ)*X 2 1+(5597496053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-910690859/5000000000 : ℝ)*X 0 0+(604821379/1250000000 : ℝ)*X 0 1+(5970679169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1294436367/2500000000 : ℝ)*X 1 0+(-1333712827/10000000000 : ℝ)*X 1 1+(1492669581/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((64721823/125000000 : ℝ)*X 2 0+(2985339321/5000000000 : ℝ)*X 2 1+(-1333711749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838026053/2000000000 : ℝ)*X 0 0+(5533354983/10000000000 : ℝ)*X 0 1+(793416429/2500000000 : ℝ)*X 0 2+(838026053/2000000000 : ℝ)*X 1 0+(5533354983/10000000000 : ℝ)*X 1 1+(793416429/2500000000 : ℝ)*X 1 2+(838026053/2000000000 : ℝ)*X 2 0+(5533354983/10000000000 : ℝ)*X 2 1+(793416429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (306186976921910453076063/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91864107/100000000000000 : ℝ)*(base1) + (756568887/50000000000000 : ℝ)*(base19) + (356991601/25000000000000 : ℝ)*(base23) + (60827667/25000000000000 : ℝ)*(upper3) + (1191779/1562500000000 : ℝ)*(upper5) + (309643118437487/50000000000000 : ℝ)*(major0) + (309643118437487/50000000000000 : ℝ)*(major1) + (309643118437487/50000000000000 : ℝ)*(major2) + (836998745791039/100000000000000 : ℝ)*(sp0) + (837001648604253/100000000000000 : ℝ)*(sp1) + (104625216721953/12500000000000 : ℝ)*(sp2) + (401566490725279/100000000000000 : ℝ)*(sp3) + (901563019/20000000000000 : ℝ)*(sp4) + (1262646939/50000000000000 : ℝ)*(sp7) + (1568629327669/390625000000 : ℝ)*(f.failure) + (209250790435507/25000000000000 : ℝ)*(f.sum) + (31387846807979/100000000000000000000000000000 : ℝ)*base66 + (648139044892021/200000000000000000000000000000 : ℝ)*base67 + (67894480507979/200000000000000000000000000000 : ℝ)*base70 + (126302288707979/200000000000000000000000000000 : ℝ)*base72 + (306055151192021/100000000000000000000000000000 : ℝ)*base73 + (692752713492021/200000000000000000000000000000 : ℝ)*base75 + (942528088507979/200000000000000000000000000000 : ℝ)*base78 + (318873519907979/200000000000000000000000000000 : ℝ)*base80 + (36716378607979/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (369657/39062500000000000000 : ℝ)*base89 + (369657/39062500000000000000 : ℝ)*base91 + (369657/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268489295099085016770663/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1409766329/100000000000000 : ℝ)*(base19) + (309432411/20000000000000 : ℝ)*(base23) + (5078221/20000000000000 : ℝ)*(base39) + (10118281/6250000000000 : ℝ)*(upper3) + (163825009/100000000000000 : ℝ)*(upper5) + (326773171585331/50000000000000 : ℝ)*(major0) + (326773171585331/50000000000000 : ℝ)*(major1) + (653546317779557/100000000000000 : ℝ)*(major2) + (2850751149/100000000000000 : ℝ)*(sp1) + (3632834031/100000000000000 : ℝ)*(sp2) + (883307798299997/100000000000000 : ℝ)*(sp4) + (441651768891259/50000000000000 : ℝ)*(sp5) + (883302643695017/100000000000000 : ℝ)*(sp6) + (8475693673147/2000000000000 : ℝ)*(sp7) + (8475693673147/2000000000000 : ℝ)*(f.failure) + (441653911845551/50000000000000 : ℝ)*(f.sum) + (742778580910377/400000000000000000000000000000 : ℝ)*base65 + (2858330185849831/400000000000000000000000000000 : ℝ)*base67 + (336694631069727/200000000000000000000000000000 : ℝ)*base70 + (2222402001449831/400000000000000000000000000000 : ℝ)*base71 + (1666512425310377/400000000000000000000000000000 : ℝ)*base73 + (1418574111930273/200000000000000000000000000000 : ℝ)*base75 + (192153222269727/200000000000000000000000000000 : ℝ)*base78 + (628561403269727/200000000000000000000000000000 : ℝ)*base80 + (89215006169727/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1340359/200000000000000000000 : ℝ)*base90 + (1340359/200000000000000000000 : ℝ)*base92 + (1340359/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1329_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (329/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5393/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1329_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-250443587/1250000000 : ℝ)*x 0 + (1129603737/2000000000 : ℝ)*x 1 + (252139119/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250443587/1250000000 : ℝ)^4289 ≤ (6050535690657/50000000000000 : ℝ)^3265 := by
    have hnat : (250443587 : ℕ)^4289*50000000000000^3265 ≤ 6050535690657^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250443587 1250000000 6050535690657 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129603737/2000000000 : ℝ)^4289 ≤ (1888615048921/4000000000000 : ℝ)^3265 := by
    have hnat : (1129603737 : ℕ)^4289*4000000000000^3265 ≤ 1888615048921^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129603737 2000000000 1888615048921 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252139119/500000000 : ℝ)^4289 ≤ (40683552391387/100000000000000 : ℝ)^3265 := by
    have hnat : (252139119 : ℕ)^4289*100000000000000^3265 ≤ 40683552391387^3265*500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252139119 500000000 40683552391387 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250443587/1250000000 : ℝ), (1129603737/2000000000 : ℝ), (252139119/500000000 : ℝ)] ![(6050535690657/50000000000000 : ℝ), (1888615048921/4000000000000 : ℝ), (40683552391387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250443587/1250000000 : ℝ)|^4289 ≤ (6050535690657/50000000000000 : ℝ)^3265
        have hw : |(-250443587/1250000000 : ℝ)|=(250443587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129603737/2000000000 : ℝ)|^4289 ≤ (1888615048921/4000000000000 : ℝ)^3265
        have hw : |(1129603737/2000000000 : ℝ)|=(1129603737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252139119/500000000 : ℝ)|^4289 ≤ (40683552391387/100000000000000 : ℝ)^3265
        have hw : |(252139119/500000000 : ℝ)|=(252139119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s1_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081415581/2000000000 : ℝ)*x 0 + (-2326879531/10000000000 : ℝ)*x 1 + (1260695577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081415581/2000000000 : ℝ)^4289 ≤ (22293684947641/50000000000000 : ℝ)^3265 := by
    have hnat : (1081415581 : ℕ)^4289*50000000000000^3265 ≤ 22293684947641^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081415581 2000000000 22293684947641 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2326879531/10000000000 : ℝ)^4289 ≤ (14729078454543/100000000000000 : ℝ)^3265 := by
    have hnat : (2326879531 : ℕ)^4289*100000000000000^3265 ≤ 14729078454543^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2326879531 10000000000 14729078454543 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260695577/2500000000 : ℝ)^4289 ≤ (8136710325667/20000000000000 : ℝ)^3265 := by
    have hnat : (1260695577 : ℕ)^4289*20000000000000^3265 ≤ 8136710325667^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260695577 2500000000 8136710325667 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081415581/2000000000 : ℝ), (-2326879531/10000000000 : ℝ), (1260695577/2500000000 : ℝ)] ![(22293684947641/50000000000000 : ℝ), (14729078454543/100000000000000 : ℝ), (8136710325667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081415581/2000000000 : ℝ)|^4289 ≤ (22293684947641/50000000000000 : ℝ)^3265
        have hw : |(1081415581/2000000000 : ℝ)|=(1081415581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2326879531/10000000000 : ℝ)|^4289 ≤ (14729078454543/100000000000000 : ℝ)^3265
        have hw : |(-2326879531/10000000000 : ℝ)|=(2326879531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1260695577/2500000000 : ℝ)|^4289 ≤ (8136710325667/20000000000000 : ℝ)^3265
        have hw : |(1260695577/2500000000 : ℝ)|=(1260695577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407078083/10000000000 : ℝ)*x 0 + (1008556393/2000000000 : ℝ)*x 1 + (-290859967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407078083/10000000000 : ℝ)^4289 ≤ (22293685911719/50000000000000 : ℝ)^3265 := by
    have hnat : (5407078083 : ℕ)^4289*50000000000000^3265 ≤ 22293685911719^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407078083 10000000000 22293685911719 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008556393/2000000000 : ℝ)^4289 ≤ (40683547993241/100000000000000 : ℝ)^3265 := by
    have hnat : (1008556393 : ℕ)^4289*100000000000000^3265 ≤ 40683547993241^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008556393 2000000000 40683547993241 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290859967/1250000000 : ℝ)^4289 ≤ (7364540079583/50000000000000 : ℝ)^3265 := by
    have hnat : (290859967 : ℕ)^4289*50000000000000^3265 ≤ 7364540079583^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290859967 1250000000 7364540079583 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407078083/10000000000 : ℝ), (1008556393/2000000000 : ℝ), (-290859967/1250000000 : ℝ)] ![(22293685911719/50000000000000 : ℝ), (40683547993241/100000000000000 : ℝ), (7364540079583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407078083/10000000000 : ℝ)|^4289 ≤ (22293685911719/50000000000000 : ℝ)^3265
        have hw : |(5407078083/10000000000 : ℝ)|=(5407078083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008556393/2000000000 : ℝ)|^4289 ≤ (40683547993241/100000000000000 : ℝ)^3265
        have hw : |(1008556393/2000000000 : ℝ)|=(1008556393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-290859967/1250000000 : ℝ)|^4289 ≤ (7364540079583/50000000000000 : ℝ)^3265
        have hw : |(-290859967/1250000000 : ℝ)|=(290859967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s1_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073654603/2500000000 : ℝ)*x 0 + (3707032233/10000000000 : ℝ)*x 1 + (496854631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073654603/2500000000 : ℝ)^4289 ≤ (1317828600829/4000000000000 : ℝ)^3265 := by
    have hnat : (1073654603 : ℕ)^4289*4000000000000^3265 ≤ 1317828600829^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073654603 2500000000 1317828600829 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3707032233/10000000000 : ℝ)^4289 ≤ (13577829849437/50000000000000 : ℝ)^3265 := by
    have hnat : (3707032233 : ℕ)^4289*50000000000000^3265 ≤ 13577829849437^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707032233 10000000000 13577829849437 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496854631/1000000000 : ℝ)^4289 ≤ (7979725053549/20000000000000 : ℝ)^3265 := by
    have hnat : (496854631 : ℕ)^4289*20000000000000^3265 ≤ 7979725053549^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496854631 1000000000 7979725053549 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073654603/2500000000 : ℝ), (3707032233/10000000000 : ℝ), (496854631/1000000000 : ℝ)] ![(1317828600829/4000000000000 : ℝ), (13577829849437/50000000000000 : ℝ), (7979725053549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073654603/2500000000 : ℝ)|^4289 ≤ (1317828600829/4000000000000 : ℝ)^3265
        have hw : |(1073654603/2500000000 : ℝ)|=(1073654603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3707032233/10000000000 : ℝ)|^4289 ≤ (13577829849437/50000000000000 : ℝ)^3265
        have hw : |(3707032233/10000000000 : ℝ)|=(3707032233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(496854631/1000000000 : ℝ)|^4289 ≤ (7979725053549/20000000000000 : ℝ)^3265
        have hw : |(496854631/1000000000 : ℝ)|=(496854631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s1_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2004109751/10000000000 : ℝ)*x 0 + (5050452281/10000000000 : ℝ)*x 1 + (1410051953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004109751/10000000000 : ℝ)^4289 ≤ (6052761517071/50000000000000 : ℝ)^3265 := by
    have hnat : (2004109751 : ℕ)^4289*50000000000000^3265 ≤ 6052761517071^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004109751 10000000000 6052761517071 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5050452281/10000000000 : ℝ)^4289 ≤ (1630594277239/4000000000000 : ℝ)^3265 := by
    have hnat : (5050452281 : ℕ)^4289*4000000000000^3265 ≤ 1630594277239^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050452281 10000000000 1630594277239 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1410051953/2500000000 : ℝ)^4289 ≤ (9425924004013/20000000000000 : ℝ)^3265 := by
    have hnat : (1410051953 : ℕ)^4289*20000000000000^3265 ≤ 9425924004013^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410051953 2500000000 9425924004013 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2004109751/10000000000 : ℝ), (5050452281/10000000000 : ℝ), (1410051953/2500000000 : ℝ)] ![(6052761517071/50000000000000 : ℝ), (1630594277239/4000000000000 : ℝ), (9425924004013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2004109751/10000000000 : ℝ)|^4289 ≤ (6052761517071/50000000000000 : ℝ)^3265
        have hw : |(-2004109751/10000000000 : ℝ)|=(2004109751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5050452281/10000000000 : ℝ)|^4289 ≤ (1630594277239/4000000000000 : ℝ)^3265
        have hw : |(5050452281/10000000000 : ℝ)|=(5050452281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1410051953/2500000000 : ℝ)|^4289 ≤ (9425924004013/20000000000000 : ℝ)^3265
        have hw : |(1410051953/2500000000 : ℝ)|=(1410051953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s1_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250199871/10000000000 : ℝ)*x 0 + (-1729454219/10000000000 : ℝ)*x 1 + (5640207299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250199871/10000000000 : ℝ)^4289 ≤ (8579159606533/20000000000000 : ℝ)^3265 := by
    have hnat : (5250199871 : ℕ)^4289*20000000000000^3265 ≤ 8579159606533^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250199871 10000000000 8579159606533 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1729454219/10000000000 : ℝ)^4289 ≤ (4987293778921/50000000000000 : ℝ)^3265 := by
    have hnat : (1729454219 : ℕ)^4289*50000000000000^3265 ≤ 4987293778921^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729454219 10000000000 4987293778921 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5640207299/10000000000 : ℝ)^4289 ≤ (47129614389019/100000000000000 : ℝ)^3265 := by
    have hnat : (5640207299 : ℕ)^4289*100000000000000^3265 ≤ 47129614389019^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5640207299 10000000000 47129614389019 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250199871/10000000000 : ℝ), (-1729454219/10000000000 : ℝ), (5640207299/10000000000 : ℝ)] ![(8579159606533/20000000000000 : ℝ), (4987293778921/50000000000000 : ℝ), (47129614389019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250199871/10000000000 : ℝ)|^4289 ≤ (8579159606533/20000000000000 : ℝ)^3265
        have hw : |(5250199871/10000000000 : ℝ)|=(5250199871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1729454219/10000000000 : ℝ)|^4289 ≤ (4987293778921/50000000000000 : ℝ)^3265
        have hw : |(-1729454219/10000000000 : ℝ)|=(1729454219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5640207299/10000000000 : ℝ)|^4289 ≤ (47129614389019/100000000000000 : ℝ)^3265
        have hw : |(5640207299/10000000000 : ℝ)|=(5640207299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250199513/10000000000 : ℝ)*x 0 + (2820103563/5000000000 : ℝ)*x 1 + (-864727489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250199513/10000000000 : ℝ)^4289 ≤ (21447897095167/50000000000000 : ℝ)^3265 := by
    have hnat : (5250199513 : ℕ)^4289*50000000000000^3265 ≤ 21447897095167^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250199513 10000000000 21447897095167 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2820103563/5000000000 : ℝ)^4289 ≤ (47129612490051/100000000000000 : ℝ)^3265 := by
    have hnat : (2820103563 : ℕ)^4289*100000000000000^3265 ≤ 47129612490051^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820103563 5000000000 47129612490051 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864727489/5000000000 : ℝ)^4289 ≤ (398983732331/4000000000000 : ℝ)^3265 := by
    have hnat : (864727489 : ℕ)^4289*4000000000000^3265 ≤ 398983732331^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864727489 5000000000 398983732331 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250199513/10000000000 : ℝ), (2820103563/5000000000 : ℝ), (-864727489/5000000000 : ℝ)] ![(21447897095167/50000000000000 : ℝ), (47129612490051/100000000000000 : ℝ), (398983732331/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250199513/10000000000 : ℝ)|^4289 ≤ (21447897095167/50000000000000 : ℝ)^3265
        have hw : |(5250199513/10000000000 : ℝ)|=(5250199513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2820103563/5000000000 : ℝ)|^4289 ≤ (47129612490051/100000000000000 : ℝ)^3265
        have hw : |(2820103563/5000000000 : ℝ)|=(2820103563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864727489/5000000000 : ℝ)|^4289 ≤ (398983732331/4000000000000 : ℝ)^3265
        have hw : |(-864727489/5000000000 : ℝ)|=(864727489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073946739/2500000000 : ℝ)*x 0 + (990511733/2000000000 : ℝ)*x 1 + (465414281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073946739/2500000000 : ℝ)^4289 ≤ (32957491373727/100000000000000 : ℝ)^3265 := by
    have hnat : (1073946739 : ℕ)^4289*100000000000000^3265 ≤ 32957491373727^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073946739 2500000000 32957491373727 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990511733/2000000000 : ℝ)^4289 ≤ (3973006058493/10000000000000 : ℝ)^3265 := by
    have hnat : (990511733 : ℕ)^4289*10000000000000^3265 ≤ 3973006058493^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990511733 2000000000 3973006058493 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465414281/1250000000 : ℝ)^4289 ≤ (5462489605379/20000000000000 : ℝ)^3265 := by
    have hnat : (465414281 : ℕ)^4289*20000000000000^3265 ≤ 5462489605379^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465414281 1250000000 5462489605379 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073946739/2500000000 : ℝ), (990511733/2000000000 : ℝ), (465414281/1250000000 : ℝ)] ![(32957491373727/100000000000000 : ℝ), (3973006058493/10000000000000 : ℝ), (5462489605379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073946739/2500000000 : ℝ)|^4289 ≤ (32957491373727/100000000000000 : ℝ)^3265
        have hw : |(1073946739/2500000000 : ℝ)|=(1073946739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(990511733/2000000000 : ℝ)|^4289 ≤ (3973006058493/10000000000000 : ℝ)^3265
        have hw : |(990511733/2000000000 : ℝ)|=(990511733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(465414281/1250000000 : ℝ)|^4289 ≤ (5462489605379/20000000000000 : ℝ)^3265
        have hw : |(465414281/1250000000 : ℝ)|=(465414281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5393/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (423/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (489/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5393/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (329/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5393/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (329/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5393/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (329/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5393/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (329/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5393/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (329/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5393/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (329/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (329/25000 : ℝ) ^ (67/16 : ℝ) ≤ (332907856929/25000000000000000000 : ℝ) := by
    have hpowers : (329/25000 : ℝ)^67 ≤ (332907856929/25000000000000000000 : ℝ)^16 := by
      have hnat : (329 : ℕ)^67*25000000000000000000^16 ≤ 332907856929^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        329 25000 332907856929 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (329/25000 : ℝ)) (X := (332907856929/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (5393/20000 : ℝ) ^ (67/16 : ℝ) ≤ (206750601847248923/50000000000000000000 : ℝ) := by
    have hpowers : (5393/20000 : ℝ)^67 ≤ (206750601847248923/50000000000000000000 : ℝ)^16 := by
      have hnat : (5393 : ℕ)^67*50000000000000000000^16 ≤ 206750601847248923^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5393 20000 206750601847248923 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5393/20000 : ℝ)) (X := (206750601847248923/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000332907856929/12500000000000000000 : ℝ) ≤ (10000000063600307/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (12500000332907856929/12500000000000000000 : ℝ)^16 ≤ (10000000063600307/10000000000000000 : ℝ)^67 := by
      have hnat : (12500000332907856929 : ℕ)^16*10000000000000000^67 ≤ 10000000063600307^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000332907856929 12500000000000000000 10000000063600307 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000063600307/10000000000000000 : ℝ)) (X := (12500000332907856929/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50206751267662962781/50000000000000000000 : ℝ) ≤ (10009859184459749/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50206751267662962781/50000000000000000000 : ℝ)^16 ≤ (10009859184459749/10000000000000000 : ℝ)^67 := by
      have hnat : (50206751267662962781 : ℕ)^16*10000000000000000^67 ≤ 10009859184459749^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50206751267662962781 50000000000000000000 10009859184459749 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009859184459749/10000000000000000 : ℝ)) (X := (50206751267662962781/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (25206750601847248923/25000000000000000000 : ℝ) ≤ (10019718305319191/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25206750601847248923/25000000000000000000 : ℝ)^16 ≤ (10019718305319191/10000000000000000 : ℝ)^67 := by
      have hnat : (25206750601847248923 : ℕ)^16*10000000000000000^67 ≤ 10019718305319191^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25206750601847248923 25000000000000000000 10019718305319191 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019718305319191/10000000000000000 : ℝ)) (X := (25206750601847248923/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(332907856929/25000000000000000000 : ℝ) ≤ ((256464052425182222899/256490000000000000000 : ℝ)+2*(4929560429721/1282450000000000 : ℝ)*(329/25000 : ℝ))^(67/16 : ℝ) := by
    rw [show (256464052425182222899/256490000000000000000 : ℝ)+2*(4929560429721/1282450000000000 : ℝ)*(329/25000 : ℝ)=(10000000063600307/10000000000000000 : ℝ) by norm_num, show 1+2*(332907856929/25000000000000000000 : ℝ)=(12500000332907856929/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(206750601847248923/50000000000000000000 : ℝ)+(332907856929/25000000000000000000 : ℝ) ≤ ((256464052425182222899/256490000000000000000 : ℝ)+(4929560429721/1282450000000000 : ℝ)*((5393/20000 : ℝ)+(329/25000 : ℝ)))^(67/16 : ℝ) := by
    rw [show (256464052425182222899/256490000000000000000 : ℝ)+(4929560429721/1282450000000000 : ℝ)*((5393/20000 : ℝ)+(329/25000 : ℝ))=(10009859184459749/10000000000000000 : ℝ) by norm_num, show 1+(206750601847248923/50000000000000000000 : ℝ)+(332907856929/25000000000000000000 : ℝ)=(50206751267662962781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(206750601847248923/50000000000000000000 : ℝ) ≤ ((256464052425182222899/256490000000000000000 : ℝ)+2*(4929560429721/1282450000000000 : ℝ)*(5393/20000 : ℝ))^(67/16 : ℝ) := by
    rw [show (256464052425182222899/256490000000000000000 : ℝ)+2*(4929560429721/1282450000000000 : ℝ)*(5393/20000 : ℝ)=(10019718305319191/10000000000000000 : ℝ) by norm_num, show 1+2*(206750601847248923/50000000000000000000 : ℝ)=(25206750601847248923/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (256464052425182222899/256490000000000000000 : ℝ)*(X 1 0+X 2 0)+(4929560429721/1282450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (329/25000 : ℝ)) (hi := (5393/20000 : ℝ)) (c := (256464052425182222899/256490000000000000000 : ℝ)) (alpha := (4929560429721/1282450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (256464052425182222899/256490000000000000000 : ℝ)*(X 0 1+X 2 1)+(4929560429721/1282450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (329/25000 : ℝ)) (hi := (5393/20000 : ℝ)) (c := (256464052425182222899/256490000000000000000 : ℝ)) (alpha := (4929560429721/1282450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (256464052425182222899/256490000000000000000 : ℝ)*(X 0 2+X 1 2)+(4929560429721/1282450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (329/25000 : ℝ)) (hi := (5393/20000 : ℝ)) (c := (256464052425182222899/256490000000000000000 : ℝ)) (alpha := (4929560429721/1282450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-250443587/1250000000 : ℝ)*X 0 0+(1129603737/2000000000 : ℝ)*X 0 1+(252139119/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1081415581/2000000000 : ℝ)*X 1 0+(-2326879531/10000000000 : ℝ)*X 1 1+(1260695577/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5407078083/10000000000 : ℝ)*X 2 0+(1008556393/2000000000 : ℝ)*X 2 1+(-290859967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073654603/2500000000 : ℝ)*X 0 0+(3707032233/10000000000 : ℝ)*X 0 1+(496854631/1000000000 : ℝ)*X 0 2+(1073654603/2500000000 : ℝ)*X 1 0+(3707032233/10000000000 : ℝ)*X 1 1+(496854631/1000000000 : ℝ)*X 1 2+(1073654603/2500000000 : ℝ)*X 2 0+(3707032233/10000000000 : ℝ)*X 2 1+(496854631/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2004109751/10000000000 : ℝ)*X 0 0+(5050452281/10000000000 : ℝ)*X 0 1+(1410051953/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250199871/10000000000 : ℝ)*X 1 0+(-1729454219/10000000000 : ℝ)*X 1 1+(5640207299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5250199513/10000000000 : ℝ)*X 2 0+(2820103563/5000000000 : ℝ)*X 2 1+(-864727489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1073946739/2500000000 : ℝ)*X 0 0+(990511733/2000000000 : ℝ)*X 0 1+(465414281/1250000000 : ℝ)*X 0 2+(1073946739/2500000000 : ℝ)*X 1 0+(990511733/2000000000 : ℝ)*X 1 1+(465414281/1250000000 : ℝ)*X 1 2+(1073946739/2500000000 : ℝ)*X 2 0+(990511733/2000000000 : ℝ)*X 2 1+(465414281/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32687122234764187257178592067/6412250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75876471/100000000000000 : ℝ)*(base1) + (710283647/100000000000000 : ℝ)*(base19) + (23896109/3125000000000 : ℝ)*(base23) + (28366377/20000000000000 : ℝ)*(upper3) + (18026643/25000000000000 : ℝ)*(upper5) + (1222477408348789/100000000000000 : ℝ)*(major0) + (1222477408348789/100000000000000 : ℝ)*(major1) + (1222477408348789/100000000000000 : ℝ)*(major2) + (25816413886273/1562500000000 : ℝ)*(sp0) + (1652252382596333/100000000000000 : ℝ)*(sp1) + (413063082051123/25000000000000 : ℝ)*(sp2) + (396349823930423/50000000000000 : ℝ)*(sp3) + (2680034979/100000000000000 : ℝ)*(sp4) + (366032017/20000000000000 : ℝ)*(sp7) + (792701553897403/100000000000000 : ℝ)*(f.failure) + (82612654643999/5000000000000 : ℝ)*(f.sum) + (234549115895343/128245000000000000000000000000 : ℝ)*base65 + (75966415076470519311/25649000000000000000000000000000000 : ℝ)*base67 + (224232727307156519311/25649000000000000000000000000000000 : ℝ)*base69 + (40324741269835519311/25649000000000000000000000000000000 : ℝ)*base71 + (39134318439919/64122500000000000000000000000 : ℝ)*base73 + (161655393448012519311/25649000000000000000000000000000000 : ℝ)*base75 + (226612749315156519311/25649000000000000000000000000000000 : ℝ)*base77 + (42597250887818480689/25649000000000000000000000000000000 : ℝ)*base80 + (189307968950439/64122500000000000000000000000 : ℝ)*base81 + (1182009/10000000000000000000000 : ℝ)*base89 + (1182009/10000000000000000000000 : ℝ)*base91 + (1182009/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3713739955270036253207702169/493250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (614574397/50000000000000 : ℝ)*(base19) + (259340653/25000000000000 : ℝ)*(base23) + (7326993/100000000000000 : ℝ)*(upper2) + (567359/625000000000 : ℝ)*(upper3) + (205223291/100000000000000 : ℝ)*(upper5) + (627281493528833/50000000000000 : ℝ)*(major0) + (627281493528833/50000000000000 : ℝ)*(major1) + (627281493528833/50000000000000 : ℝ)*(major2) + (5994404707/100000000000000 : ℝ)*(sp1) + (372290977/12500000000000 : ℝ)*(sp2) + (26494041267551/1562500000000 : ℝ)*(sp4) + (1695611417569763/100000000000000 : ℝ)*(sp5) + (423903656358209/25000000000000 : ℝ)*(sp6) + (50844192626331/6250000000000 : ℝ)*(sp7) + (50844192626331/6250000000000 : ℝ)*(f.failure) + (26494041267551/1562500000000 : ℝ)*(f.sum) + (9676349445059/2466250000000000000000000000 : ℝ)*base66 + (528744487886149759/986500000000000000000000000000000 : ℝ)*base67 + (1301500764038149759/986500000000000000000000000000000 : ℝ)*base69 + (4031786889246149759/986500000000000000000000000000000 : ℝ)*base71 + (29849698211173/4932500000000000000000000000 : ℝ)*base74 + (1796639393625649759/986500000000000000000000000000000 : ℝ)*base75 + (4840256994784149759/986500000000000000000000000000000 : ℝ)*base77 + (772150940878149759/986500000000000000000000000000000 : ℝ)*base79 + (4004377706529/2466250000000000000000000000 : ℝ)*base82 + (2673593/625000000000000000000 : ℝ)*base89 + (2673593/625000000000000000000 : ℝ)*base91 + (2673593/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1329_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5393/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (423/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (489/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1329_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022423759/5000000000 : ℝ)*x 0 + (5483359651/10000000000 : ℝ)*x 1 + (323812927/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022423759/5000000000 : ℝ)^4289 ≤ (12429793895887/100000000000000 : ℝ)^3265 := by
    have hnat : (1022423759 : ℕ)^4289*100000000000000^3265 ≤ 12429793895887^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022423759 5000000000 12429793895887 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483359651/10000000000 : ℝ)^4289 ≤ (45415501516259/100000000000000 : ℝ)^3265 := by
    have hnat : (5483359651 : ℕ)^4289*100000000000000^3265 ≤ 45415501516259^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483359651 10000000000 45415501516259 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323812927/625000000 : ℝ)^4289 ≤ (4215470457871/10000000000000 : ℝ)^3265 := by
    have hnat : (323812927 : ℕ)^4289*10000000000000^3265 ≤ 4215470457871^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323812927 625000000 4215470457871 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022423759/5000000000 : ℝ), (5483359651/10000000000 : ℝ), (323812927/625000000 : ℝ)] ![(12429793895887/100000000000000 : ℝ), (45415501516259/100000000000000 : ℝ), (4215470457871/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022423759/5000000000 : ℝ)|^4289 ≤ (12429793895887/100000000000000 : ℝ)^3265
        have hw : |(-1022423759/5000000000 : ℝ)|=(1022423759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483359651/10000000000 : ℝ)|^4289 ≤ (45415501516259/100000000000000 : ℝ)^3265
        have hw : |(5483359651/10000000000 : ℝ)|=(5483359651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323812927/625000000 : ℝ)|^4289 ≤ (4215470457871/10000000000000 : ℝ)^3265
        have hw : |(323812927/625000000 : ℝ)|=(323812927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s2_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5366875991/10000000000 : ℝ)*x 0 + (-275148709/1250000000 : ℝ)*x 1 + (5181006353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366875991/10000000000 : ℝ)^4289 ≤ (22076198946669/50000000000000 : ℝ)^3265 := by
    have hnat : (5366875991 : ℕ)^4289*50000000000000^3265 ≤ 22076198946669^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366875991 10000000000 22076198946669 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275148709/1250000000 : ℝ)^4289 ≤ (13692902639897/100000000000000 : ℝ)^3265 := by
    have hnat : (275148709 : ℕ)^4289*100000000000000^3265 ≤ 13692902639897^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275148709 1250000000 13692902639897 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181006353/10000000000 : ℝ)^4289 ≤ (2107734972953/5000000000000 : ℝ)^3265 := by
    have hnat : (5181006353 : ℕ)^4289*5000000000000^3265 ≤ 2107734972953^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181006353 10000000000 2107734972953 5000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366875991/10000000000 : ℝ), (-275148709/1250000000 : ℝ), (5181006353/10000000000 : ℝ)] ![(22076198946669/50000000000000 : ℝ), (13692902639897/100000000000000 : ℝ), (2107734972953/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366875991/10000000000 : ℝ)|^4289 ≤ (22076198946669/50000000000000 : ℝ)^3265
        have hw : |(5366875991/10000000000 : ℝ)|=(5366875991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275148709/1250000000 : ℝ)|^4289 ≤ (13692902639897/100000000000000 : ℝ)^3265
        have hw : |(-275148709/1250000000 : ℝ)|=(275148709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181006353/10000000000 : ℝ)|^4289 ≤ (2107734972953/5000000000000 : ℝ)^3265
        have hw : |(5181006353/10000000000 : ℝ)|=(5181006353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s2_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683437687/5000000000 : ℝ)*x 0 + (5181006957/10000000000 : ℝ)*x 1 + (-34393589/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683437687/5000000000 : ℝ)^4289 ≤ (11038097806353/25000000000000 : ℝ)^3265 := by
    have hnat : (2683437687 : ℕ)^4289*25000000000000^3265 ≤ 11038097806353^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683437687 5000000000 11038097806353 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181006957/10000000000 : ℝ)^4289 ≤ (2634669119671/6250000000000 : ℝ)^3265 := by
    have hnat : (5181006957 : ℕ)^4289*6250000000000^3265 ≤ 2634669119671^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181006957 10000000000 2634669119671 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34393589/156250000 : ℝ)^4289 ≤ (13692902836017/100000000000000 : ℝ)^3265 := by
    have hnat : (34393589 : ℕ)^4289*100000000000000^3265 ≤ 13692902836017^3265*156250000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34393589 156250000 13692902836017 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683437687/5000000000 : ℝ), (5181006957/10000000000 : ℝ), (-34393589/156250000 : ℝ)] ![(11038097806353/25000000000000 : ℝ), (2634669119671/6250000000000 : ℝ), (13692902836017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683437687/5000000000 : ℝ)|^4289 ≤ (11038097806353/25000000000000 : ℝ)^3265
        have hw : |(2683437687/5000000000 : ℝ)|=(2683437687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181006957/10000000000 : ℝ)|^4289 ≤ (2634669119671/6250000000000 : ℝ)^3265
        have hw : |(5181006957/10000000000 : ℝ)|=(5181006957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34393589/156250000 : ℝ)|^4289 ≤ (13692902836017/100000000000000 : ℝ)^3265
        have hw : |(-34393589/156250000 : ℝ)|=(34393589/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s2_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323457121/10000000000 : ℝ)*x 0 + (125597247/312500000 : ℝ)*x 1 + (464932501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323457121/10000000000 : ℝ)^4289 ≤ (33236638928769/100000000000000 : ℝ)^3265 := by
    have hnat : (4323457121 : ℕ)^4289*100000000000000^3265 ≤ 33236638928769^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323457121 10000000000 33236638928769 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125597247/312500000 : ℝ)^4289 ≤ (30197685489311/100000000000000 : ℝ)^3265 := by
    have hnat : (125597247 : ℕ)^4289*100000000000000^3265 ≤ 30197685489311^3265*312500000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125597247 312500000 30197685489311 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464932501/1000000000 : ℝ)^4289 ≤ (36565675559327/100000000000000 : ℝ)^3265 := by
    have hnat : (464932501 : ℕ)^4289*100000000000000^3265 ≤ 36565675559327^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464932501 1000000000 36565675559327 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323457121/10000000000 : ℝ), (125597247/312500000 : ℝ), (464932501/1000000000 : ℝ)] ![(33236638928769/100000000000000 : ℝ), (30197685489311/100000000000000 : ℝ), (36565675559327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323457121/10000000000 : ℝ)|^4289 ≤ (33236638928769/100000000000000 : ℝ)^3265
        have hw : |(4323457121/10000000000 : ℝ)|=(4323457121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125597247/312500000 : ℝ)|^4289 ≤ (30197685489311/100000000000000 : ℝ)^3265
        have hw : |(125597247/312500000 : ℝ)|=(125597247/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464932501/1000000000 : ℝ)|^4289 ≤ (36565675559327/100000000000000 : ℝ)^3265
        have hw : |(464932501/1000000000 : ℝ)|=(464932501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s2_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044917057/10000000000 : ℝ)*x 0 + (259146503/500000000 : ℝ)*x 1 + (2740709539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044917057/10000000000 : ℝ)^4289 ≤ (12430349168963/100000000000000 : ℝ)^3265 := by
    have hnat : (2044917057 : ℕ)^4289*100000000000000^3265 ≤ 12430349168963^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044917057 10000000000 12430349168963 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259146503/500000000 : ℝ)^4289 ≤ (42175261628923/100000000000000 : ℝ)^3265 := by
    have hnat : (259146503 : ℕ)^4289*100000000000000^3265 ≤ 42175261628923^3265*500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259146503 500000000 42175261628923 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740709539/5000000000 : ℝ)^4289 ≤ (45394389188333/100000000000000 : ℝ)^3265 := by
    have hnat : (2740709539 : ℕ)^4289*100000000000000^3265 ≤ 45394389188333^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740709539 5000000000 45394389188333 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044917057/10000000000 : ℝ), (259146503/500000000 : ℝ), (2740709539/5000000000 : ℝ)] ![(12430349168963/100000000000000 : ℝ), (42175261628923/100000000000000 : ℝ), (45394389188333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044917057/10000000000 : ℝ)|^4289 ≤ (12430349168963/100000000000000 : ℝ)^3265
        have hw : |(-2044917057/10000000000 : ℝ)|=(2044917057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259146503/500000000 : ℝ)|^4289 ≤ (42175261628923/100000000000000 : ℝ)^3265
        have hw : |(259146503/500000000 : ℝ)|=(259146503/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740709539/5000000000 : ℝ)|^4289 ≤ (45394389188333/100000000000000 : ℝ)^3265
        have hw : |(2740709539/5000000000 : ℝ)|=(2740709539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s2_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289055147/10000000000 : ℝ)*x 0 + (-1900776333/10000000000 : ℝ)*x 1 + (1096283823/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289055147/10000000000 : ℝ)^4289 ≤ (21656652942903/50000000000000 : ℝ)^3265 := by
    have hnat : (5289055147 : ℕ)^4289*50000000000000^3265 ≤ 21656652942903^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289055147 10000000000 21656652942903 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900776333/10000000000 : ℝ)^4289 ≤ (2258460902527/20000000000000 : ℝ)^3265 := by
    have hnat : (1900776333 : ℕ)^4289*20000000000000^3265 ≤ 2258460902527^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900776333 10000000000 2258460902527 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096283823/2000000000 : ℝ)^4289 ≤ (907887791817/2000000000000 : ℝ)^3265 := by
    have hnat : (1096283823 : ℕ)^4289*2000000000000^3265 ≤ 907887791817^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096283823 2000000000 907887791817 2000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289055147/10000000000 : ℝ), (-1900776333/10000000000 : ℝ), (1096283823/2000000000 : ℝ)] ![(21656652942903/50000000000000 : ℝ), (2258460902527/20000000000000 : ℝ), (907887791817/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289055147/10000000000 : ℝ)|^4289 ≤ (21656652942903/50000000000000 : ℝ)^3265
        have hw : |(5289055147/10000000000 : ℝ)|=(5289055147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1900776333/10000000000 : ℝ)|^4289 ≤ (2258460902527/20000000000000 : ℝ)^3265
        have hw : |(-1900776333/10000000000 : ℝ)|=(1900776333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096283823/2000000000 : ℝ)|^4289 ≤ (907887791817/2000000000000 : ℝ)^3265
        have hw : |(1096283823/2000000000 : ℝ)|=(1096283823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s2_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644527603/5000000000 : ℝ)*x 0 + (1096283817/2000000000 : ℝ)*x 1 + (-1900776293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644527603/5000000000 : ℝ)^4289 ≤ (8662661304101/20000000000000 : ℝ)^3265 := by
    have hnat : (2644527603 : ℕ)^4289*20000000000000^3265 ≤ 8662661304101^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644527603 5000000000 8662661304101 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096283817/2000000000 : ℝ)^4289 ≤ (9078877852897/20000000000000 : ℝ)^3265 := by
    have hnat : (1096283817 : ℕ)^4289*20000000000000^3265 ≤ 9078877852897^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096283817 2000000000 9078877852897 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900776293/10000000000 : ℝ)^4289 ≤ (1129230420047/10000000000000 : ℝ)^3265 := by
    have hnat : (1900776293 : ℕ)^4289*10000000000000^3265 ≤ 1129230420047^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900776293 10000000000 1129230420047 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644527603/5000000000 : ℝ), (1096283817/2000000000 : ℝ), (-1900776293/10000000000 : ℝ)] ![(8662661304101/20000000000000 : ℝ), (9078877852897/20000000000000 : ℝ), (1129230420047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644527603/5000000000 : ℝ)|^4289 ≤ (8662661304101/20000000000000 : ℝ)^3265
        have hw : |(2644527603/5000000000 : ℝ)|=(2644527603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096283817/2000000000 : ℝ)|^4289 ≤ (9078877852897/20000000000000 : ℝ)^3265
        have hw : |(1096283817/2000000000 : ℝ)|=(1096283817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1900776293/10000000000 : ℝ)|^4289 ≤ (1129230420047/10000000000000 : ℝ)^3265
        have hw : |(-1900776293/10000000000 : ℝ)|=(1900776293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080900051/2500000000 : ℝ)*x 0 + (4645313843/10000000000 : ℝ)*x 1 + (4023162961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080900051/2500000000 : ℝ)^4289 ≤ (33238083866377/100000000000000 : ℝ)^3265 := by
    have hnat : (1080900051 : ℕ)^4289*100000000000000^3265 ≤ 33238083866377^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080900051 2500000000 33238083866377 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4645313843/10000000000 : ℝ)^4289 ≤ (18262120223153/50000000000000 : ℝ)^3265 := by
    have hnat : (4645313843 : ℕ)^4289*50000000000000^3265 ≤ 18262120223153^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4645313843 10000000000 18262120223153 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023162961/10000000000 : ℝ)^4289 ≤ (7559418918217/25000000000000 : ℝ)^3265 := by
    have hnat : (4023162961 : ℕ)^4289*25000000000000^3265 ≤ 7559418918217^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023162961 10000000000 7559418918217 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080900051/2500000000 : ℝ), (4645313843/10000000000 : ℝ), (4023162961/10000000000 : ℝ)] ![(33238083866377/100000000000000 : ℝ), (18262120223153/50000000000000 : ℝ), (7559418918217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080900051/2500000000 : ℝ)|^4289 ≤ (33238083866377/100000000000000 : ℝ)^3265
        have hw : |(1080900051/2500000000 : ℝ)|=(1080900051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4645313843/10000000000 : ℝ)|^4289 ≤ (18262120223153/50000000000000 : ℝ)^3265
        have hw : |(4645313843/10000000000 : ℝ)|=(4645313843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023162961/10000000000 : ℝ)|^4289 ≤ (7559418918217/25000000000000 : ℝ)^3265
        have hw : |(4023162961/10000000000 : ℝ)|=(4023162961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (489/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1953/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16157/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (489/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (423/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (489/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (423/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (489/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (423/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (489/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (423/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (489/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (423/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (489/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (423/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (423/6250 : ℝ) ^ (67/16 : ℝ) ≤ (1266346970557257/100000000000000000000 : ℝ) := by
    have hpowers : (423/6250 : ℝ)^67 ≤ (1266346970557257/100000000000000000000 : ℝ)^16 := by
      have hnat : (423 : ℕ)^67*100000000000000000000^16 ≤ 1266346970557257^16*6250^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        423 6250 1266346970557257 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (423/6250 : ℝ)) (X := (1266346970557257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (489/2500 : ℝ) ^ (67/16 : ℝ) ≤ (107797095983722697/100000000000000000000 : ℝ) := by
    have hpowers : (489/2500 : ℝ)^67 ≤ (107797095983722697/100000000000000000000 : ℝ)^16 := by
      have hnat : (489 : ℕ)^67*100000000000000000000^16 ≤ 107797095983722697^16*2500^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        489 2500 107797095983722697 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (489/2500 : ℝ)) (X := (107797095983722697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001266346970557257/50000000000000000000 : ℝ) ≤ (10000060481660369/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50001266346970557257/50000000000000000000 : ℝ)^16 ≤ (10000060481660369/10000000000000000 : ℝ)^67 := by
      have hnat : (50001266346970557257 : ℕ)^16*10000000000000000^67 ≤ 10000060481660369^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001266346970557257 50000000000000000000 10000060481660369 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000060481660369/10000000000000000 : ℝ)) (X := (50001266346970557257/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50054531721477139977/50000000000000000000 : ℝ) ≤ (400104136788569/400000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50054531721477139977/50000000000000000000 : ℝ)^16 ≤ (400104136788569/400000000000000 : ℝ)^67 := by
      have hnat : (50054531721477139977 : ℕ)^16*400000000000000^67 ≤ 400104136788569^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054531721477139977 50000000000000000000 400104136788569 400000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400104136788569/400000000000000 : ℝ)) (X := (50054531721477139977/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50107797095983722697/50000000000000000000 : ℝ) ≤ (10005146357768081/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50107797095983722697/50000000000000000000 : ℝ)^16 ≤ (10005146357768081/10000000000000000 : ℝ)^67 := by
      have hnat : (50107797095983722697 : ℕ)^16*10000000000000000^67 ≤ 10005146357768081^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50107797095983722697 50000000000000000000 10005146357768081 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005146357768081/10000000000000000 : ℝ)) (X := (50107797095983722697/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1266346970557257/100000000000000000000 : ℝ) ≤ ((5328598019662601893/5330000000000000000 : ℝ)+2*(26488938061/13325000000000 : ℝ)*(423/6250 : ℝ))^(67/16 : ℝ) := by
    rw [show (5328598019662601893/5330000000000000000 : ℝ)+2*(26488938061/13325000000000 : ℝ)*(423/6250 : ℝ)=(10000060481660369/10000000000000000 : ℝ) by norm_num, show 1+2*(1266346970557257/100000000000000000000 : ℝ)=(50001266346970557257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(107797095983722697/100000000000000000000 : ℝ)+(1266346970557257/100000000000000000000 : ℝ) ≤ ((5328598019662601893/5330000000000000000 : ℝ)+(26488938061/13325000000000 : ℝ)*((489/2500 : ℝ)+(423/6250 : ℝ)))^(67/16 : ℝ) := by
    rw [show (5328598019662601893/5330000000000000000 : ℝ)+(26488938061/13325000000000 : ℝ)*((489/2500 : ℝ)+(423/6250 : ℝ))=(400104136788569/400000000000000 : ℝ) by norm_num, show 1+(107797095983722697/100000000000000000000 : ℝ)+(1266346970557257/100000000000000000000 : ℝ)=(50054531721477139977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(107797095983722697/100000000000000000000 : ℝ) ≤ ((5328598019662601893/5330000000000000000 : ℝ)+2*(26488938061/13325000000000 : ℝ)*(489/2500 : ℝ))^(67/16 : ℝ) := by
    rw [show (5328598019662601893/5330000000000000000 : ℝ)+2*(26488938061/13325000000000 : ℝ)*(489/2500 : ℝ)=(10005146357768081/10000000000000000 : ℝ) by norm_num, show 1+2*(107797095983722697/100000000000000000000 : ℝ)=(50107797095983722697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5328598019662601893/5330000000000000000 : ℝ)*(X 1 0+X 2 0)+(26488938061/13325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (423/6250 : ℝ)) (hi := (489/2500 : ℝ)) (c := (5328598019662601893/5330000000000000000 : ℝ)) (alpha := (26488938061/13325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5328598019662601893/5330000000000000000 : ℝ)*(X 0 1+X 2 1)+(26488938061/13325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (423/6250 : ℝ)) (hi := (489/2500 : ℝ)) (c := (5328598019662601893/5330000000000000000 : ℝ)) (alpha := (26488938061/13325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5328598019662601893/5330000000000000000 : ℝ)*(X 0 2+X 1 2)+(26488938061/13325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (423/6250 : ℝ)) (hi := (489/2500 : ℝ)) (c := (5328598019662601893/5330000000000000000 : ℝ)) (alpha := (26488938061/13325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1022423759/5000000000 : ℝ)*X 0 0+(5483359651/10000000000 : ℝ)*X 0 1+(323812927/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5366875991/10000000000 : ℝ)*X 1 0+(-275148709/1250000000 : ℝ)*X 1 1+(5181006353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683437687/5000000000 : ℝ)*X 2 0+(5181006957/10000000000 : ℝ)*X 2 1+(-34393589/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323457121/10000000000 : ℝ)*X 0 0+(125597247/312500000 : ℝ)*X 0 1+(464932501/1000000000 : ℝ)*X 0 2+(4323457121/10000000000 : ℝ)*X 1 0+(125597247/312500000 : ℝ)*X 1 1+(464932501/1000000000 : ℝ)*X 1 2+(4323457121/10000000000 : ℝ)*X 2 0+(125597247/312500000 : ℝ)*X 2 1+(464932501/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2044917057/10000000000 : ℝ)*X 0 0+(259146503/500000000 : ℝ)*X 0 1+(2740709539/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289055147/10000000000 : ℝ)*X 1 0+(-1900776333/10000000000 : ℝ)*X 1 1+(1096283823/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644527603/5000000000 : ℝ)*X 2 0+(1096283817/2000000000 : ℝ)*X 2 1+(-1900776293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080900051/2500000000 : ℝ)*X 0 0+(4645313843/10000000000 : ℝ)*X 0 1+(4023162961/10000000000 : ℝ)*X 0 2+(1080900051/2500000000 : ℝ)*X 1 0+(4645313843/10000000000 : ℝ)*X 1 1+(4023162961/10000000000 : ℝ)*X 1 2+(1080900051/2500000000 : ℝ)*X 2 0+(4645313843/10000000000 : ℝ)*X 2 1+(4023162961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (460551047468106300773465763/66625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308195013/12500000000000 : ℝ)*(base19) + (695525497/50000000000000 : ℝ)*(base23) + (7452161/2000000000000 : ℝ)*(lower2) + (416133627/50000000000000 : ℝ)*(upper3) + (1314759/800000000000 : ℝ)*(upper5) + (611777464639399/25000000000000 : ℝ)*(major0) + (611777464639399/25000000000000 : ℝ)*(major1) + (611777464639399/25000000000000 : ℝ)*(major2) + (1653706196803171/50000000000000 : ℝ)*(sp0) + (1653708250494089/50000000000000 : ℝ)*(sp1) + (413427196937161/12500000000000 : ℝ)*(sp2) + (99173699078387/6250000000000 : ℝ)*(sp3) + (6572941939/100000000000000 : ℝ)*(sp4) + (21334893173/100000000000000 : ℝ)*(sp7) + (317360104029473/20000000000000 : ℝ)*(f.failure) + (3307418966548281/100000000000000 : ℝ)*(f.sum) + (18138243681501/2665000000000000000000000000 : ℝ)*base66 + (1300892684358867693/133250000000000000000000000000000 : ℝ)*base68 + (438666522061367693/133250000000000000000000000000000 : ℝ)*base70 + (820000700881117693/133250000000000000000000000000000 : ℝ)*base72 + (13153366367591/2665000000000000000000000000 : ℝ)*base74 + (1365347523957367693/133250000000000000000000000000000 : ℝ)*base76 + (885020213471617693/133250000000000000000000000000000 : ℝ)*base78 + (2298180940589367693/133250000000000000000000000000000 : ℝ)*base80 + (17332792416701/2665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17940219/2000000000000000000000 : ℝ)*base89 + (17940219/2000000000000000000000 : ℝ)*base91 + (17940219/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (353168295770510076265150839/33312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1037747863/50000000000000 : ℝ)*(base19) + (2370693959/100000000000000 : ℝ)*(base23) + (267845569/100000000000000 : ℝ)*(upper3) + (12855299/12500000000000 : ℝ)*(lower4) + (177161577/100000000000000 : ℝ)*(upper5) + (619691520679541/25000000000000 : ℝ)*(major0) + (619691520679541/25000000000000 : ℝ)*(major1) + (619691520679541/25000000000000 : ℝ)*(major2) + (22714737999/100000000000000 : ℝ)*(sp1) + (27022737629/100000000000000 : ℝ)*(sp2) + (335020417384327/10000000000000 : ℝ)*(sp4) + (418772422951193/12500000000000 : ℝ)*(sp5) + (1675087390205841/50000000000000 : ℝ)*(sp6) + (1607327638203887/100000000000000 : ℝ)*(sp7) + (1607327638203887/100000000000000 : ℝ)*(f.failure) + (335020417384327/10000000000000 : ℝ)*(f.sum) + (2058118183527/1332500000000000000000000000 : ℝ)*base66 + (1402149269624878887/133250000000000000000000000000000 : ℝ)*base68 + (471122262214378887/133250000000000000000000000000000 : ℝ)*base70 + (1410356667992878887/133250000000000000000000000000000 : ℝ)*base72 + (1572501070549/2665000000000000000000000000 : ℝ)*base74 + (465940221197871113/133250000000000000000000000000000 : ℝ)*base75 + (1121012256146128887/133250000000000000000000000000000 : ℝ)*base78 + (1548023337714628887/133250000000000000000000000000000 : ℝ)*base80 + (6028439941011/2665000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (74535861/10000000000000000000000 : ℝ)*base89 + (74535861/10000000000000000000000 : ℝ)*base91 + (74535861/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1329_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (489/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1953/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16157/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1329_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1953/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16157/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1329_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1329_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1329_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1953/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16157/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1329_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
