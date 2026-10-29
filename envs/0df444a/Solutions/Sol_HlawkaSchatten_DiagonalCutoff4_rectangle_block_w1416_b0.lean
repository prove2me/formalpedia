-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1416_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:09.749129+00:00
-- url     : https://prove2.me/submissions/0928634c-25f7-49c6-b5f9-66ac709e602f

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
theorem support_rectangle_w1416_s0_0 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1766197399/10000000000 : ℝ)*x 0 + (1491391057/2500000000 : ℝ)*x 1 + (4828255173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1766197399/10000000000 : ℝ)^547 ≤ (5199814131673/50000000000000 : ℝ)^419 := by
    have hnat : (1766197399 : ℕ)^547*50000000000000^419 ≤ 5199814131673^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766197399 10000000000 5199814131673 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1491391057/2500000000 : ℝ)^547 ≤ (12736657933323/25000000000000 : ℝ)^419 := by
    have hnat : (1491391057 : ℕ)^547*25000000000000^419 ≤ 12736657933323^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491391057 2500000000 12736657933323 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4828255173/10000000000 : ℝ)^547 ≤ (38653739994929/100000000000000 : ℝ)^419 := by
    have hnat : (4828255173 : ℕ)^547*100000000000000^419 ≤ 38653739994929^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828255173 10000000000 38653739994929 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1766197399/10000000000 : ℝ), (1491391057/2500000000 : ℝ), (4828255173/10000000000 : ℝ)] ![(5199814131673/50000000000000 : ℝ), (12736657933323/25000000000000 : ℝ), (38653739994929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1766197399/10000000000 : ℝ)|^547 ≤ (5199814131673/50000000000000 : ℝ)^419
        have hw : |(-1766197399/10000000000 : ℝ)|=(1766197399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1491391057/2500000000 : ℝ)|^547 ≤ (12736657933323/25000000000000 : ℝ)^419
        have hw : |(1491391057/2500000000 : ℝ)|=(1491391057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4828255173/10000000000 : ℝ)|^547 ≤ (38653739994929/100000000000000 : ℝ)^419
        have hw : |(4828255173/10000000000 : ℝ)|=(4828255173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s0_1 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1098709223/2000000000 : ℝ)*x 0 + (-1204620259/5000000000 : ℝ)*x 1 + (2414127761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098709223/2000000000 : ℝ)^547 ≤ (365991145087/800000000000 : ℝ)^419 := by
    have hnat : (1098709223 : ℕ)^547*800000000000^419 ≤ 365991145087^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098709223 2000000000 365991145087 800000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204620259/5000000000 : ℝ)^547 ≤ (7798681601487/50000000000000 : ℝ)^419 := by
    have hnat : (1204620259 : ℕ)^547*50000000000000^419 ≤ 7798681601487^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204620259 5000000000 7798681601487 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2414127761/5000000000 : ℝ)^547 ≤ (38653743642469/100000000000000 : ℝ)^419 := by
    have hnat : (2414127761 : ℕ)^547*100000000000000^419 ≤ 38653743642469^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414127761 5000000000 38653743642469 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098709223/2000000000 : ℝ), (-1204620259/5000000000 : ℝ), (2414127761/5000000000 : ℝ)] ![(365991145087/800000000000 : ℝ), (7798681601487/50000000000000 : ℝ), (38653743642469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098709223/2000000000 : ℝ)|^547 ≤ (365991145087/800000000000 : ℝ)^419
        have hw : |(1098709223/2000000000 : ℝ)|=(1098709223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1204620259/5000000000 : ℝ)|^547 ≤ (7798681601487/50000000000000 : ℝ)^419
        have hw : |(-1204620259/5000000000 : ℝ)|=(1204620259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2414127761/5000000000 : ℝ)|^547 ≤ (38653743642469/100000000000000 : ℝ)^419
        have hw : |(2414127761/5000000000 : ℝ)|=(2414127761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s0_2 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5493546401/10000000000 : ℝ)*x 0 + (38626043/80000000 : ℝ)*x 1 + (-602310083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5493546401/10000000000 : ℝ)^547 ≤ (45748896245207/100000000000000 : ℝ)^419 := by
    have hnat : (5493546401 : ℕ)^547*100000000000000^419 ≤ 45748896245207^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493546401 10000000000 45748896245207 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38626043/80000000 : ℝ)^547 ≤ (38653742106113/100000000000000 : ℝ)^419 := by
    have hnat : (38626043 : ℕ)^547*100000000000000^419 ≤ 38653742106113^419*80000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38626043 80000000 38653742106113 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602310083/2500000000 : ℝ)^547 ≤ (15597361630957/100000000000000 : ℝ)^419 := by
    have hnat : (602310083 : ℕ)^547*100000000000000^419 ≤ 15597361630957^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602310083 2500000000 15597361630957 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5493546401/10000000000 : ℝ), (38626043/80000000 : ℝ), (-602310083/2500000000 : ℝ)] ![(45748896245207/100000000000000 : ℝ), (38653742106113/100000000000000 : ℝ), (15597361630957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5493546401/10000000000 : ℝ)|^547 ≤ (45748896245207/100000000000000 : ℝ)^419
        have hw : |(5493546401/10000000000 : ℝ)|=(5493546401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38626043/80000000 : ℝ)|^547 ≤ (38653742106113/100000000000000 : ℝ)^419
        have hw : |(38626043/80000000 : ℝ)|=(38626043/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-602310083/2500000000 : ℝ)|^547 ≤ (15597361630957/100000000000000 : ℝ)^419
        have hw : |(-602310083/2500000000 : ℝ)|=(602310083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s0_3 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4167871149/10000000000 : ℝ)*x 0 + (1551850189/5000000000 : ℝ)*x 1 + (1388091651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4167871149/10000000000 : ℝ)^547 ≤ (6380168898411/20000000000000 : ℝ)^419 := by
    have hnat : (4167871149 : ℕ)^547*20000000000000^419 ≤ 6380168898411^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167871149 10000000000 6380168898411 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551850189/5000000000 : ℝ)^547 ≤ (4341946995561/20000000000000 : ℝ)^419 := by
    have hnat : (1551850189 : ℕ)^547*20000000000000^419 ≤ 4341946995561^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551850189 5000000000 4341946995561 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1388091651/2500000000 : ℝ)^547 ≤ (46389420510113/100000000000000 : ℝ)^419 := by
    have hnat : (1388091651 : ℕ)^547*100000000000000^419 ≤ 46389420510113^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388091651 2500000000 46389420510113 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4167871149/10000000000 : ℝ), (1551850189/5000000000 : ℝ), (1388091651/2500000000 : ℝ)] ![(6380168898411/20000000000000 : ℝ), (4341946995561/20000000000000 : ℝ), (46389420510113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4167871149/10000000000 : ℝ)|^547 ≤ (6380168898411/20000000000000 : ℝ)^419
        have hw : |(4167871149/10000000000 : ℝ)|=(4167871149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551850189/5000000000 : ℝ)|^547 ≤ (4341946995561/20000000000000 : ℝ)^419
        have hw : |(1551850189/5000000000 : ℝ)|=(1551850189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1388091651/2500000000 : ℝ)|^547 ≤ (46389420510113/100000000000000 : ℝ)^419
        have hw : |(1388091651/2500000000 : ℝ)|=(1388091651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s0_4 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770277807/10000000000 : ℝ)*x 0 + (1214345713/2500000000 : ℝ)*x 1 + (5935396399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770277807/10000000000 : ℝ)^547 ≤ (10431005060827/100000000000000 : ℝ)^419 := by
    have hnat : (1770277807 : ℕ)^547*100000000000000^419 ≤ 10431005060827^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770277807 10000000000 10431005060827 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214345713/2500000000 : ℝ)^547 ≤ (38958445245751/100000000000000 : ℝ)^419 := by
    have hnat : (1214345713 : ℕ)^547*100000000000000^419 ≤ 38958445245751^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214345713 2500000000 38958445245751 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5935396399/10000000000 : ℝ)^547 ≤ (50610549676329/100000000000000 : ℝ)^419 := by
    have hnat : (5935396399 : ℕ)^547*100000000000000^419 ≤ 50610549676329^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5935396399 10000000000 50610549676329 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770277807/10000000000 : ℝ), (1214345713/2500000000 : ℝ), (5935396399/10000000000 : ℝ)] ![(10431005060827/100000000000000 : ℝ), (38958445245751/100000000000000 : ℝ), (50610549676329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770277807/10000000000 : ℝ)|^547 ≤ (10431005060827/100000000000000 : ℝ)^419
        have hw : |(-1770277807/10000000000 : ℝ)|=(1770277807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214345713/2500000000 : ℝ)|^547 ≤ (38958445245751/100000000000000 : ℝ)^419
        have hw : |(1214345713/2500000000 : ℝ)|=(1214345713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5935396399/10000000000 : ℝ)|^547 ≤ (50610549676329/100000000000000 : ℝ)^419
        have hw : |(5935396399/10000000000 : ℝ)|=(5935396399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s0_5 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5183190147/10000000000 : ℝ)*x 0 + (-651049551/5000000000 : ℝ)*x 1 + (5935396491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183190147/10000000000 : ℝ)^547 ≤ (1696170964483/4000000000000 : ℝ)^419 := by
    have hnat : (5183190147 : ℕ)^547*4000000000000^419 ≤ 1696170964483^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183190147 10000000000 1696170964483 4000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651049551/5000000000 : ℝ)^547 ≤ (6985175177351/100000000000000 : ℝ)^419 := by
    have hnat : (651049551 : ℕ)^547*100000000000000^419 ≤ 6985175177351^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651049551 5000000000 6985175177351 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5935396491/10000000000 : ℝ)^547 ≤ (12652637675113/25000000000000 : ℝ)^419 := by
    have hnat : (5935396491 : ℕ)^547*25000000000000^419 ≤ 12652637675113^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5935396491 10000000000 12652637675113 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183190147/10000000000 : ℝ), (-651049551/5000000000 : ℝ), (5935396491/10000000000 : ℝ)] ![(1696170964483/4000000000000 : ℝ), (6985175177351/100000000000000 : ℝ), (12652637675113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183190147/10000000000 : ℝ)|^547 ≤ (1696170964483/4000000000000 : ℝ)^419
        have hw : |(5183190147/10000000000 : ℝ)|=(5183190147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-651049551/5000000000 : ℝ)|^547 ≤ (6985175177351/100000000000000 : ℝ)^419
        have hw : |(-651049551/5000000000 : ℝ)|=(651049551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5935396491/10000000000 : ℝ)|^547 ≤ (12652637675113/25000000000000 : ℝ)^419
        have hw : |(5935396491/10000000000 : ℝ)|=(5935396491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s0_6 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5183190163/10000000000 : ℝ)*x 0 + (5935396307/10000000000 : ℝ)*x 1 + (-1302099369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183190163/10000000000 : ℝ)^547 ≤ (42404274282961/100000000000000 : ℝ)^419 := by
    have hnat : (5183190163 : ℕ)^547*100000000000000^419 ≤ 42404274282961^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183190163 10000000000 42404274282961 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5935396307/10000000000 : ℝ)^547 ≤ (10122109730441/20000000000000 : ℝ)^419 := by
    have hnat : (5935396307 : ℕ)^547*20000000000000^419 ≤ 10122109730441^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5935396307 10000000000 10122109730441 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302099369/10000000000 : ℝ)^547 ≤ (6985177047249/100000000000000 : ℝ)^419 := by
    have hnat : (1302099369 : ℕ)^547*100000000000000^419 ≤ 6985177047249^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302099369 10000000000 6985177047249 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183190163/10000000000 : ℝ), (5935396307/10000000000 : ℝ), (-1302099369/10000000000 : ℝ)] ![(42404274282961/100000000000000 : ℝ), (10122109730441/20000000000000 : ℝ), (6985177047249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183190163/10000000000 : ℝ)|^547 ≤ (42404274282961/100000000000000 : ℝ)^419
        have hw : |(5183190163/10000000000 : ℝ)|=(5183190163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5935396307/10000000000 : ℝ)|^547 ≤ (10122109730441/20000000000000 : ℝ)^419
        have hw : |(5935396307/10000000000 : ℝ)|=(5935396307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1302099369/10000000000 : ℝ)|^547 ≤ (6985177047249/100000000000000 : ℝ)^419
        have hw : |(-1302099369/10000000000 : ℝ)|=(1302099369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s0_7 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (167066331/400000000 : ℝ)*x 0 + (43917229/80000000 : ℝ)*x 1 + (1584326519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167066331/400000000 : ℝ)^547 ≤ (31988675490341/100000000000000 : ℝ)^419 := by
    have hnat : (167066331 : ℕ)^547*100000000000000^419 ≤ 31988675490341^419*400000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167066331 400000000 31988675490341 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43917229/80000000 : ℝ)^547 ≤ (45706579376479/100000000000000 : ℝ)^419 := by
    have hnat : (43917229 : ℕ)^547*100000000000000^419 ≤ 45706579376479^419*80000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43917229 80000000 45706579376479 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584326519/5000000000 : ℝ)^547 ≤ (22304745117783/100000000000000 : ℝ)^419 := by
    have hnat : (1584326519 : ℕ)^547*100000000000000^419 ≤ 22304745117783^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584326519 5000000000 22304745117783 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167066331/400000000 : ℝ), (43917229/80000000 : ℝ), (1584326519/5000000000 : ℝ)] ![(31988675490341/100000000000000 : ℝ), (45706579376479/100000000000000 : ℝ), (22304745117783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167066331/400000000 : ℝ)|^547 ≤ (31988675490341/100000000000000 : ℝ)^419
        have hw : |(167066331/400000000 : ℝ)|=(167066331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43917229/80000000 : ℝ)|^547 ≤ (45706579376479/100000000000000 : ℝ)^419
        have hw : |(43917229/80000000 : ℝ)|=(43917229/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584326519/5000000000 : ℝ)|^547 ≤ (22304745117783/100000000000000 : ℝ)^419
        have hw : |(1584326519/5000000000 : ℝ)|=(1584326519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1416_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (391/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6587/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4375/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4375 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4375*1^1024 ≤ 0^1024*1^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4375/1024 : ℝ) ≤ (1994421087770780623/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4375 ≤ (1994421087770780623/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4375*100000000000000000000^1024 ≤ 1994421087770780623^1024*5^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1994421087770780623 100000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1994421087770780623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4375 := by
      have hnat : (1 : ℕ)^1024*1^4375 ≤ 1^4375*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101994421087770780623/100000000000000000000 : ℝ) ≤ (5023164213975619/5000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (101994421087770780623/100000000000000000000 : ℝ)^1024 ≤ (5023164213975619/5000000000000000 : ℝ)^4375 := by
      have hnat : (101994421087770780623 : ℕ)^1024*5000000000000000^4375 ≤ 5023164213975619^4375*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101994421087770780623 100000000000000000000 5023164213975619 5000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023164213975619/5000000000000000 : ℝ)) (X := (101994421087770780623/100000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51994421087770780623/50000000000000000000 : ℝ) ≤ (2523164213975619/2500000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (51994421087770780623/50000000000000000000 : ℝ)^1024 ≤ (2523164213975619/2500000000000000 : ℝ)^4375 := by
      have hnat : (51994421087770780623 : ℕ)^1024*2500000000000000^4375 ≤ 2523164213975619^4375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51994421087770780623 50000000000000000000 2523164213975619 2500000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523164213975619/2500000000000000 : ℝ)) (X := (51994421087770780623/50000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(23164213975619/2000000000000000 : ℝ)*(0 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23164213975619/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1994421087770780623/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(23164213975619/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4375/1024 : ℝ) := by
    rw [show (1 : ℝ)+(23164213975619/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5023164213975619/5000000000000000 : ℝ) by norm_num, show 1+(1994421087770780623/100000000000000000000 : ℝ)+(0 : ℝ)=(101994421087770780623/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1994421087770780623/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(23164213975619/2000000000000000 : ℝ)*(2/5 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23164213975619/2000000000000000 : ℝ)*(2/5 : ℝ)=(2523164213975619/2500000000000000 : ℝ) by norm_num, show 1+2*(1994421087770780623/100000000000000000000 : ℝ)=(51994421087770780623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(23164213975619/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23164213975619/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(23164213975619/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23164213975619/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(23164213975619/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23164213975619/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1766197399/10000000000 : ℝ)*X 0 0+(1491391057/2500000000 : ℝ)*X 0 1+(4828255173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1098709223/2000000000 : ℝ)*X 1 0+(-1204620259/5000000000 : ℝ)*X 1 1+(2414127761/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5493546401/10000000000 : ℝ)*X 2 0+(38626043/80000000 : ℝ)*X 2 1+(-602310083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4167871149/10000000000 : ℝ)*X 0 0+(1551850189/5000000000 : ℝ)*X 0 1+(1388091651/2500000000 : ℝ)*X 0 2+(4167871149/10000000000 : ℝ)*X 1 0+(1551850189/5000000000 : ℝ)*X 1 1+(1388091651/2500000000 : ℝ)*X 1 2+(4167871149/10000000000 : ℝ)*X 2 0+(1551850189/5000000000 : ℝ)*X 2 1+(1388091651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1770277807/10000000000 : ℝ)*X 0 0+(1214345713/2500000000 : ℝ)*X 0 1+(5935396399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183190147/10000000000 : ℝ)*X 1 0+(-651049551/5000000000 : ℝ)*X 1 1+(5935396491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183190163/10000000000 : ℝ)*X 2 0+(5935396307/10000000000 : ℝ)*X 2 1+(-1302099369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((167066331/400000000 : ℝ)*X 0 0+(43917229/80000000 : ℝ)*X 0 1+(1584326519/5000000000 : ℝ)*X 0 2+(167066331/400000000 : ℝ)*X 1 0+(43917229/80000000 : ℝ)*X 1 1+(1584326519/5000000000 : ℝ)*X 1 2+(167066331/400000000 : ℝ)*X 2 0+(43917229/80000000 : ℝ)*X 2 1+(1584326519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7936005670364387523/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1311291/25000000000000 : ℝ)*(base1) + (926367353/50000000000000 : ℝ)*(base19) + (1898510969/100000000000000 : ℝ)*(base23) + (41916817/20000000000000 : ℝ)*(upper3) + (273137599/100000000000000 : ℝ)*(upper5) + (643836916175749/100000000000000 : ℝ)*(major0) + (643836916175749/100000000000000 : ℝ)*(major1) + (643836916175749/100000000000000 : ℝ)*(major2) + (439637331108481/50000000000000 : ℝ)*(sp0) + (87927982012067/10000000000000 : ℝ)*(sp1) + (879279774344407/100000000000000 : ℝ)*(sp2) + (408388731085831/100000000000000 : ℝ)*(sp3) + (3507941789/50000000000000 : ℝ)*(sp4) + (1579315801/50000000000000 : ℝ)*(sp7) + (408391894962597/100000000000000 : ℝ)*(f.failure) + (54955104553461/6250000000000 : ℝ)*(f.sum) + (108576896563631/100000000000000000000000000000 : ℝ)*base65 + (890735226936369/200000000000000000000000000000 : ℝ)*base68 + (154681964536369/200000000000000000000000000000 : ℝ)*base70 + (94174321263631/200000000000000000000000000000 : ℝ)*base71 + (93476425736369/100000000000000000000000000000 : ℝ)*base74 + (663593902936369/200000000000000000000000000000 : ℝ)*base76 + (645752110136369/200000000000000000000000000000 : ℝ)*base78 + (87005206463631/200000000000000000000000000000 : ℝ)*base79 + (513685837463631/100000000000000000000000000000 : ℝ)*base81 + (67080989/10000000000000000000000 : ℝ)*base89 + (67080989/10000000000000000000000 : ℝ)*base91 + (67080989/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55113506329170993/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1246950773/100000000000000 : ℝ)*(base19) + (628137761/50000000000000 : ℝ)*(base23) + (160404499/100000000000000 : ℝ)*(base32) + (195221019/100000000000000 : ℝ)*(upper3) + (5875799/6250000000000 : ℝ)*(upper5) + (339620005454089/50000000000000 : ℝ)*(major0) + (339620005454089/50000000000000 : ℝ)*(major1) + (339620005454089/50000000000000 : ℝ)*(major2) + (2891675469/100000000000000 : ℝ)*(sp1) + (2999580783/100000000000000 : ℝ)*(sp2) + (463815711291089/50000000000000 : ℝ)*(sp4) + (28988352623623/3125000000000 : ℝ)*(sp5) + (927627166725873/100000000000000 : ℝ)*(sp6) + (107712063779497/25000000000000 : ℝ)*(sp7) + (430848415522487/100000000000000 : ℝ)*(f.failure) + (463815711291089/50000000000000 : ℝ)*(f.sum) + (42696717156091/50000000000000000000000000000 : ℝ)*base65 + (451073745743909/100000000000000000000000000000 : ℝ)*base68 + (178675613256091/100000000000000000000000000000 : ℝ)*base69 + (118951447156091/100000000000000000000000000000 : ℝ)*base71 + (67196134443909/50000000000000000000000000000 : ℝ)*base74 + (579467723943909/100000000000000000000000000000 : ℝ)*base76 + (239696928343909/100000000000000000000000000000 : ℝ)*base78 + (568473543743909/100000000000000000000000000000 : ℝ)*base80 + (249436397306091/50000000000000000000000000000 : ℝ)*base81 + (38109919/10000000000000000000000 : ℝ)*base89 + (38109919/10000000000000000000000 : ℝ)*base91 + (38109919/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1416_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (391/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6587/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1416_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1416_s1_0 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1940401323/10000000000 : ℝ)*x 0 + (1122095579/2000000000 : ℝ)*x 1 + (2535842197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940401323/10000000000 : ℝ)^547 ≤ (11758450147393/100000000000000 : ℝ)^419 := by
    have hnat : (1940401323 : ℕ)^547*100000000000000^419 ≤ 11758450147393^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940401323 10000000000 11758450147393 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122095579/2000000000 : ℝ)^547 ≤ (47024264030937/100000000000000 : ℝ)^419 := by
    have hnat : (1122095579 : ℕ)^547*100000000000000^419 ≤ 47024264030937^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122095579 2000000000 47024264030937 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2535842197/5000000000 : ℝ)^547 ≤ (41217285815823/100000000000000 : ℝ)^419 := by
    have hnat : (2535842197 : ℕ)^547*100000000000000^419 ≤ 41217285815823^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535842197 5000000000 41217285815823 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1940401323/10000000000 : ℝ), (1122095579/2000000000 : ℝ), (2535842197/5000000000 : ℝ)] ![(11758450147393/100000000000000 : ℝ), (47024264030937/100000000000000 : ℝ), (41217285815823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1940401323/10000000000 : ℝ)|^547 ≤ (11758450147393/100000000000000 : ℝ)^419
        have hw : |(-1940401323/10000000000 : ℝ)|=(1940401323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122095579/2000000000 : ℝ)|^547 ≤ (47024264030937/100000000000000 : ℝ)^419
        have hw : |(1122095579/2000000000 : ℝ)|=(1122095579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2535842197/5000000000 : ℝ)|^547 ≤ (41217285815823/100000000000000 : ℝ)^419
        have hw : |(2535842197/5000000000 : ℝ)|=(2535842197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s1_1 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (42172803/78125000 : ℝ)*x 0 + (-2226189701/10000000000 : ℝ)*x 1 + (40573453/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42172803/78125000 : ℝ)^547 ≤ (44714190935889/100000000000000 : ℝ)^419 := by
    have hnat : (42172803 : ℕ)^547*100000000000000^419 ≤ 44714190935889^419*78125000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42172803 78125000 44714190935889 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226189701/10000000000 : ℝ)^547 ≤ (7034276305951/50000000000000 : ℝ)^419 := by
    have hnat : (2226189701 : ℕ)^547*50000000000000^419 ≤ 7034276305951^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226189701 10000000000 7034276305951 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40573453/80000000 : ℝ)^547 ≤ (2576078527359/6250000000000 : ℝ)^419 := by
    have hnat : (40573453 : ℕ)^547*6250000000000^419 ≤ 2576078527359^419*80000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40573453 80000000 2576078527359 6250000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42172803/78125000 : ℝ), (-2226189701/10000000000 : ℝ), (40573453/80000000 : ℝ)] ![(44714190935889/100000000000000 : ℝ), (7034276305951/50000000000000 : ℝ), (2576078527359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42172803/78125000 : ℝ)|^547 ≤ (44714190935889/100000000000000 : ℝ)^419
        have hw : |(42172803/78125000 : ℝ)|=(42172803/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226189701/10000000000 : ℝ)|^547 ≤ (7034276305951/50000000000000 : ℝ)^419
        have hw : |(-2226189701/10000000000 : ℝ)|=(2226189701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40573453/80000000 : ℝ)|^547 ≤ (2576078527359/6250000000000 : ℝ)^419
        have hw : |(40573453/80000000 : ℝ)|=(40573453/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s1_2 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5398117063/10000000000 : ℝ)*x 0 + (5071684233/10000000000 : ℝ)*x 1 + (-1113094301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398117063/10000000000 : ℝ)^547 ≤ (44714172325429/100000000000000 : ℝ)^419 := by
    have hnat : (5398117063 : ℕ)^547*100000000000000^419 ≤ 44714172325429^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398117063 10000000000 44714172325429 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5071684233/10000000000 : ℝ)^547 ≤ (41217284107671/100000000000000 : ℝ)^419 := by
    have hnat : (5071684233 : ℕ)^547*100000000000000^419 ≤ 41217284107671^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071684233 10000000000 41217284107671 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113094301/5000000000 : ℝ)^547 ≤ (2813708709003/20000000000000 : ℝ)^419 := by
    have hnat : (1113094301 : ℕ)^547*20000000000000^419 ≤ 2813708709003^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113094301 5000000000 2813708709003 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398117063/10000000000 : ℝ), (5071684233/10000000000 : ℝ), (-1113094301/5000000000 : ℝ)] ![(44714172325429/100000000000000 : ℝ), (41217284107671/100000000000000 : ℝ), (2813708709003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398117063/10000000000 : ℝ)|^547 ≤ (44714172325429/100000000000000 : ℝ)^419
        have hw : |(5398117063/10000000000 : ℝ)|=(5398117063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5071684233/10000000000 : ℝ)|^547 ≤ (41217284107671/100000000000000 : ℝ)^419
        have hw : |(5071684233/10000000000 : ℝ)|=(5071684233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113094301/5000000000 : ℝ)|^547 ≤ (2813708709003/20000000000000 : ℝ)^419
        have hw : |(-1113094301/5000000000 : ℝ)|=(1113094301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s1_3 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2139500301/5000000000 : ℝ)*x 0 + (233391237/625000000 : ℝ)*x 1 + (2447154493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139500301/5000000000 : ℝ)^547 ≤ (8253941809647/25000000000000 : ℝ)^419 := by
    have hnat : (2139500301 : ℕ)^547*25000000000000^419 ≤ 8253941809647^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139500301 5000000000 8253941809647 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233391237/625000000 : ℝ)^547 ≤ (6909674911939/25000000000000 : ℝ)^419 := by
    have hnat : (233391237 : ℕ)^547*25000000000000^419 ≤ 6909674911939^419*625000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233391237 625000000 6909674911939 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2447154493/5000000000 : ℝ)^547 ≤ (786910661947/2000000000000 : ℝ)^419 := by
    have hnat : (2447154493 : ℕ)^547*2000000000000^419 ≤ 786910661947^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2447154493 5000000000 786910661947 2000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139500301/5000000000 : ℝ), (233391237/625000000 : ℝ), (2447154493/5000000000 : ℝ)] ![(8253941809647/25000000000000 : ℝ), (6909674911939/25000000000000 : ℝ), (786910661947/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139500301/5000000000 : ℝ)|^547 ≤ (8253941809647/25000000000000 : ℝ)^419
        have hw : |(2139500301/5000000000 : ℝ)|=(2139500301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(233391237/625000000 : ℝ)|^547 ≤ (6909674911939/25000000000000 : ℝ)^419
        have hw : |(233391237/625000000 : ℝ)|=(233391237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2447154493/5000000000 : ℝ)|^547 ≤ (786910661947/2000000000000 : ℝ)^419
        have hw : |(2447154493/5000000000 : ℝ)|=(2447154493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s1_4 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-121301053/625000000 : ℝ)*x 0 + (1269516313/2500000000 : ℝ)*x 1 + (1400997017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121301053/625000000 : ℝ)^547 ≤ (2940434369127/25000000000000 : ℝ)^419 := by
    have hnat : (121301053 : ℕ)^547*25000000000000^419 ≤ 2940434369127^419*625000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121301053 625000000 2940434369127 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269516313/2500000000 : ℝ)^547 ≤ (41284997400921/100000000000000 : ℝ)^419 := by
    have hnat : (1269516313 : ℕ)^547*100000000000000^419 ≤ 41284997400921^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269516313 2500000000 41284997400921 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1400997017/2500000000 : ℝ)^547 ≤ (46953265099199/100000000000000 : ℝ)^419 := by
    have hnat : (1400997017 : ℕ)^547*100000000000000^419 ≤ 46953265099199^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400997017 2500000000 46953265099199 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121301053/625000000 : ℝ), (1269516313/2500000000 : ℝ), (1400997017/2500000000 : ℝ)] ![(2940434369127/25000000000000 : ℝ), (41284997400921/100000000000000 : ℝ), (46953265099199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121301053/625000000 : ℝ)|^547 ≤ (2940434369127/25000000000000 : ℝ)^419
        have hw : |(-121301053/625000000 : ℝ)|=(121301053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269516313/2500000000 : ℝ)|^547 ≤ (41284997400921/100000000000000 : ℝ)^419
        have hw : |(1269516313/2500000000 : ℝ)|=(1269516313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1400997017/2500000000 : ℝ)|^547 ≤ (46953265099199/100000000000000 : ℝ)^419
        have hw : |(1400997017/2500000000 : ℝ)|=(1400997017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s1_5 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5257482129/10000000000 : ℝ)*x 0 + (-169388307/1000000000 : ℝ)*x 1 + (224159523/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257482129/10000000000 : ℝ)^547 ≤ (345595763793/800000000000 : ℝ)^419 := by
    have hnat : (5257482129 : ℕ)^547*800000000000^419 ≤ 345595763793^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257482129 10000000000 345595763793 800000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169388307/1000000000 : ℝ)^547 ≤ (9847264335963/100000000000000 : ℝ)^419 := by
    have hnat : (169388307 : ℕ)^547*100000000000000^419 ≤ 9847264335963^419*1000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169388307 1000000000 9847264335963 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224159523/400000000 : ℝ)^547 ≤ (23476632587883/50000000000000 : ℝ)^419 := by
    have hnat : (224159523 : ℕ)^547*50000000000000^419 ≤ 23476632587883^419*400000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224159523 400000000 23476632587883 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257482129/10000000000 : ℝ), (-169388307/1000000000 : ℝ), (224159523/400000000 : ℝ)] ![(345595763793/800000000000 : ℝ), (9847264335963/100000000000000 : ℝ), (23476632587883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257482129/10000000000 : ℝ)|^547 ≤ (345595763793/800000000000 : ℝ)^419
        have hw : |(5257482129/10000000000 : ℝ)|=(5257482129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169388307/1000000000 : ℝ)|^547 ≤ (9847264335963/100000000000000 : ℝ)^419
        have hw : |(-169388307/1000000000 : ℝ)|=(169388307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224159523/400000000 : ℝ)|^547 ≤ (23476632587883/50000000000000 : ℝ)^419
        have hw : |(224159523/400000000 : ℝ)|=(224159523/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s1_6 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1314370527/2500000000 : ℝ)*x 0 + (2801994021/5000000000 : ℝ)*x 1 + (-423470787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314370527/2500000000 : ℝ)^547 ≤ (2159973512443/5000000000000 : ℝ)^419 := by
    have hnat : (1314370527 : ℕ)^547*5000000000000^419 ≤ 2159973512443^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314370527 2500000000 2159973512443 5000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2801994021/5000000000 : ℝ)^547 ≤ (5869158101851/12500000000000 : ℝ)^419 := by
    have hnat : (2801994021 : ℕ)^547*12500000000000^419 ≤ 5869158101851^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801994021 5000000000 5869158101851 12500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423470787/2500000000 : ℝ)^547 ≤ (4923632463967/50000000000000 : ℝ)^419 := by
    have hnat : (423470787 : ℕ)^547*50000000000000^419 ≤ 4923632463967^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423470787 2500000000 4923632463967 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314370527/2500000000 : ℝ), (2801994021/5000000000 : ℝ), (-423470787/2500000000 : ℝ)] ![(2159973512443/5000000000000 : ℝ), (5869158101851/12500000000000 : ℝ), (4923632463967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314370527/2500000000 : ℝ)|^547 ≤ (2159973512443/5000000000000 : ℝ)^419
        have hw : |(1314370527/2500000000 : ℝ)|=(1314370527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2801994021/5000000000 : ℝ)|^547 ≤ (5869158101851/12500000000000 : ℝ)^419
        have hw : |(2801994021/5000000000 : ℝ)|=(2801994021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423470787/2500000000 : ℝ)|^547 ≤ (4923632463967/50000000000000 : ℝ)^419
        have hw : |(-423470787/2500000000 : ℝ)|=(423470787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s1_7 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (855978939/2000000000 : ℝ)*x 0 + (244028409/500000000 : ℝ)*x 1 + (3748237919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855978939/2000000000 : ℝ)^547 ≤ (33024773590337/100000000000000 : ℝ)^419 := by
    have hnat : (855978939 : ℕ)^547*100000000000000^419 ≤ 33024773590337^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855978939 2000000000 33024773590337 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244028409/500000000 : ℝ)^547 ≤ (19600693454739/50000000000000 : ℝ)^419 := by
    have hnat : (244028409 : ℕ)^547*50000000000000^419 ≤ 19600693454739^419*500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244028409 500000000 19600693454739 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3748237919/10000000000 : ℝ)^547 ≤ (13886919741931/50000000000000 : ℝ)^419 := by
    have hnat : (3748237919 : ℕ)^547*50000000000000^419 ≤ 13886919741931^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3748237919 10000000000 13886919741931 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855978939/2000000000 : ℝ), (244028409/500000000 : ℝ), (3748237919/10000000000 : ℝ)] ![(33024773590337/100000000000000 : ℝ), (19600693454739/50000000000000 : ℝ), (13886919741931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855978939/2000000000 : ℝ)|^547 ≤ (33024773590337/100000000000000 : ℝ)^419
        have hw : |(855978939/2000000000 : ℝ)|=(855978939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244028409/500000000 : ℝ)|^547 ≤ (19600693454739/50000000000000 : ℝ)^419
        have hw : |(244028409/500000000 : ℝ)|=(244028409/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3748237919/10000000000 : ℝ)|^547 ≤ (13886919741931/50000000000000 : ℝ)^419
        have hw : |(3748237919/10000000000 : ℝ)|=(3748237919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1416_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6587/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (391/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (943/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9467/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6587/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (391/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6587/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (391/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6587/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (391/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6587/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (391/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6587/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (391/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6587/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (391/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (391/20000 : ℝ) ^ (4375/1024 : ℝ) ≤ (100004901689/2000000000000000000 : ℝ) := by
    have hpowers : (391/20000 : ℝ)^4375 ≤ (100004901689/2000000000000000000 : ℝ)^1024 := by
      have hnat : (391 : ℕ)^4375*2000000000000000000^1024 ≤ 100004901689^1024*20000^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        391 20000 100004901689 2000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (391/20000 : ℝ)) (X := (100004901689/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6587/25000 : ℝ) ^ (4375/1024 : ℝ) ≤ (67018850981415929/20000000000000000000 : ℝ) := by
    have hpowers : (6587/25000 : ℝ)^4375 ≤ (67018850981415929/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6587 : ℕ)^4375*20000000000000000000^1024 ≤ 67018850981415929^1024*25000^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6587 25000 67018850981415929 20000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6587/25000 : ℝ)) (X := (67018850981415929/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000000100004901689/1000000000000000000 : ℝ) ≤ (10000000234068607/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (1000000100004901689/1000000000000000000 : ℝ)^1024 ≤ (10000000234068607/10000000000000000 : ℝ)^4375 := by
      have hnat : (1000000100004901689 : ℕ)^1024*10000000000000000^4375 ≤ 10000000234068607^4375*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000000100004901689 1000000000000000000 10000000234068607 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000234068607/10000000000000000 : ℝ)) (X := (1000000100004901689/1000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20067019851030432819/20000000000000000000 : ℝ) ≤ (10007833191735861/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (20067019851030432819/20000000000000000000 : ℝ)^1024 ≤ (10007833191735861/10000000000000000 : ℝ)^4375 := by
      have hnat : (20067019851030432819 : ℕ)^1024*10000000000000000^4375 ≤ 10007833191735861^4375*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20067019851030432819 20000000000000000000 10007833191735861 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007833191735861/10000000000000000 : ℝ)) (X := (20067019851030432819/20000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10067018850981415929/10000000000000000000 : ℝ) ≤ (2003133229880623/2000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (10067018850981415929/10000000000000000000 : ℝ)^1024 ≤ (2003133229880623/2000000000000000 : ℝ)^4375 := by
      have hnat : (10067018850981415929 : ℕ)^1024*2000000000000000^4375 ≤ 2003133229880623^4375*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10067018850981415929 10000000000000000000 2003133229880623 2000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003133229880623/2000000000000000 : ℝ)) (X := (10067018850981415929/10000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(100004901689/2000000000000000000 : ℝ) ≤ ((243899378845156567411/243930000000000000000 : ℝ)+2*(3916478833627/1219650000000000 : ℝ)*(391/20000 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (243899378845156567411/243930000000000000000 : ℝ)+2*(3916478833627/1219650000000000 : ℝ)*(391/20000 : ℝ)=(10000000234068607/10000000000000000 : ℝ) by norm_num, show 1+2*(100004901689/2000000000000000000 : ℝ)=(1000000100004901689/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67018850981415929/20000000000000000000 : ℝ)+(100004901689/2000000000000000000 : ℝ) ≤ ((243899378845156567411/243930000000000000000 : ℝ)+(3916478833627/1219650000000000 : ℝ)*((6587/25000 : ℝ)+(391/20000 : ℝ)))^(4375/1024 : ℝ) := by
    rw [show (243899378845156567411/243930000000000000000 : ℝ)+(3916478833627/1219650000000000 : ℝ)*((6587/25000 : ℝ)+(391/20000 : ℝ))=(10007833191735861/10000000000000000 : ℝ) by norm_num, show 1+(67018850981415929/20000000000000000000 : ℝ)+(100004901689/2000000000000000000 : ℝ)=(20067019851030432819/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67018850981415929/20000000000000000000 : ℝ) ≤ ((243899378845156567411/243930000000000000000 : ℝ)+2*(3916478833627/1219650000000000 : ℝ)*(6587/25000 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (243899378845156567411/243930000000000000000 : ℝ)+2*(3916478833627/1219650000000000 : ℝ)*(6587/25000 : ℝ)=(2003133229880623/2000000000000000 : ℝ) by norm_num, show 1+2*(67018850981415929/20000000000000000000 : ℝ)=(10067018850981415929/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (243899378845156567411/243930000000000000000 : ℝ)*(X 1 0+X 2 0)+(3916478833627/1219650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (391/20000 : ℝ)) (hi := (6587/25000 : ℝ)) (c := (243899378845156567411/243930000000000000000 : ℝ)) (alpha := (3916478833627/1219650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (243899378845156567411/243930000000000000000 : ℝ)*(X 0 1+X 2 1)+(3916478833627/1219650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (391/20000 : ℝ)) (hi := (6587/25000 : ℝ)) (c := (243899378845156567411/243930000000000000000 : ℝ)) (alpha := (3916478833627/1219650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (243899378845156567411/243930000000000000000 : ℝ)*(X 0 2+X 1 2)+(3916478833627/1219650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (391/20000 : ℝ)) (hi := (6587/25000 : ℝ)) (c := (243899378845156567411/243930000000000000000 : ℝ)) (alpha := (3916478833627/1219650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1940401323/10000000000 : ℝ)*X 0 0+(1122095579/2000000000 : ℝ)*X 0 1+(2535842197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42172803/78125000 : ℝ)*X 1 0+(-2226189701/10000000000 : ℝ)*X 1 1+(40573453/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5398117063/10000000000 : ℝ)*X 2 0+(5071684233/10000000000 : ℝ)*X 2 1+(-1113094301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2139500301/5000000000 : ℝ)*X 0 0+(233391237/625000000 : ℝ)*X 0 1+(2447154493/5000000000 : ℝ)*X 0 2+(2139500301/5000000000 : ℝ)*X 1 0+(233391237/625000000 : ℝ)*X 1 1+(2447154493/5000000000 : ℝ)*X 1 2+(2139500301/5000000000 : ℝ)*X 2 0+(233391237/625000000 : ℝ)*X 2 1+(2447154493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-121301053/625000000 : ℝ)*X 0 0+(1269516313/2500000000 : ℝ)*X 0 1+(1400997017/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257482129/10000000000 : ℝ)*X 1 0+(-169388307/1000000000 : ℝ)*X 1 1+(224159523/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314370527/2500000000 : ℝ)*X 2 0+(2801994021/5000000000 : ℝ)*X 2 1+(-423470787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((855978939/2000000000 : ℝ)*X 0 0+(244028409/500000000 : ℝ)*X 0 1+(3748237919/10000000000 : ℝ)*X 0 2+(855978939/2000000000 : ℝ)*X 1 0+(244028409/500000000 : ℝ)*X 1 1+(3748237919/10000000000 : ℝ)*X 1 2+(855978939/2000000000 : ℝ)*X 2 0+(244028409/500000000 : ℝ)*X 2 1+(3748237919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21073349810595493174287/20327500000000000000000000000 : ℝ) := by norm_num
    linear_combination (38443251/50000000000000 : ℝ)*(base1) + (19397471/3125000000000 : ℝ)*(base19) + (32243079/100000000000000 : ℝ)*(base23) + (172259223/50000000000000 : ℝ)*(upper5) + (679508175446629/50000000000000 : ℝ)*(major0) + (679508175446629/50000000000000 : ℝ)*(major1) + (679508175446629/50000000000000 : ℝ)*(major2) + (1855995714424233/100000000000000 : ℝ)*(sp0) + (92799518822817/5000000000000 : ℝ)*(sp1) + (1855991089348397/100000000000000 : ℝ)*(sp2) + (215508966588129/25000000000000 : ℝ)*(sp3) + (4640362319/100000000000000 : ℝ)*(sp5) + (2257973127/50000000000000 : ℝ)*(sp6) + (1086453371/100000000000000 : ℝ)*(sp7) + (86203702969239/10000000000000 : ℝ)*(f.failure) + (185599563753773/10000000000000 : ℝ)*(f.sum) + (64164715310081/60982500000000000000000000000 : ℝ)*base65 + (17393152759400769173/4065500000000000000000000000000000 : ℝ)*base67 + (17321348966969230827/4065500000000000000000000000000000 : ℝ)*base70 + (12102440338235269173/4065500000000000000000000000000000 : ℝ)*base71 + (342887880395951/60982500000000000000000000000 : ℝ)*base73 + (51254364358775730827/4065500000000000000000000000000000 : ℝ)*base76 + (12106123099210730827/4065500000000000000000000000000000 : ℝ)*base78 + (4625085602373769173/4065500000000000000000000000000000 : ℝ)*base79 + (121272057495397/121965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5918143/1000000000000000000000 : ℝ)*base89 + (5918143/1000000000000000000000 : ℝ)*base91 + (5918143/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10197056949011446165240683331/1016375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23566347/25000000000000 : ℝ)*(base1) + (2035756501/100000000000000 : ℝ)*(base19) + (1011711621/50000000000000 : ℝ)*(base23) + (117759141/50000000000000 : ℝ)*(upper3) + (13890963/6250000000000 : ℝ)*(upper5) + (348069305280721/25000000000000 : ℝ)*(major0) + (348069305280721/25000000000000 : ℝ)*(major1) + (348069305280721/25000000000000 : ℝ)*(major2) + (11420254001/100000000000000 : ℝ)*(sp1) + (702703233/6250000000000 : ℝ)*(sp2) + (1901419485261591/100000000000000 : ℝ)*(sp4) + (19014059349857/1000000000000 : ℝ)*(sp5) + (118837882770077/6250000000000 : ℝ)*(sp6) + (27597956954953/3125000000000 : ℝ)*(sp7) + (220783679205971/25000000000000 : ℝ)*(f.failure) + (950709695498101/50000000000000 : ℝ)*(f.sum) + (19207114471357/15245625000000000000000000000 : ℝ)*base65 + (1075637355983472223/2032750000000000000000000000000000 : ℝ)*base68 + (18531090900183472223/2032750000000000000000000000000000 : ℝ)*base70 + (3286040745621472223/2032750000000000000000000000000000 : ℝ)*base72 + (500474025212801/121965000000000000000000000000 : ℝ)*base73 + (1842627864629777777/2032750000000000000000000000000000 : ℝ)*base75 + (9253669962750472223/2032750000000000000000000000000000 : ℝ)*base78 + (9789459293737527777/2032750000000000000000000000000000 : ℝ)*base79 + (19387393776293/15245625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8921627/2500000000000000000000 : ℝ)*base89 + (8921627/2500000000000000000000 : ℝ)*base91 + (8921627/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1416_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6587/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (391/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (943/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9467/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1416_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1416_s2_0 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-987254629/5000000000 : ℝ)*x 0 + (2730566237/5000000000 : ℝ)*x 1 + (649886409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987254629/5000000000 : ℝ)^547 ≤ (12028999832033/100000000000000 : ℝ)^419 := by
    have hnat : (987254629 : ℕ)^547*100000000000000^419 ≤ 12028999832033^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987254629 5000000000 12028999832033 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730566237/5000000000 : ℝ)^547 ≤ (45396816812247/100000000000000 : ℝ)^419 := by
    have hnat : (2730566237 : ℕ)^547*100000000000000^419 ≤ 45396816812247^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730566237 5000000000 45396816812247 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649886409/1250000000 : ℝ)^547 ≤ (21287091669263/50000000000000 : ℝ)^419 := by
    have hnat : (649886409 : ℕ)^547*50000000000000^419 ≤ 21287091669263^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649886409 1250000000 21287091669263 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987254629/5000000000 : ℝ), (2730566237/5000000000 : ℝ), (649886409/1250000000 : ℝ)] ![(12028999832033/100000000000000 : ℝ), (45396816812247/100000000000000 : ℝ), (21287091669263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987254629/5000000000 : ℝ)|^547 ≤ (12028999832033/100000000000000 : ℝ)^419
        have hw : |(-987254629/5000000000 : ℝ)|=(987254629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730566237/5000000000 : ℝ)|^547 ≤ (45396816812247/100000000000000 : ℝ)^419
        have hw : |(2730566237/5000000000 : ℝ)|=(2730566237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649886409/1250000000 : ℝ)|^547 ≤ (21287091669263/50000000000000 : ℝ)^419
        have hw : |(649886409/1250000000 : ℝ)|=(649886409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s2_1 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1340243083/2500000000 : ℝ)*x 0 + (-527351721/2500000000 : ℝ)*x 1 + (649886403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340243083/2500000000 : ℝ)^547 ≤ (44312921456317/100000000000000 : ℝ)^419 := by
    have hnat : (1340243083 : ℕ)^547*100000000000000^419 ≤ 44312921456317^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340243083 2500000000 44312921456317 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527351721/2500000000 : ℝ)^547 ≤ (13112895707073/100000000000000 : ℝ)^419 := by
    have hnat : (527351721 : ℕ)^547*100000000000000^419 ≤ 13112895707073^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527351721 2500000000 13112895707073 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649886403/1250000000 : ℝ)^547 ≤ (42574182825389/100000000000000 : ℝ)^419 := by
    have hnat : (649886403 : ℕ)^547*100000000000000^419 ≤ 42574182825389^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649886403 1250000000 42574182825389 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340243083/2500000000 : ℝ), (-527351721/2500000000 : ℝ), (649886403/1250000000 : ℝ)] ![(44312921456317/100000000000000 : ℝ), (13112895707073/100000000000000 : ℝ), (42574182825389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340243083/2500000000 : ℝ)|^547 ≤ (44312921456317/100000000000000 : ℝ)^419
        have hw : |(1340243083/2500000000 : ℝ)|=(1340243083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527351721/2500000000 : ℝ)|^547 ≤ (13112895707073/100000000000000 : ℝ)^419
        have hw : |(-527351721/2500000000 : ℝ)|=(527351721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649886403/1250000000 : ℝ)|^547 ≤ (42574182825389/100000000000000 : ℝ)^419
        have hw : |(649886403/1250000000 : ℝ)|=(649886403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s2_2 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (20941297/39062500 : ℝ)*x 0 + (2599545781/5000000000 : ℝ)*x 1 + (-2109406837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20941297/39062500 : ℝ)^547 ≤ (44312918219029/100000000000000 : ℝ)^419 := by
    have hnat : (20941297 : ℕ)^547*100000000000000^419 ≤ 44312918219029^419*39062500^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20941297 39062500 44312918219029 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599545781/5000000000 : ℝ)^547 ≤ (4257418643873/10000000000000 : ℝ)^419 := by
    have hnat : (2599545781 : ℕ)^547*10000000000000^419 ≤ 4257418643873^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599545781 5000000000 4257418643873 10000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109406837/10000000000 : ℝ)^547 ≤ (819555957853/6250000000000 : ℝ)^419 := by
    have hnat : (2109406837 : ℕ)^547*6250000000000^419 ≤ 819555957853^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109406837 10000000000 819555957853 6250000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20941297/39062500 : ℝ), (2599545781/5000000000 : ℝ), (-2109406837/10000000000 : ℝ)] ![(44312918219029/100000000000000 : ℝ), (4257418643873/10000000000000 : ℝ), (819555957853/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20941297/39062500 : ℝ)|^547 ≤ (44312918219029/100000000000000 : ℝ)^419
        have hw : |(20941297/39062500 : ℝ)|=(20941297/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2599545781/5000000000 : ℝ)|^547 ≤ (4257418643873/10000000000000 : ℝ)^419
        have hw : |(2599545781/5000000000 : ℝ)|=(2599545781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109406837/10000000000 : ℝ)|^547 ≤ (819555957853/6250000000000 : ℝ)^419
        have hw : |(-2109406837/10000000000 : ℝ)|=(2109406837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s2_3 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1075761673/2500000000 : ℝ)*x 0 + (4029301503/10000000000 : ℝ)*x 1 + (11483713/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075761673/2500000000 : ℝ)^547 ≤ (1039318360063/3125000000000 : ℝ)^419 := by
    have hnat : (1075761673 : ℕ)^547*3125000000000^419 ≤ 1039318360063^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075761673 2500000000 1039318360063 3125000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029301503/10000000000 : ℝ)^547 ≤ (30523315031027/100000000000000 : ℝ)^419 := by
    have hnat : (4029301503 : ℕ)^547*100000000000000^419 ≤ 30523315031027^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029301503 10000000000 30523315031027 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11483713/25000000 : ℝ)^547 ≤ (36218497436709/100000000000000 : ℝ)^419 := by
    have hnat : (11483713 : ℕ)^547*100000000000000^419 ≤ 36218497436709^419*25000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11483713 25000000 36218497436709 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075761673/2500000000 : ℝ), (4029301503/10000000000 : ℝ), (11483713/25000000 : ℝ)] ![(1039318360063/3125000000000 : ℝ), (30523315031027/100000000000000 : ℝ), (36218497436709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075761673/2500000000 : ℝ)|^547 ≤ (1039318360063/3125000000000 : ℝ)^419
        have hw : |(1075761673/2500000000 : ℝ)|=(1075761673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029301503/10000000000 : ℝ)|^547 ≤ (30523315031027/100000000000000 : ℝ)^419
        have hw : |(4029301503/10000000000 : ℝ)|=(4029301503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11483713/25000000 : ℝ)|^547 ≤ (36218497436709/100000000000000 : ℝ)^419
        have hw : |(11483713/25000000 : ℝ)|=(11483713/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s2_4 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-197455739/1000000000 : ℝ)*x 0 + (2600305059/5000000000 : ℝ)*x 1 + (2729800433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197455739/1000000000 : ℝ)^547 ≤ (6014691319209/50000000000000 : ℝ)^419 := by
    have hnat : (197455739 : ℕ)^547*50000000000000^419 ≤ 6014691319209^419*1000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197455739 1000000000 6014691319209 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600305059/5000000000 : ℝ)^547 ≤ (212952105341/500000000000 : ℝ)^419 := by
    have hnat : (2600305059 : ℕ)^547*500000000000^419 ≤ 212952105341^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600305059 5000000000 212952105341 500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729800433/5000000000 : ℝ)^547 ≤ (45380196276703/100000000000000 : ℝ)^419 := by
    have hnat : (2729800433 : ℕ)^547*100000000000000^419 ≤ 45380196276703^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729800433 5000000000 45380196276703 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197455739/1000000000 : ℝ), (2600305059/5000000000 : ℝ), (2729800433/5000000000 : ℝ)] ![(6014691319209/50000000000000 : ℝ), (212952105341/500000000000 : ℝ), (45380196276703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197455739/1000000000 : ℝ)|^547 ≤ (6014691319209/50000000000000 : ℝ)^419
        have hw : |(-197455739/1000000000 : ℝ)|=(197455739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600305059/5000000000 : ℝ)|^547 ≤ (212952105341/500000000000 : ℝ)^419
        have hw : |(2600305059/5000000000 : ℝ)|=(2600305059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729800433/5000000000 : ℝ)|^547 ≤ (45380196276703/100000000000000 : ℝ)^419
        have hw : |(2729800433/5000000000 : ℝ)|=(2729800433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s2_5 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1323229289/2500000000 : ℝ)*x 0 + (-369779427/2000000000 : ℝ)*x 1 + (2729800559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323229289/2500000000 : ℝ)^547 ≤ (43579968900779/100000000000000 : ℝ)^419 := by
    have hnat : (1323229289 : ℕ)^547*100000000000000^419 ≤ 43579968900779^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323229289 2500000000 43579968900779 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369779427/2000000000 : ℝ)^547 ≤ (1379979010119/12500000000000 : ℝ)^419 := by
    have hnat : (369779427 : ℕ)^547*12500000000000^419 ≤ 1379979010119^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369779427 2000000000 1379979010119 12500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729800559/5000000000 : ℝ)^547 ≤ (45380199011211/100000000000000 : ℝ)^419 := by
    have hnat : (2729800559 : ℕ)^547*100000000000000^419 ≤ 45380199011211^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729800559 5000000000 45380199011211 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323229289/2500000000 : ℝ), (-369779427/2000000000 : ℝ), (2729800559/5000000000 : ℝ)] ![(43579968900779/100000000000000 : ℝ), (1379979010119/12500000000000 : ℝ), (45380199011211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323229289/2500000000 : ℝ)|^547 ≤ (43579968900779/100000000000000 : ℝ)^419
        have hw : |(1323229289/2500000000 : ℝ)|=(1323229289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369779427/2000000000 : ℝ)|^547 ≤ (1379979010119/12500000000000 : ℝ)^419
        have hw : |(-369779427/2000000000 : ℝ)|=(369779427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729800559/5000000000 : ℝ)|^547 ≤ (45380199011211/100000000000000 : ℝ)^419
        have hw : |(2729800559/5000000000 : ℝ)|=(2729800559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s2_6 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5292917121/10000000000 : ℝ)*x 0 + (2729800557/5000000000 : ℝ)*x 1 + (-462224297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292917121/10000000000 : ℝ)^547 ≤ (21789984262283/50000000000000 : ℝ)^419 := by
    have hnat : (5292917121 : ℕ)^547*50000000000000^419 ≤ 21789984262283^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292917121 10000000000 21789984262283 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729800557/5000000000 : ℝ)^547 ≤ (22690099483903/50000000000000 : ℝ)^419 := by
    have hnat : (2729800557 : ℕ)^547*50000000000000^419 ≤ 22690099483903^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729800557 5000000000 22690099483903 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462224297/2500000000 : ℝ)^547 ≤ (5519916247047/50000000000000 : ℝ)^419 := by
    have hnat : (462224297 : ℕ)^547*50000000000000^419 ≤ 5519916247047^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462224297 2500000000 5519916247047 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292917121/10000000000 : ℝ), (2729800557/5000000000 : ℝ), (-462224297/2500000000 : ℝ)] ![(21789984262283/50000000000000 : ℝ), (22690099483903/50000000000000 : ℝ), (5519916247047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292917121/10000000000 : ℝ)|^547 ≤ (21789984262283/50000000000000 : ℝ)^419
        have hw : |(5292917121/10000000000 : ℝ)|=(5292917121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729800557/5000000000 : ℝ)|^547 ≤ (22690099483903/50000000000000 : ℝ)^419
        have hw : |(2729800557/5000000000 : ℝ)|=(2729800557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-462224297/2500000000 : ℝ)|^547 ≤ (5519916247047/50000000000000 : ℝ)^419
        have hw : |(-462224297/2500000000 : ℝ)|=(462224297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s2_7 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4303150067/10000000000 : ℝ)*x 0 + (4590215179/10000000000 : ℝ)*x 1 + (4032598833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303150067/10000000000 : ℝ)^547 ≤ (4157403823847/12500000000000 : ℝ)^419 := by
    have hnat : (4303150067 : ℕ)^547*12500000000000^419 ≤ 4157403823847^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303150067 10000000000 4157403823847 12500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4590215179/10000000000 : ℝ)^547 ≤ (1447393650587/4000000000000 : ℝ)^419 := by
    have hnat : (4590215179 : ℕ)^547*4000000000000^419 ≤ 1447393650587^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590215179 10000000000 1447393650587 4000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032598833/10000000000 : ℝ)^547 ≤ (30555928119021/100000000000000 : ℝ)^419 := by
    have hnat : (4032598833 : ℕ)^547*100000000000000^419 ≤ 30555928119021^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032598833 10000000000 30555928119021 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303150067/10000000000 : ℝ), (4590215179/10000000000 : ℝ), (4032598833/10000000000 : ℝ)] ![(4157403823847/12500000000000 : ℝ), (1447393650587/4000000000000 : ℝ), (30555928119021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303150067/10000000000 : ℝ)|^547 ≤ (4157403823847/12500000000000 : ℝ)^419
        have hw : |(4303150067/10000000000 : ℝ)|=(4303150067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4590215179/10000000000 : ℝ)|^547 ≤ (1447393650587/4000000000000 : ℝ)^419
        have hw : |(4590215179/10000000000 : ℝ)|=(4590215179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032598833/10000000000 : ℝ)|^547 ≤ (30555928119021/100000000000000 : ℝ)^419
        have hw : |(4032598833/10000000000 : ℝ)|=(4032598833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1416_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10297/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (99/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (943/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (943/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (943/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (943/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (943/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (943/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (943/12500 : ℝ) ^ (4375/1024 : ℝ) ≤ (1601758437305327/100000000000000000000 : ℝ) := by
    have hpowers : (943/12500 : ℝ)^4375 ≤ (1601758437305327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (943 : ℕ)^4375*100000000000000000000^1024 ≤ 1601758437305327^1024*12500^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        943 12500 1601758437305327 100000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (943/12500 : ℝ)) (X := (1601758437305327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9467/50000 : ℝ) ^ (4375/1024 : ℝ) ≤ (5104183599901099/6250000000000000000 : ℝ) := by
    have hpowers : (9467/50000 : ℝ)^4375 ≤ (5104183599901099/6250000000000000000 : ℝ)^1024 := by
      have hnat : (9467 : ℕ)^4375*6250000000000000000^1024 ≤ 5104183599901099^1024*50000^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9467 50000 5104183599901099 6250000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9467/50000 : ℝ)) (X := (5104183599901099/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001601758437305327/50000000000000000000 : ℝ) ≤ (10000074979680791/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (50001601758437305327/50000000000000000000 : ℝ)^1024 ≤ (10000074979680791/10000000000000000 : ℝ)^4375 := by
      have hnat : (50001601758437305327 : ℕ)^1024*10000000000000000^4375 ≤ 10000074979680791^4375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001601758437305327 50000000000000000000 10000074979680791 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000074979680791/10000000000000000 : ℝ)) (X := (50001601758437305327/50000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100083268696035722911/100000000000000000000 : ℝ) ≤ (2000389668419511/2000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (100083268696035722911/100000000000000000000 : ℝ)^1024 ≤ (2000389668419511/2000000000000000 : ℝ)^4375 := by
      have hnat : (100083268696035722911 : ℕ)^1024*2000000000000000^4375 ≤ 2000389668419511^4375*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100083268696035722911 100000000000000000000 2000389668419511 2000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000389668419511/2000000000000000 : ℝ)) (X := (100083268696035722911/100000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3130104183599901099/3125000000000000000 : ℝ) ≤ (10003821704514319/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (3130104183599901099/3125000000000000000 : ℝ)^1024 ≤ (10003821704514319/10000000000000000 : ℝ)^4375 := by
      have hnat : (3130104183599901099 : ℕ)^1024*10000000000000000^4375 ≤ 10003821704514319^4375*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3130104183599901099 3125000000000000000 10003821704514319 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003821704514319/10000000000000000 : ℝ)) (X := (3130104183599901099/3125000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1601758437305327/100000000000000000000 : ℝ) ≤ ((56936294363210037129/56950000000000000000 : ℝ)+2*(468340604191/284750000000000 : ℝ)*(943/12500 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (56936294363210037129/56950000000000000000 : ℝ)+2*(468340604191/284750000000000 : ℝ)*(943/12500 : ℝ)=(10000074979680791/10000000000000000 : ℝ) by norm_num, show 1+2*(1601758437305327/100000000000000000000 : ℝ)=(50001601758437305327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5104183599901099/6250000000000000000 : ℝ)+(1601758437305327/100000000000000000000 : ℝ) ≤ ((56936294363210037129/56950000000000000000 : ℝ)+(468340604191/284750000000000 : ℝ)*((9467/50000 : ℝ)+(943/12500 : ℝ)))^(4375/1024 : ℝ) := by
    rw [show (56936294363210037129/56950000000000000000 : ℝ)+(468340604191/284750000000000 : ℝ)*((9467/50000 : ℝ)+(943/12500 : ℝ))=(2000389668419511/2000000000000000 : ℝ) by norm_num, show 1+(5104183599901099/6250000000000000000 : ℝ)+(1601758437305327/100000000000000000000 : ℝ)=(100083268696035722911/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5104183599901099/6250000000000000000 : ℝ) ≤ ((56936294363210037129/56950000000000000000 : ℝ)+2*(468340604191/284750000000000 : ℝ)*(9467/50000 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (56936294363210037129/56950000000000000000 : ℝ)+2*(468340604191/284750000000000 : ℝ)*(9467/50000 : ℝ)=(10003821704514319/10000000000000000 : ℝ) by norm_num, show 1+2*(5104183599901099/6250000000000000000 : ℝ)=(3130104183599901099/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56936294363210037129/56950000000000000000 : ℝ)*(X 1 0+X 2 0)+(468340604191/284750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (943/12500 : ℝ)) (hi := (9467/50000 : ℝ)) (c := (56936294363210037129/56950000000000000000 : ℝ)) (alpha := (468340604191/284750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56936294363210037129/56950000000000000000 : ℝ)*(X 0 1+X 2 1)+(468340604191/284750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (943/12500 : ℝ)) (hi := (9467/50000 : ℝ)) (c := (56936294363210037129/56950000000000000000 : ℝ)) (alpha := (468340604191/284750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56936294363210037129/56950000000000000000 : ℝ)*(X 0 2+X 1 2)+(468340604191/284750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (943/12500 : ℝ)) (hi := (9467/50000 : ℝ)) (c := (56936294363210037129/56950000000000000000 : ℝ)) (alpha := (468340604191/284750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-987254629/5000000000 : ℝ)*X 0 0+(2730566237/5000000000 : ℝ)*X 0 1+(649886409/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340243083/2500000000 : ℝ)*X 1 0+(-527351721/2500000000 : ℝ)*X 1 1+(649886403/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((20941297/39062500 : ℝ)*X 2 0+(2599545781/5000000000 : ℝ)*X 2 1+(-2109406837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075761673/2500000000 : ℝ)*X 0 0+(4029301503/10000000000 : ℝ)*X 0 1+(11483713/25000000 : ℝ)*X 0 2+(1075761673/2500000000 : ℝ)*X 1 0+(4029301503/10000000000 : ℝ)*X 1 1+(11483713/25000000 : ℝ)*X 1 2+(1075761673/2500000000 : ℝ)*X 2 0+(4029301503/10000000000 : ℝ)*X 2 1+(11483713/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-197455739/1000000000 : ℝ)*X 0 0+(2600305059/5000000000 : ℝ)*X 0 1+(2729800433/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323229289/2500000000 : ℝ)*X 1 0+(-369779427/2000000000 : ℝ)*X 1 1+(2729800559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292917121/10000000000 : ℝ)*X 2 0+(2729800557/5000000000 : ℝ)*X 2 1+(-462224297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303150067/10000000000 : ℝ)*X 0 0+(4590215179/10000000000 : ℝ)*X 0 1+(4032598833/10000000000 : ℝ)*X 0 2+(4303150067/10000000000 : ℝ)*X 1 0+(4590215179/10000000000 : ℝ)*X 1 1+(4032598833/10000000000 : ℝ)*X 1 2+(4303150067/10000000000 : ℝ)*X 2 0+(4590215179/10000000000 : ℝ)*X 2 1+(4032598833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9376467134801973169783840041/1423750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (889285197/100000000000000 : ℝ)*(base19) + (481432777/100000000000000 : ℝ)*(base23) + (4166487/4000000000000 : ℝ)*(lower2) + (100004803/50000000000000 : ℝ)*(upper3) + (10819293/25000000000000 : ℝ)*(upper5) + (1397173602443081/50000000000000 : ℝ)*(major0) + (1397173602443081/50000000000000 : ℝ)*(major1) + (1397173602443081/50000000000000 : ℝ)*(major2) + (477025638263077/12500000000000 : ℝ)*(sp0) + (954053056149177/25000000000000 : ℝ)*(sp1) + (477026579056141/12500000000000 : ℝ)*(sp2) + (886237947308281/50000000000000 : ℝ)*(sp3) + (8007777289/100000000000000 : ℝ)*(sp4) + (5181748719/100000000000000 : ℝ)*(sp7) + (886240538182641/50000000000000 : ℝ)*(f.failure) + (763242622776381/20000000000000 : ℝ)*(f.sum) + (44105603609359/28475000000000000000000000000 : ℝ)*base65 + (28320855981254145551/2847500000000000000000000000000000 : ℝ)*base68 + (6293628712554145551/2847500000000000000000000000000000 : ℝ)*base70 + (20220862208104145551/2847500000000000000000000000000000 : ℝ)*base72 + (2225615454741/28475000000000000000000000000 : ℝ)*base74 + (25594116878739145551/2847500000000000000000000000000000 : ℝ)*base76 + (18582140309504145551/2847500000000000000000000000000000 : ℝ)*base78 + (7921786984129145551/2847500000000000000000000000000000 : ℝ)*base80 + (23724259246159/28475000000000000000000000000 : ℝ)*base81 + (76897417/5000000000000000000000 : ℝ)*base89 + (76897417/5000000000000000000000 : ℝ)*base91 + (76897417/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1403386082279315238306618333/284750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (197898521/50000000000000 : ℝ)*(base19) + (14872543/3125000000000 : ℝ)*(base23) + (31695279/25000000000000 : ℝ)*(upper3) + (2412469/5000000000000 : ℝ)*(lower4) + (85820959/100000000000000 : ℝ)*(upper5) + (282724399110147/10000000000000 : ℝ)*(major0) + (282724399110147/10000000000000 : ℝ)*(major1) + (282724399110147/10000000000000 : ℝ)*(major2) + (5766662287/100000000000000 : ℝ)*(sp1) + (6894267477/100000000000000 : ℝ)*(sp2) + (386113999638517/10000000000000 : ℝ)*(sp4) + (48264172924073/1250000000000 : ℝ)*(sp5) + (3861132626196317/100000000000000 : ℝ)*(sp6) + (71733912861397/4000000000000 : ℝ)*(sp7) + (71733912861397/4000000000000 : ℝ)*(f.failure) + (386113999638517/10000000000000 : ℝ)*(f.sum) + (39378091775183/5695000000000000000000000000 : ℝ)*base65 + (8012054978013547963/569500000000000000000000000000000 : ℝ)*base67 + (1735980966868547963/569500000000000000000000000000000 : ℝ)*base69 + (8460383793365547963/569500000000000000000000000000000 : ℝ)*base71 + (24072831714743/5695000000000000000000000000 : ℝ)*base73 + (13407882790302547963/569500000000000000000000000000000 : ℝ)*base75 + (6912430230224047963/569500000000000000000000000000000 : ℝ)*base77 + (10751078809449547963/569500000000000000000000000000000 : ℝ)*base79 + (476613835823/1423750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2703411/400000000000000000000 : ℝ)*base90 + (2703411/400000000000000000000 : ℝ)*base92 + (2703411/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1416_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (99/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1416_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1416_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (99/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1416_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1416_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1416_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (99/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1416_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
