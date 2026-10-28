-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:38:39.315825+00:00
-- url     : https://prove2.me/submissions/c0be59e8-36fb-4d4d-8a68-9ae7bc1172ce

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
theorem support_rectangle_w1157_box_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2033333941/10000000000 : ℝ)*x 0 + (5376095679/10000000000 : ℝ)*x 1 + (2688047759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033333941/10000000000 : ℝ)^4175 ≤ (6058470690141/50000000000000 : ℝ)^3151 := by
    have hnat : (2033333941 : ℕ)^4175*50000000000000^3151 ≤ 6058470690141^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033333941 10000000000 6058470690141 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376095679/10000000000 : ℝ)^4175 ≤ (21970765085887/50000000000000 : ℝ)^3151 := by
    have hnat : (5376095679 : ℕ)^4175*50000000000000^3151 ≤ 21970765085887^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376095679 10000000000 21970765085887 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688047759/5000000000 : ℝ)^4175 ≤ (43941528428193/100000000000000 : ℝ)^3151 := by
    have hnat : (2688047759 : ℕ)^4175*100000000000000^3151 ≤ 43941528428193^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688047759 5000000000 43941528428193 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2033333941/10000000000 : ℝ), (5376095679/10000000000 : ℝ), (2688047759/5000000000 : ℝ)] ![(6058470690141/50000000000000 : ℝ), (21970765085887/50000000000000 : ℝ), (43941528428193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2033333941/10000000000 : ℝ)|^4175 ≤ (6058470690141/50000000000000 : ℝ)^3151
        have hw : |(-2033333941/10000000000 : ℝ)|=(2033333941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376095679/10000000000 : ℝ)|^4175 ≤ (21970765085887/50000000000000 : ℝ)^3151
        have hw : |(5376095679/10000000000 : ℝ)|=(5376095679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688047759/5000000000 : ℝ)|^4175 ≤ (43941528428193/100000000000000 : ℝ)^3151
        have hw : |(2688047759/5000000000 : ℝ)|=(2688047759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1324030211/2500000000 : ℝ)*x 0 + (-133864447/625000000 : ℝ)*x 1 + (1344023821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324030211/2500000000 : ℝ)^4175 ≤ (43077527598877/100000000000000 : ℝ)^3151 := by
    have hnat : (1324030211 : ℕ)^4175*100000000000000^3151 ≤ 43077527598877^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324030211 2500000000 43077527598877 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133864447/625000000 : ℝ)^4175 ≤ (129809464869/1000000000000 : ℝ)^3151 := by
    have hnat : (133864447 : ℕ)^4175*1000000000000^3151 ≤ 129809464869^3151*625000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133864447 625000000 129809464869 1000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344023821/2500000000 : ℝ)^4175 ≤ (10985381473511/25000000000000 : ℝ)^3151 := by
    have hnat : (1344023821 : ℕ)^4175*25000000000000^3151 ≤ 10985381473511^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344023821 2500000000 10985381473511 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324030211/2500000000 : ℝ), (-133864447/625000000 : ℝ), (1344023821/2500000000 : ℝ)] ![(43077527598877/100000000000000 : ℝ), (129809464869/1000000000000 : ℝ), (10985381473511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324030211/2500000000 : ℝ)|^4175 ≤ (43077527598877/100000000000000 : ℝ)^3151
        have hw : |(1324030211/2500000000 : ℝ)|=(1324030211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133864447/625000000 : ℝ)|^4175 ≤ (129809464869/1000000000000 : ℝ)^3151
        have hw : |(-133864447/625000000 : ℝ)|=(133864447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344023821/2500000000 : ℝ)|^4175 ≤ (10985381473511/25000000000000 : ℝ)^3151
        have hw : |(1344023821/2500000000 : ℝ)|=(1344023821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296120419/10000000000 : ℝ)*x 0 + (1075219101/2000000000 : ℝ)*x 1 + (-85673257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296120419/10000000000 : ℝ)^4175 ≤ (43077523018619/100000000000000 : ℝ)^3151 := by
    have hnat : (5296120419 : ℕ)^4175*100000000000000^3151 ≤ 43077523018619^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296120419 10000000000 43077523018619 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075219101/2000000000 : ℝ)^4175 ≤ (43941528287407/100000000000000 : ℝ)^3151 := by
    have hnat : (1075219101 : ℕ)^4175*100000000000000^3151 ≤ 43941528287407^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075219101 2000000000 43941528287407 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85673257/400000000 : ℝ)^4175 ≤ (12980948679159/100000000000000 : ℝ)^3151 := by
    have hnat : (85673257 : ℕ)^4175*100000000000000^3151 ≤ 12980948679159^3151*400000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85673257 400000000 12980948679159 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296120419/10000000000 : ℝ), (1075219101/2000000000 : ℝ), (-85673257/400000000 : ℝ)] ![(43077523018619/100000000000000 : ℝ), (43941528287407/100000000000000 : ℝ), (12980948679159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296120419/10000000000 : ℝ)|^4175 ≤ (43077523018619/100000000000000 : ℝ)^3151
        have hw : |(5296120419/10000000000 : ℝ)|=(5296120419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075219101/2000000000 : ℝ)|^4175 ≤ (43941528287407/100000000000000 : ℝ)^3151
        have hw : |(1075219101/2000000000 : ℝ)|=(1075219101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85673257/400000000 : ℝ)|^4175 ≤ (12980948679159/100000000000000 : ℝ)^3151
        have hw : |(-85673257/400000000 : ℝ)|=(85673257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4469954461/10000000000 : ℝ)*x 0 + (4310970067/10000000000 : ℝ)*x 1 + (4310970561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4469954461/10000000000 : ℝ)^4175 ≤ (34408039585071/100000000000000 : ℝ)^3151 := by
    have hnat : (4469954461 : ℕ)^4175*100000000000000^3151 ≤ 34408039585071^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469954461 10000000000 34408039585071 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310970067/10000000000 : ℝ)^4175 ≤ (16397988855767/50000000000000 : ℝ)^3151 := by
    have hnat : (4310970067 : ℕ)^4175*50000000000000^3151 ≤ 16397988855767^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310970067 10000000000 16397988855767 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4310970561/10000000000 : ℝ)^4175 ≤ (1024874459093/3125000000000 : ℝ)^3151 := by
    have hnat : (4310970561 : ℕ)^4175*3125000000000^3151 ≤ 1024874459093^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310970561 10000000000 1024874459093 3125000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4469954461/10000000000 : ℝ), (4310970067/10000000000 : ℝ), (4310970561/10000000000 : ℝ)] ![(34408039585071/100000000000000 : ℝ), (16397988855767/50000000000000 : ℝ), (1024874459093/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4469954461/10000000000 : ℝ)|^4175 ≤ (34408039585071/100000000000000 : ℝ)^3151
        have hw : |(4469954461/10000000000 : ℝ)|=(4469954461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310970067/10000000000 : ℝ)|^4175 ≤ (16397988855767/50000000000000 : ℝ)^3151
        have hw : |(4310970067/10000000000 : ℝ)|=(4310970067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4310970561/10000000000 : ℝ)|^4175 ≤ (1024874459093/3125000000000 : ℝ)^3151
        have hw : |(4310970561/10000000000 : ℝ)|=(4310970561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2287525699/10000000000 : ℝ)*x 0 + (2640664019/5000000000 : ℝ)*x 1 + (5281327739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2287525699/10000000000 : ℝ)^4175 ≤ (7081824803353/50000000000000 : ℝ)^3151 := by
    have hnat : (2287525699 : ℕ)^4175*50000000000000^3151 ≤ 7081824803353^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287525699 10000000000 7081824803353 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640664019/5000000000 : ℝ)^4175 ≤ (21459088399561/50000000000000 : ℝ)^3151 := by
    have hnat : (2640664019 : ℕ)^4175*50000000000000^3151 ≤ 21459088399561^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640664019 5000000000 21459088399561 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281327739/10000000000 : ℝ)^4175 ≤ (5364771697463/12500000000000 : ℝ)^3151 := by
    have hnat : (5281327739 : ℕ)^4175*12500000000000^3151 ≤ 5364771697463^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281327739 10000000000 5364771697463 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2287525699/10000000000 : ℝ), (2640664019/5000000000 : ℝ), (5281327739/10000000000 : ℝ)] ![(7081824803353/50000000000000 : ℝ), (21459088399561/50000000000000 : ℝ), (5364771697463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2287525699/10000000000 : ℝ)|^4175 ≤ (7081824803353/50000000000000 : ℝ)^3151
        have hw : |(-2287525699/10000000000 : ℝ)|=(2287525699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640664019/5000000000 : ℝ)|^4175 ≤ (21459088399561/50000000000000 : ℝ)^3151
        have hw : |(2640664019/5000000000 : ℝ)|=(2640664019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281327739/10000000000 : ℝ)|^4175 ≤ (5364771697463/12500000000000 : ℝ)^3151
        have hw : |(5281327739/10000000000 : ℝ)|=(5281327739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681525657/5000000000 : ℝ)*x 0 + (-2179154433/10000000000 : ℝ)*x 1 + (2640663861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681525657/5000000000 : ℝ)^4175 ≤ (2737519961907/6250000000000 : ℝ)^3151 := by
    have hnat : (2681525657 : ℕ)^4175*6250000000000^3151 ≤ 2737519961907^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681525657 5000000000 2737519961907 6250000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179154433/10000000000 : ℝ)^4175 ≤ (664075360003/5000000000000 : ℝ)^3151 := by
    have hnat : (2179154433 : ℕ)^4175*5000000000000^3151 ≤ 664075360003^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179154433 10000000000 664075360003 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640663861/5000000000 : ℝ)^4175 ≤ (2145908669833/5000000000000 : ℝ)^3151 := by
    have hnat : (2640663861 : ℕ)^4175*5000000000000^3151 ≤ 2145908669833^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640663861 5000000000 2145908669833 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681525657/5000000000 : ℝ), (-2179154433/10000000000 : ℝ), (2640663861/5000000000 : ℝ)] ![(2737519961907/6250000000000 : ℝ), (664075360003/5000000000000 : ℝ), (2145908669833/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681525657/5000000000 : ℝ)|^4175 ≤ (2737519961907/6250000000000 : ℝ)^3151
        have hw : |(2681525657/5000000000 : ℝ)|=(2681525657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179154433/10000000000 : ℝ)|^4175 ≤ (664075360003/5000000000000 : ℝ)^3151
        have hw : |(-2179154433/10000000000 : ℝ)|=(2179154433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640663861/5000000000 : ℝ)|^4175 ≤ (2145908669833/5000000000000 : ℝ)^3151
        have hw : |(2640663861/5000000000 : ℝ)|=(2640663861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363051043/10000000000 : ℝ)*x 0 + (1320332003/2500000000 : ℝ)*x 1 + (-272394301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363051043/10000000000 : ℝ)^4175 ≤ (43800316457981/100000000000000 : ℝ)^3151 := by
    have hnat : (5363051043 : ℕ)^4175*100000000000000^3151 ≤ 43800316457981^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363051043 10000000000 43800316457981 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320332003/2500000000 : ℝ)^4175 ≤ (42918176519173/100000000000000 : ℝ)^3151 := by
    have hnat : (1320332003 : ℕ)^4175*100000000000000^3151 ≤ 42918176519173^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320332003 2500000000 42918176519173 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272394301/1250000000 : ℝ)^4175 ≤ (13281506998173/100000000000000 : ℝ)^3151 := by
    have hnat : (272394301 : ℕ)^4175*100000000000000^3151 ≤ 13281506998173^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272394301 1250000000 13281506998173 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363051043/10000000000 : ℝ), (1320332003/2500000000 : ℝ), (-272394301/1250000000 : ℝ)] ![(43800316457981/100000000000000 : ℝ), (42918176519173/100000000000000 : ℝ), (13281506998173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363051043/10000000000 : ℝ)|^4175 ≤ (43800316457981/100000000000000 : ℝ)^3151
        have hw : |(5363051043/10000000000 : ℝ)|=(5363051043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320332003/2500000000 : ℝ)|^4175 ≤ (42918176519173/100000000000000 : ℝ)^3151
        have hw : |(1320332003/2500000000 : ℝ)|=(1320332003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272394301/1250000000 : ℝ)|^4175 ≤ (13281506998173/100000000000000 : ℝ)^3151
        have hw : |(-272394301/1250000000 : ℝ)|=(272394301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127405251/5000000000 : ℝ)*x 0 + (4418521481/10000000000 : ℝ)*x 1 + (4418521651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127405251/5000000000 : ℝ)^4175 ≤ (1007221876459/3125000000000 : ℝ)^3151 := by
    have hnat : (2127405251 : ℕ)^4175*3125000000000^3151 ≤ 1007221876459^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127405251 5000000000 1007221876459 3125000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4418521481/10000000000 : ℝ)^4175 ≤ (2117778069163/6250000000000 : ℝ)^3151 := by
    have hnat : (4418521481 : ℕ)^4175*6250000000000^3151 ≤ 2117778069163^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418521481 10000000000 2117778069163 6250000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418521651/10000000000 : ℝ)^4175 ≤ (33884450833959/100000000000000 : ℝ)^3151 := by
    have hnat : (4418521651 : ℕ)^4175*100000000000000^3151 ≤ 33884450833959^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418521651 10000000000 33884450833959 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127405251/5000000000 : ℝ), (4418521481/10000000000 : ℝ), (4418521651/10000000000 : ℝ)] ![(1007221876459/3125000000000 : ℝ), (2117778069163/6250000000000 : ℝ), (33884450833959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127405251/5000000000 : ℝ)|^4175 ≤ (1007221876459/3125000000000 : ℝ)^3151
        have hw : |(2127405251/5000000000 : ℝ)|=(2127405251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4418521481/10000000000 : ℝ)|^4175 ≤ (2117778069163/6250000000000 : ℝ)^3151
        have hw : |(4418521481/10000000000 : ℝ)|=(4418521481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418521651/10000000000 : ℝ)|^4175 ≤ (33884450833959/100000000000000 : ℝ)^3151
        have hw : |(4418521651/10000000000 : ℝ)|=(4418521651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_8 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-558588319/2500000000 : ℝ)*x 0 + (2608423769/5000000000 : ℝ)*x 1 + (5385705719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (558588319/2500000000 : ℝ)^4175 ≤ (1716135968429/12500000000000 : ℝ)^3151 := by
    have hnat : (558588319 : ℕ)^4175*12500000000000^3151 ≤ 1716135968429^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558588319 2500000000 1716135968429 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608423769/5000000000 : ℝ)^4175 ≤ (42225278040299/100000000000000 : ℝ)^3151 := by
    have hnat : (2608423769 : ℕ)^4175*100000000000000^3151 ≤ 42225278040299^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608423769 5000000000 42225278040299 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385705719/10000000000 : ℝ)^4175 ≤ (68821303437/156250000000 : ℝ)^3151 := by
    have hnat : (5385705719 : ℕ)^4175*156250000000^3151 ≤ 68821303437^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385705719 10000000000 68821303437 156250000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-558588319/2500000000 : ℝ), (2608423769/5000000000 : ℝ), (5385705719/10000000000 : ℝ)] ![(1716135968429/12500000000000 : ℝ), (42225278040299/100000000000000 : ℝ), (68821303437/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-558588319/2500000000 : ℝ)|^4175 ≤ (1716135968429/12500000000000 : ℝ)^3151
        have hw : |(-558588319/2500000000 : ℝ)|=(558588319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608423769/5000000000 : ℝ)|^4175 ≤ (42225278040299/100000000000000 : ℝ)^3151
        have hw : |(2608423769/5000000000 : ℝ)|=(2608423769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385705719/10000000000 : ℝ)|^4175 ≤ (68821303437/156250000000 : ℝ)^3151
        have hw : |(5385705719/10000000000 : ℝ)|=(5385705719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_9 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289329937/10000000000 : ℝ)*x 0 + (-267247243/1250000000 : ℝ)*x 1 + (336606583/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289329937/10000000000 : ℝ)^4175 ≤ (21502178364127/50000000000000 : ℝ)^3151 := by
    have hnat : (5289329937 : ℕ)^4175*50000000000000^3151 ≤ 21502178364127^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289329937 10000000000 21502178364127 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267247243/1250000000 : ℝ)^4175 ≤ (647500665107/5000000000000 : ℝ)^3151 := by
    have hnat : (267247243 : ℕ)^4175*5000000000000^3151 ≤ 647500665107^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267247243 1250000000 647500665107 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336606583/625000000 : ℝ)^4175 ≤ (44045629962811/100000000000000 : ℝ)^3151 := by
    have hnat : (336606583 : ℕ)^4175*100000000000000^3151 ≤ 44045629962811^3151*625000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336606583 625000000 44045629962811 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289329937/10000000000 : ℝ), (-267247243/1250000000 : ℝ), (336606583/625000000 : ℝ)] ![(21502178364127/50000000000000 : ℝ), (647500665107/5000000000000 : ℝ), (44045629962811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289329937/10000000000 : ℝ)|^4175 ≤ (21502178364127/50000000000000 : ℝ)^3151
        have hw : |(5289329937/10000000000 : ℝ)|=(5289329937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267247243/1250000000 : ℝ)|^4175 ≤ (647500665107/5000000000000 : ℝ)^3151
        have hw : |(-267247243/1250000000 : ℝ)|=(267247243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336606583/625000000 : ℝ)|^4175 ≤ (44045629962811/100000000000000 : ℝ)^3151
        have hw : |(336606583/625000000 : ℝ)|=(336606583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_10 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289330421/10000000000 : ℝ)*x 0 + (5385705163/10000000000 : ℝ)*x 1 + (-427595503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289330421/10000000000 : ℝ)^4175 ≤ (5375545242773/12500000000000 : ℝ)^3151 := by
    have hnat : (5289330421 : ℕ)^4175*12500000000000^3151 ≤ 5375545242773^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289330421 10000000000 5375545242773 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385705163/10000000000 : ℝ)^4175 ≤ (22022814087437/50000000000000 : ℝ)^3151 := by
    have hnat : (5385705163 : ℕ)^4175*50000000000000^3151 ≤ 22022814087437^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385705163 10000000000 22022814087437 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427595503/2000000000 : ℝ)^4175 ≤ (12950009859177/100000000000000 : ℝ)^3151 := by
    have hnat : (427595503 : ℕ)^4175*100000000000000^3151 ≤ 12950009859177^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427595503 2000000000 12950009859177 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289330421/10000000000 : ℝ), (5385705163/10000000000 : ℝ), (-427595503/2000000000 : ℝ)] ![(5375545242773/12500000000000 : ℝ), (22022814087437/50000000000000 : ℝ), (12950009859177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289330421/10000000000 : ℝ)|^4175 ≤ (5375545242773/12500000000000 : ℝ)^3151
        have hw : |(5289330421/10000000000 : ℝ)|=(5289330421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385705163/10000000000 : ℝ)|^4175 ≤ (22022814087437/50000000000000 : ℝ)^3151
        have hw : |(5385705163/10000000000 : ℝ)|=(5385705163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427595503/2000000000 : ℝ)|^4175 ≤ (12950009859177/100000000000000 : ℝ)^3151
        have hw : |(-427595503/2000000000 : ℝ)|=(427595503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_11 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2245749309/5000000000 : ℝ)*x 0 + (53750719/125000000 : ℝ)*x 1 + (2150028931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245749309/5000000000 : ℝ)^4175 ≤ (8656986010507/25000000000000 : ℝ)^3151 := by
    have hnat : (2245749309 : ℕ)^4175*25000000000000^3151 ≤ 8656986010507^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245749309 5000000000 8656986010507 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53750719/125000000 : ℝ)^4175 ≤ (326860262493/1000000000000 : ℝ)^3151 := by
    have hnat : (53750719 : ℕ)^4175*1000000000000^3151 ≤ 326860262493^3151*125000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53750719 125000000 326860262493 1000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150028931/5000000000 : ℝ)^4175 ≤ (32686029693767/100000000000000 : ℝ)^3151 := by
    have hnat : (2150028931 : ℕ)^4175*100000000000000^3151 ≤ 32686029693767^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150028931 5000000000 32686029693767 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245749309/5000000000 : ℝ), (53750719/125000000 : ℝ), (2150028931/5000000000 : ℝ)] ![(8656986010507/25000000000000 : ℝ), (326860262493/1000000000000 : ℝ), (32686029693767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245749309/5000000000 : ℝ)|^4175 ≤ (8656986010507/25000000000000 : ℝ)^3151
        have hw : |(2245749309/5000000000 : ℝ)|=(2245749309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53750719/125000000 : ℝ)|^4175 ≤ (326860262493/1000000000000 : ℝ)^3151
        have hw : |(53750719/125000000 : ℝ)|=(53750719/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2150028931/5000000000 : ℝ)|^4175 ≤ (32686029693767/100000000000000 : ℝ)^3151
        have hw : |(2150028931/5000000000 : ℝ)|=(2150028931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_12 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086816711/10000000000 : ℝ)*x 0 + (5439308551/10000000000 : ℝ)*x 1 + (263664117/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086816711/10000000000 : ℝ)^4175 ≤ (3135255306189/25000000000000 : ℝ)^3151 := by
    have hnat : (2086816711 : ℕ)^4175*25000000000000^3151 ≤ 3135255306189^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086816711 10000000000 3135255306189 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439308551/10000000000 : ℝ)^4175 ≤ (4462741083413/10000000000000 : ℝ)^3151 := by
    have hnat : (5439308551 : ℕ)^4175*10000000000000^3151 ≤ 4462741083413^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439308551 10000000000 4462741083413 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263664117/500000000 : ℝ)^4175 ≤ (21415783964797/50000000000000 : ℝ)^3151 := by
    have hnat : (263664117 : ℕ)^4175*50000000000000^3151 ≤ 21415783964797^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263664117 500000000 21415783964797 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086816711/10000000000 : ℝ), (5439308551/10000000000 : ℝ), (263664117/500000000 : ℝ)] ![(3135255306189/25000000000000 : ℝ), (4462741083413/10000000000000 : ℝ), (21415783964797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086816711/10000000000 : ℝ)|^4175 ≤ (3135255306189/25000000000000 : ℝ)^3151
        have hw : |(-2086816711/10000000000 : ℝ)|=(2086816711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439308551/10000000000 : ℝ)|^4175 ≤ (4462741083413/10000000000000 : ℝ)^3151
        have hw : |(5439308551/10000000000 : ℝ)|=(5439308551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263664117/500000000 : ℝ)|^4175 ≤ (21415783964797/50000000000000 : ℝ)^3151
        have hw : |(263664117/500000000 : ℝ)|=(263664117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_13 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671091423/1250000000 : ℝ)*x 0 + (-2182265417/10000000000 : ℝ)*x 1 + (2636641241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671091423/1250000000 : ℝ)^4175 ≤ (21930897426481/50000000000000 : ℝ)^3151 := by
    have hnat : (671091423 : ℕ)^4175*50000000000000^3151 ≤ 21930897426481^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671091423 1250000000 21930897426481 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182265417/10000000000 : ℝ)^4175 ≤ (13306635661951/100000000000000 : ℝ)^3151 := by
    have hnat : (2182265417 : ℕ)^4175*100000000000000^3151 ≤ 13306635661951^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182265417 10000000000 13306635661951 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636641241/5000000000 : ℝ)^4175 ≤ (42831569457791/100000000000000 : ℝ)^3151 := by
    have hnat : (2636641241 : ℕ)^4175*100000000000000^3151 ≤ 42831569457791^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636641241 5000000000 42831569457791 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671091423/1250000000 : ℝ), (-2182265417/10000000000 : ℝ), (2636641241/5000000000 : ℝ)] ![(21930897426481/50000000000000 : ℝ), (13306635661951/100000000000000 : ℝ), (42831569457791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671091423/1250000000 : ℝ)|^4175 ≤ (21930897426481/50000000000000 : ℝ)^3151
        have hw : |(671091423/1250000000 : ℝ)|=(671091423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182265417/10000000000 : ℝ)|^4175 ≤ (13306635661951/100000000000000 : ℝ)^3151
        have hw : |(-2182265417/10000000000 : ℝ)|=(2182265417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636641241/5000000000 : ℝ)|^4175 ≤ (42831569457791/100000000000000 : ℝ)^3151
        have hw : |(2636641241/5000000000 : ℝ)|=(2636641241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_14 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342182861/2500000000 : ℝ)*x 0 + (5273282311/10000000000 : ℝ)*x 1 + (-1091132783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342182861/2500000000 : ℝ)^4175 ≤ (21930897751227/50000000000000 : ℝ)^3151 := by
    have hnat : (1342182861 : ℕ)^4175*50000000000000^3151 ≤ 21930897751227^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342182861 2500000000 21930897751227 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273282311/10000000000 : ℝ)^4175 ≤ (42831567617497/100000000000000 : ℝ)^3151 := by
    have hnat : (5273282311 : ℕ)^4175*100000000000000^3151 ≤ 42831567617497^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273282311 10000000000 42831567617497 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091132783/5000000000 : ℝ)^4175 ≤ (1663329608219/12500000000000 : ℝ)^3151 := by
    have hnat : (1091132783 : ℕ)^4175*12500000000000^3151 ≤ 1663329608219^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091132783 5000000000 1663329608219 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342182861/2500000000 : ℝ), (5273282311/10000000000 : ℝ), (-1091132783/5000000000 : ℝ)] ![(21930897751227/50000000000000 : ℝ), (42831567617497/100000000000000 : ℝ), (1663329608219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342182861/2500000000 : ℝ)|^4175 ≤ (21930897751227/50000000000000 : ℝ)^3151
        have hw : |(1342182861/2500000000 : ℝ)|=(1342182861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273282311/10000000000 : ℝ)|^4175 ≤ (42831567617497/100000000000000 : ℝ)^3151
        have hw : |(5273282311/10000000000 : ℝ)|=(5273282311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091132783/5000000000 : ℝ)|^4175 ≤ (1663329608219/12500000000000 : ℝ)^3151
        have hw : |(-1091132783/5000000000 : ℝ)|=(1091132783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_box_15 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (847262877/2000000000 : ℝ)*x 0 + (35421181/80000000 : ℝ)*x 1 + (553455879/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847262877/2000000000 : ℝ)^4175 ≤ (16022793091233/50000000000000 : ℝ)^3151 := by
    have hnat : (847262877 : ℕ)^4175*50000000000000^3151 ≤ 16022793091233^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847262877 2000000000 16022793091233 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35421181/80000000 : ℝ)^4175 ≤ (8494302478113/25000000000000 : ℝ)^3151 := by
    have hnat : (35421181 : ℕ)^4175*25000000000000^3151 ≤ 8494302478113^3151*80000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35421181 80000000 8494302478113 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553455879/1250000000 : ℝ)^4175 ≤ (16988601941503/50000000000000 : ℝ)^3151 := by
    have hnat : (553455879 : ℕ)^4175*50000000000000^3151 ≤ 16988601941503^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553455879 1250000000 16988601941503 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847262877/2000000000 : ℝ), (35421181/80000000 : ℝ), (553455879/1250000000 : ℝ)] ![(16022793091233/50000000000000 : ℝ), (8494302478113/25000000000000 : ℝ), (16988601941503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847262877/2000000000 : ℝ)|^4175 ≤ (16022793091233/50000000000000 : ℝ)^3151
        have hw : |(847262877/2000000000 : ℝ)|=(847262877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35421181/80000000 : ℝ)|^4175 ≤ (8494302478113/25000000000000 : ℝ)^3151
        have hw : |(35421181/80000000 : ℝ)|=(35421181/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553455879/1250000000 : ℝ)|^4175 ≤ (16988601941503/50000000000000 : ℝ)^3151
        have hw : |(553455879/1250000000 : ℝ)|=(553455879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62233/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5931/10000 : ℝ) ∧ (39927/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41579/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11373/100000 : ℝ) ^ (8349/2048 : ℝ) ≤ (3540490213297619/25000000000000000000 : ℝ) := by
    have hpowers : (11373/100000 : ℝ)^8349 ≤ (3540490213297619/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11373 : ℕ)^8349*25000000000000000000^2048 ≤ 3540490213297619^2048*100000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373 100000 3540490213297619 25000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11373/100000 : ℝ)) (X := (3540490213297619/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (8349/2048 : ℝ) ≤ (8398232719781663/25000000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^8349 ≤ (8398232719781663/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14057 : ℕ)^8349*25000000000000000000^2048 ≤ 8398232719781663^2048*100000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 8398232719781663 25000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (8398232719781663/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503540490213297619/12500000000000000000 : ℝ) ≤ (200013894165247/200000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (12503540490213297619/12500000000000000000 : ℝ)^2048 ≤ (200013894165247/200000000000000 : ℝ)^8349 := by
      have hnat : (12503540490213297619 : ℕ)^2048*200000000000000^8349 ≤ 200013894165247^8349*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503540490213297619 12500000000000000000 200013894165247 200000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013894165247/200000000000000 : ℝ)) (X := (12503540490213297619/12500000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505969361466539641/12500000000000000000 : ℝ) ≤ (5000585605455363/5000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (12505969361466539641/12500000000000000000 : ℝ)^2048 ≤ (5000585605455363/5000000000000000 : ℝ)^8349 := by
      have hnat : (12505969361466539641 : ℕ)^2048*5000000000000000^8349 ≤ 5000585605455363^8349*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505969361466539641 12500000000000000000 5000585605455363 5000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000585605455363/5000000000000000 : ℝ)) (X := (12505969361466539641/12500000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508398232719781663/12500000000000000000 : ℝ) ≤ (5000823856779551/5000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (12508398232719781663/12500000000000000000 : ℝ)^2048 ≤ (5000823856779551/5000000000000000 : ℝ)^8349 := by
      have hnat : (12508398232719781663 : ℕ)^2048*5000000000000000^8349 ≤ 5000823856779551^8349*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508398232719781663 12500000000000000000 5000823856779551 5000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000823856779551/5000000000000000 : ℝ)) (X := (12508398232719781663/12500000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3540490213297619/25000000000000000000 : ℝ) ≤ ((3353878258467023363/3355000000000000000 : ℝ)+2*(59562831047/33550000000000 : ℝ)*(11373/100000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (3353878258467023363/3355000000000000000 : ℝ)+2*(59562831047/33550000000000 : ℝ)*(11373/100000 : ℝ)=(200013894165247/200000000000000 : ℝ) by norm_num, show 1+2*(3540490213297619/25000000000000000000 : ℝ)=(12503540490213297619/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8398232719781663/25000000000000000000 : ℝ)+(3540490213297619/25000000000000000000 : ℝ) ≤ ((3353878258467023363/3355000000000000000 : ℝ)+(59562831047/33550000000000 : ℝ)*((14057/100000 : ℝ)+(11373/100000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (3353878258467023363/3355000000000000000 : ℝ)+(59562831047/33550000000000 : ℝ)*((14057/100000 : ℝ)+(11373/100000 : ℝ))=(5000585605455363/5000000000000000 : ℝ) by norm_num, show 1+(8398232719781663/25000000000000000000 : ℝ)+(3540490213297619/25000000000000000000 : ℝ)=(12505969361466539641/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8398232719781663/25000000000000000000 : ℝ) ≤ ((3353878258467023363/3355000000000000000 : ℝ)+2*(59562831047/33550000000000 : ℝ)*(14057/100000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (3353878258467023363/3355000000000000000 : ℝ)+2*(59562831047/33550000000000 : ℝ)*(14057/100000 : ℝ)=(5000823856779551/5000000000000000 : ℝ) by norm_num, show 1+2*(8398232719781663/25000000000000000000 : ℝ)=(12508398232719781663/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3353878258467023363/3355000000000000000 : ℝ)*(X 1 0+X 2 0)+(59562831047/33550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (3353878258467023363/3355000000000000000 : ℝ)) (alpha := (59562831047/33550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3353878258467023363/3355000000000000000 : ℝ)*(X 0 1+X 2 1)+(59562831047/33550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (3353878258467023363/3355000000000000000 : ℝ)) (alpha := (59562831047/33550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3353878258467023363/3355000000000000000 : ℝ)*(X 0 2+X 1 2)+(59562831047/33550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (3353878258467023363/3355000000000000000 : ℝ)) (alpha := (59562831047/33550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2033333941/10000000000 : ℝ)*X 0 0+(5376095679/10000000000 : ℝ)*X 0 1+(2688047759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1324030211/2500000000 : ℝ)*X 1 0+(-133864447/625000000 : ℝ)*X 1 1+(1344023821/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296120419/10000000000 : ℝ)*X 2 0+(1075219101/2000000000 : ℝ)*X 2 1+(-85673257/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4469954461/10000000000 : ℝ)*X 0 0+(4310970067/10000000000 : ℝ)*X 0 1+(4310970561/10000000000 : ℝ)*X 0 2+(4469954461/10000000000 : ℝ)*X 1 0+(4310970067/10000000000 : ℝ)*X 1 1+(4310970561/10000000000 : ℝ)*X 1 2+(4469954461/10000000000 : ℝ)*X 2 0+(4310970067/10000000000 : ℝ)*X 2 1+(4310970561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2287525699/10000000000 : ℝ)*X 0 0+(2640664019/5000000000 : ℝ)*X 0 1+(5281327739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681525657/5000000000 : ℝ)*X 1 0+(-2179154433/10000000000 : ℝ)*X 1 1+(2640663861/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363051043/10000000000 : ℝ)*X 2 0+(1320332003/2500000000 : ℝ)*X 2 1+(-272394301/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127405251/5000000000 : ℝ)*X 0 0+(4418521481/10000000000 : ℝ)*X 0 1+(4418521651/10000000000 : ℝ)*X 0 2+(2127405251/5000000000 : ℝ)*X 1 0+(4418521481/10000000000 : ℝ)*X 1 1+(4418521651/10000000000 : ℝ)*X 1 2+(2127405251/5000000000 : ℝ)*X 2 0+(4418521481/10000000000 : ℝ)*X 2 1+(4418521651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-558588319/2500000000 : ℝ)*X 0 0+(2608423769/5000000000 : ℝ)*X 0 1+(5385705719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289329937/10000000000 : ℝ)*X 1 0+(-267247243/1250000000 : ℝ)*X 1 1+(336606583/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289330421/10000000000 : ℝ)*X 2 0+(5385705163/10000000000 : ℝ)*X 2 1+(-427595503/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2245749309/5000000000 : ℝ)*X 0 0+(53750719/125000000 : ℝ)*X 0 1+(2150028931/5000000000 : ℝ)*X 0 2+(2245749309/5000000000 : ℝ)*X 1 0+(53750719/125000000 : ℝ)*X 1 1+(2150028931/5000000000 : ℝ)*X 1 2+(2245749309/5000000000 : ℝ)*X 2 0+(53750719/125000000 : ℝ)*X 2 1+(2150028931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2086816711/10000000000 : ℝ)*X 0 0+(5439308551/10000000000 : ℝ)*X 0 1+(263664117/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671091423/1250000000 : ℝ)*X 1 0+(-2182265417/10000000000 : ℝ)*X 1 1+(2636641241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342182861/2500000000 : ℝ)*X 2 0+(5273282311/10000000000 : ℝ)*X 2 1+(-1091132783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((847262877/2000000000 : ℝ)*X 0 0+(35421181/80000000 : ℝ)*X 0 1+(553455879/1250000000 : ℝ)*X 0 2+(847262877/2000000000 : ℝ)*X 1 0+(35421181/80000000 : ℝ)*X 1 1+(553455879/1250000000 : ℝ)*X 1 2+(847262877/2000000000 : ℝ)*X 2 0+(35421181/80000000 : ℝ)*X 2 1+(553455879/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62233/100000 : ℝ) ≤ (-52195805648598867860914203520089/83875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8943529/20000000000000 : ℝ)*(upper0) + (2650291/6250000000000 : ℝ)*(upper3) + (21195917/50000000000000 : ℝ)*(lower4) + (1966456596018239/50000000000000 : ℝ)*(major0) + (1966456596018239/50000000000000 : ℝ)*(major1) + (6145176862557/156250000000 : ℝ)*(major2) + (4648347623/50000000000000 : ℝ)*(sp1) + (7362318961/100000000000000 : ℝ)*(sp3) + (2630267843562329/50000000000000 : ℝ)*(sp4) + (2630264955880219/50000000000000 : ℝ)*(sp5) + (5260472407606777/100000000000000 : ℝ)*(sp6) + (656505825718871/25000000000000 : ℝ)*(sp7) + (1760665513/50000000000000 : ℝ)*(sp8) + (16700212227/25000000000000 : ℝ)*(sp14) + (525206133038889/20000000000000 : ℝ)*(f.failure) + (1315134802113921/25000000000000 : ℝ)*(f.sum) + (13539052404821/3355000000000000000000000000 : ℝ)*base65 + (899101512833132243/167750000000000000000000000000000 : ℝ)*base68 + (35808933171496139/2096875000000000000000000000000 : ℝ)*base69 + (759701927458632243/167750000000000000000000000000000 : ℝ)*base72 + (90262043655551/3355000000000000000000000000 : ℝ)*base73 + (41740036069546139/2096875000000000000000000000000 : ℝ)*base75 + (2622811483337582243/167750000000000000000000000000000 : ℝ)*base78 + (5096445261282167757/167750000000000000000000000000000 : ℝ)*base79 + (16393646459277/3355000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (20901829/2000000000000000000000 : ℝ)*base89 + (20901829/2000000000000000000000 : ℝ)*base91 + (19098171/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5931/10000 : ℝ) ≤ (248741996511653801300790611787/419375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6124911/25000000000000 : ℝ)*(lower1) + (22484193/20000000000000 : ℝ)*(upper2) + (129920693/100000000000000 : ℝ)*(lower4) + (698189/2500000000000 : ℝ)*(lower5) + (4996637172657/125000000000 : ℝ)*(major0) + (4996637172657/125000000000 : ℝ)*(major1) + (4996637172657/125000000000 : ℝ)*(major2) + (663226684358531/12500000000000 : ℝ)*(sp0) + (2652867481265881/50000000000000 : ℝ)*(sp1) + (5305710143617989/100000000000000 : ℝ)*(sp2) + (2669028640615071/100000000000000 : ℝ)*(sp3) + (21255975809/25000000000000 : ℝ)*(sp9) + (109842817009/100000000000000 : ℝ)*(sp10) + (6511566749/100000000000000 : ℝ)*(sp12) + (2669028640615071/100000000000000 : ℝ)*(f.failure) + (2652909993217499/50000000000000 : ℝ)*(f.sum) + (23909296791/10484375000000000000000000 : ℝ)*base66 + (2534463197305491/419375000000000000000000000000 : ℝ)*base67 + (2811076973403683/209687500000000000000000000000 : ℝ)*base69 + (99680245542433/209687500000000000000000000000 : ℝ)*base71 + (3487682711699/671000000000000000000000000 : ℝ)*base74 + (520487063924933/209687500000000000000000000000 : ℝ)*base75 + (600345863879933/209687500000000000000000000000 : ℝ)*base77 + (111631643160113/13105468750000000000000000000 : ℝ)*base79 + (2767072140161/671000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (46933731/10000000000000000000000 : ℝ)*base89 + (46933731/10000000000000000000000 : ℝ)*base91 + (46933731/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39927/50000 : ℝ) ≤ (33489794000938922337096550407453/41937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55643097/50000000000000 : ℝ)*(upper0) + (535021/50000000000000 : ℝ)*(lower1) + (6296353/2500000000000 : ℝ)*(lower3) + (17012789/6250000000000 : ℝ)*(upper4) + (2232526512300477/50000000000000 : ℝ)*(major0) + (2232526512300477/50000000000000 : ℝ)*(major1) + (893010604920191/20000000000000 : ℝ)*(major2) + (1236230329/100000000000000 : ℝ)*(sp0) + (4248952413/20000000000000 : ℝ)*(sp1) + (78811459949/50000000000000 : ℝ)*(sp3) + (5922142250067289/100000000000000 : ℝ)*(sp8) + (2961061120767777/50000000000000 : ℝ)*(sp9) + (5922143486297619/100000000000000 : ℝ)*(sp10) + (1490593063533797/50000000000000 : ℝ)*(sp11) + (745335937496873/25000000000000 : ℝ)*(f.failure) + (5922143486297619/100000000000000 : ℝ)*(f.sum) + (114259380527/76250000000000000000000000 : ℝ)*base65 + (1051442559032955849/167750000000000000000000000000000 : ℝ)*base68 + (177760249249282333/67100000000000000000000000000000 : ℝ)*base69 + (270378447317705849/167750000000000000000000000000000 : ℝ)*base72 + (2211225052843/305000000000000000000000000 : ℝ)*base73 + (223037576199617667/67100000000000000000000000000000 : ℝ)*base76 + (935550492397805849/167750000000000000000000000000000 : ℝ)*base78 + (964384918111305849/167750000000000000000000000000000 : ℝ)*base80 + (11017769417221/3355000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (17776453/2500000000000000000000 : ℝ)*base89 + (17776453/2500000000000000000000 : ℝ)*base91 + (7223547/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-41579/50000 : ℝ) ≤ (-2789868828504761101546720359/3355000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6392871/2500000000000 : ℝ)*(lower0) + (21813351/50000000000000 : ℝ)*(lower1) + (65803409/100000000000000 : ℝ)*(lower4) + (4500077600123471/100000000000000 : ℝ)*(major0) + (4500077600123471/100000000000000 : ℝ)*(major1) + (281254850007717/6250000000000 : ℝ)*(major2) + (8776382627/100000000000000 : ℝ)*(sp0) + (60073831033/100000000000000 : ℝ)*(sp5) + (9581339679/4000000000000 : ℝ)*(sp6) + (8945895381/20000000000000 : ℝ)*(sp7) + (6023135064294837/100000000000000 : ℝ)*(sp12) + (188221367713951/3125000000000 : ℝ)*(sp13) + (6022904307185489/100000000000000 : ℝ)*(sp14) + (1502342574005567/50000000000000 : ℝ)*(sp15) + (3004729877488039/100000000000000 : ℝ)*(f.failure) + (752892980084683/12500000000000 : ℝ)*(f.sum) + (4114896932291/3355000000000000000000000000 : ℝ)*base65 + (265544121047552973/335500000000000000000000000000000 : ℝ)*base67 + (181291512131429771/20968750000000000000000000000000 : ℝ)*base69 + (5908895610164947027/335500000000000000000000000000000 : ℝ)*base72 + (233912814347511/3355000000000000000000000000 : ℝ)*base73 + (24276817086195229/20968750000000000000000000000000 : ℝ)*base76 + (3619779191650147027/335500000000000000000000000000000 : ℝ)*base78 + (10613228935748352973/335500000000000000000000000000000 : ℝ)*base79 + (13830915987221/3355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (70859979/10000000000000000000000 : ℝ)*base89 + (70859979/10000000000000000000000 : ℝ)*base91 + (29140021/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1157_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5931/10000 : ℝ) else (39927/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41579/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1157_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1157_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5931/10000 : ℝ) else (39927/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41579/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1157_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5931/10000 : ℝ) else (39927/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41579/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
