-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:12.4886+00:00
-- url     : https://prove2.me/submissions/da36b85a-03da-4509-8c1e-a59e45221acf

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
theorem support_rectangle_w1223_s0_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1866436857/10000000000 : ℝ)*x 0 + (3017898887/5000000000 : ℝ)*x 1 + (4790630377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1866436857/10000000000 : ℝ)^263 ≤ (5439203693201/50000000000000 : ℝ)^199 := by
    have hnat : (1866436857 : ℕ)^263*50000000000000^199 ≤ 5439203693201^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866436857 10000000000 5439203693201 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3017898887/5000000000 : ℝ)^263 ≤ (25655896518359/50000000000000 : ℝ)^199 := by
    have hnat : (3017898887 : ℕ)^263*50000000000000^199 ≤ 25655896518359^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017898887 5000000000 25655896518359 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790630377/10000000000 : ℝ)^263 ≤ (7561959911331/20000000000000 : ℝ)^199 := by
    have hnat : (4790630377 : ℕ)^263*20000000000000^199 ≤ 7561959911331^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790630377 10000000000 7561959911331 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1866436857/10000000000 : ℝ), (3017898887/5000000000 : ℝ), (4790630377/10000000000 : ℝ)] ![(5439203693201/50000000000000 : ℝ), (25655896518359/50000000000000 : ℝ), (7561959911331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1866436857/10000000000 : ℝ)|^263 ≤ (5439203693201/50000000000000 : ℝ)^199
        have hw : |(-1866436857/10000000000 : ℝ)|=(1866436857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3017898887/5000000000 : ℝ)|^263 ≤ (25655896518359/50000000000000 : ℝ)^199
        have hw : |(3017898887/5000000000 : ℝ)|=(3017898887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4790630377/10000000000 : ℝ)|^263 ≤ (7561959911331/20000000000000 : ℝ)^199
        have hw : |(4790630377/10000000000 : ℝ)|=(4790630377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s0_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (689028741/1250000000 : ℝ)*x 0 + (-515756889/2000000000 : ℝ)*x 1 + (958126067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689028741/1250000000 : ℝ)^263 ≤ (45513068065247/100000000000000 : ℝ)^199 := by
    have hnat : (689028741 : ℕ)^263*100000000000000^199 ≤ 45513068065247^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689028741 1250000000 45513068065247 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515756889/2000000000 : ℝ)^263 ≤ (3335426560021/20000000000000 : ℝ)^199 := by
    have hnat : (515756889 : ℕ)^263*20000000000000^199 ≤ 3335426560021^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515756889 2000000000 3335426560021 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958126067/2000000000 : ℝ)^263 ≤ (7561959823713/20000000000000 : ℝ)^199 := by
    have hnat : (958126067 : ℕ)^263*20000000000000^199 ≤ 7561959823713^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958126067 2000000000 7561959823713 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689028741/1250000000 : ℝ), (-515756889/2000000000 : ℝ), (958126067/2000000000 : ℝ)] ![(45513068065247/100000000000000 : ℝ), (3335426560021/20000000000000 : ℝ), (7561959823713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689028741/1250000000 : ℝ)|^263 ≤ (45513068065247/100000000000000 : ℝ)^199
        have hw : |(689028741/1250000000 : ℝ)|=(689028741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515756889/2000000000 : ℝ)|^263 ≤ (3335426560021/20000000000000 : ℝ)^199
        have hw : |(-515756889/2000000000 : ℝ)|=(515756889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958126067/2000000000 : ℝ)|^263 ≤ (7561959823713/20000000000000 : ℝ)^199
        have hw : |(958126067/2000000000 : ℝ)|=(958126067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s0_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1378057473/2500000000 : ℝ)*x 0 + (4790630379/10000000000 : ℝ)*x 1 + (-2578784437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378057473/2500000000 : ℝ)^263 ≤ (45513067672409/100000000000000 : ℝ)^199 := by
    have hnat : (1378057473 : ℕ)^263*100000000000000^199 ≤ 45513067672409^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378057473 2500000000 45513067672409 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4790630379/10000000000 : ℝ)^263 ≤ (9452449894379/25000000000000 : ℝ)^199 := by
    have hnat : (4790630379 : ℕ)^263*25000000000000^199 ≤ 9452449894379^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790630379 10000000000 9452449894379 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578784437/10000000000 : ℝ)^263 ≤ (16677132731729/100000000000000 : ℝ)^199 := by
    have hnat : (2578784437 : ℕ)^263*100000000000000^199 ≤ 16677132731729^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578784437 10000000000 16677132731729 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378057473/2500000000 : ℝ), (4790630379/10000000000 : ℝ), (-2578784437/10000000000 : ℝ)] ![(45513067672409/100000000000000 : ℝ), (9452449894379/25000000000000 : ℝ), (16677132731729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378057473/2500000000 : ℝ)|^263 ≤ (45513067672409/100000000000000 : ℝ)^199
        have hw : |(1378057473/2500000000 : ℝ)|=(1378057473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4790630379/10000000000 : ℝ)|^263 ≤ (9452449894379/25000000000000 : ℝ)^199
        have hw : |(4790630379/10000000000 : ℝ)|=(4790630379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2578784437/10000000000 : ℝ)|^263 ≤ (16677132731729/100000000000000 : ℝ)^199
        have hw : |(-2578784437/10000000000 : ℝ)|=(2578784437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s0_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (838903583/2000000000 : ℝ)*x 0 + (3117619337/10000000000 : ℝ)*x 1 + (2817132817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838903583/2000000000 : ℝ)^263 ≤ (31720028464403/100000000000000 : ℝ)^199 := by
    have hnat : (838903583 : ℕ)^263*100000000000000^199 ≤ 31720028464403^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838903583 2000000000 31720028464403 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117619337/10000000000 : ℝ)^263 ≤ (4286102147203/20000000000000 : ℝ)^199 := by
    have hnat : (3117619337 : ℕ)^263*20000000000000^199 ≤ 4286102147203^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117619337 10000000000 4286102147203 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2817132817/5000000000 : ℝ)^263 ≤ (46849460786757/100000000000000 : ℝ)^199 := by
    have hnat : (2817132817 : ℕ)^263*100000000000000^199 ≤ 46849460786757^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2817132817 5000000000 46849460786757 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838903583/2000000000 : ℝ), (3117619337/10000000000 : ℝ), (2817132817/5000000000 : ℝ)] ![(31720028464403/100000000000000 : ℝ), (4286102147203/20000000000000 : ℝ), (46849460786757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838903583/2000000000 : ℝ)|^263 ≤ (31720028464403/100000000000000 : ℝ)^199
        have hw : |(838903583/2000000000 : ℝ)|=(838903583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117619337/10000000000 : ℝ)|^263 ≤ (4286102147203/20000000000000 : ℝ)^199
        have hw : |(3117619337/10000000000 : ℝ)|=(3117619337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2817132817/5000000000 : ℝ)|^263 ≤ (46849460786757/100000000000000 : ℝ)^199
        have hw : |(2817132817/5000000000 : ℝ)|=(2817132817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s0_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-467837183/2500000000 : ℝ)*x 0 + (4822708181/10000000000 : ℝ)*x 1 + (6002586713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467837183/2500000000 : ℝ)^263 ≤ (5458129553863/50000000000000 : ℝ)^199 := by
    have hnat : (467837183 : ℕ)^263*50000000000000^199 ≤ 5458129553863^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467837183 2500000000 5458129553863 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4822708181/10000000000 : ℝ)^263 ≤ (9536188486983/25000000000000 : ℝ)^199 := by
    have hnat : (4822708181 : ℕ)^263*25000000000000^199 ≤ 9536188486983^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822708181 10000000000 9536188486983 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6002586713/10000000000 : ℝ)^263 ≤ (10187797385713/20000000000000 : ℝ)^199 := by
    have hnat : (6002586713 : ℕ)^263*20000000000000^199 ≤ 10187797385713^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002586713 10000000000 10187797385713 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467837183/2500000000 : ℝ), (4822708181/10000000000 : ℝ), (6002586713/10000000000 : ℝ)] ![(5458129553863/50000000000000 : ℝ), (9536188486983/25000000000000 : ℝ), (10187797385713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467837183/2500000000 : ℝ)|^263 ≤ (5458129553863/50000000000000 : ℝ)^199
        have hw : |(-467837183/2500000000 : ℝ)|=(467837183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4822708181/10000000000 : ℝ)|^263 ≤ (9536188486983/25000000000000 : ℝ)^199
        have hw : |(4822708181/10000000000 : ℝ)|=(4822708181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6002586713/10000000000 : ℝ)|^263 ≤ (10187797385713/20000000000000 : ℝ)^199
        have hw : |(6002586713/10000000000 : ℝ)|=(6002586713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s0_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5173519181/10000000000 : ℝ)*x 0 + (-683413107/5000000000 : ℝ)*x 1 + (6002588627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173519181/10000000000 : ℝ)^263 ≤ (10463509407069/25000000000000 : ℝ)^199 := by
    have hnat : (5173519181 : ℕ)^263*25000000000000^199 ≤ 10463509407069^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173519181 10000000000 10463509407069 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683413107/5000000000 : ℝ)^263 ≤ (3603476978397/50000000000000 : ℝ)^199 := by
    have hnat : (683413107 : ℕ)^263*50000000000000^199 ≤ 3603476978397^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683413107 5000000000 3603476978397 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6002588627/10000000000 : ℝ)^263 ≤ (5093900839483/10000000000000 : ℝ)^199 := by
    have hnat : (6002588627 : ℕ)^263*10000000000000^199 ≤ 5093900839483^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002588627 10000000000 5093900839483 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173519181/10000000000 : ℝ), (-683413107/5000000000 : ℝ), (6002588627/10000000000 : ℝ)] ![(10463509407069/25000000000000 : ℝ), (3603476978397/50000000000000 : ℝ), (5093900839483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173519181/10000000000 : ℝ)|^263 ≤ (10463509407069/25000000000000 : ℝ)^199
        have hw : |(5173519181/10000000000 : ℝ)|=(5173519181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-683413107/5000000000 : ℝ)|^263 ≤ (3603476978397/50000000000000 : ℝ)^199
        have hw : |(-683413107/5000000000 : ℝ)|=(683413107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6002588627/10000000000 : ℝ)|^263 ≤ (5093900839483/10000000000000 : ℝ)^199
        have hw : |(6002588627/10000000000 : ℝ)|=(6002588627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s0_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5173520163/10000000000 : ℝ)*x 0 + (3001293573/5000000000 : ℝ)*x 1 + (-1366827091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173520163/10000000000 : ℝ)^263 ≤ (418540481277/1000000000000 : ℝ)^199 := by
    have hnat : (5173520163 : ℕ)^263*1000000000000^199 ≤ 418540481277^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173520163 10000000000 418540481277 1000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3001293573/5000000000 : ℝ)^263 ≤ (50938991784831/100000000000000 : ℝ)^199 := by
    have hnat : (3001293573 : ℕ)^263*100000000000000^199 ≤ 50938991784831^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001293573 5000000000 50938991784831 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366827091/10000000000 : ℝ)^263 ≤ (1441392013639/20000000000000 : ℝ)^199 := by
    have hnat : (1366827091 : ℕ)^263*20000000000000^199 ≤ 1441392013639^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366827091 10000000000 1441392013639 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173520163/10000000000 : ℝ), (3001293573/5000000000 : ℝ), (-1366827091/10000000000 : ℝ)] ![(418540481277/1000000000000 : ℝ), (50938991784831/100000000000000 : ℝ), (1441392013639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173520163/10000000000 : ℝ)|^263 ≤ (418540481277/1000000000000 : ℝ)^199
        have hw : |(5173520163/10000000000 : ℝ)|=(5173520163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3001293573/5000000000 : ℝ)|^263 ≤ (50938991784831/100000000000000 : ℝ)^199
        have hw : |(3001293573/5000000000 : ℝ)|=(3001293573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1366827091/10000000000 : ℝ)|^263 ≤ (1441392013639/20000000000000 : ℝ)^199
        have hw : |(-1366827091/10000000000 : ℝ)|=(1366827091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s0_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2102222359/5000000000 : ℝ)*x 0 + (222777467/400000000 : ℝ)*x 1 + (796184439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102222359/5000000000 : ℝ)^263 ≤ (31819278059999/100000000000000 : ℝ)^199 := by
    have hnat : (2102222359 : ℕ)^263*100000000000000^199 ≤ 31819278059999^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102222359 5000000000 31819278059999 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222777467/400000000 : ℝ)^263 ≤ (9011397977/19531250000 : ℝ)^199 := by
    have hnat : (222777467 : ℕ)^263*19531250000^199 ≤ 9011397977^199*400000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222777467 400000000 9011397977 19531250000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796184439/2500000000 : ℝ)^263 ≤ (440847285797/2000000000000 : ℝ)^199 := by
    have hnat : (796184439 : ℕ)^263*2000000000000^199 ≤ 440847285797^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796184439 2500000000 440847285797 2000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102222359/5000000000 : ℝ), (222777467/400000000 : ℝ), (796184439/2500000000 : ℝ)] ![(31819278059999/100000000000000 : ℝ), (9011397977/19531250000 : ℝ), (440847285797/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102222359/5000000000 : ℝ)|^263 ≤ (31819278059999/100000000000000 : ℝ)^199
        have hw : |(2102222359/5000000000 : ℝ)|=(2102222359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222777467/400000000 : ℝ)|^263 ≤ (9011397977/19531250000 : ℝ)^199
        have hw : |(222777467/400000000 : ℝ)|=(222777467/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796184439/2500000000 : ℝ)|^263 ≤ (440847285797/2000000000000 : ℝ)^199
        have hw : |(796184439/2500000000 : ℝ)|=(796184439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (371/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27507/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8415/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8415 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8415*1^2048 ≤ 0^2048*1^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8415/2048 : ℝ) ≤ (2316912237933957097/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8415 ≤ (2316912237933957097/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8415*100000000000000000000^2048 ≤ 2316912237933957097^2048*5^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2316912237933957097 100000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2316912237933957097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8415 := by
      have hnat : (1 : ℕ)^2048*1^8415 ≤ 1^8415*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102316912237933957097/100000000000000000000 : ℝ) ≤ (10055900185446601/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (102316912237933957097/100000000000000000000 : ℝ)^2048 ≤ (10055900185446601/10000000000000000 : ℝ)^8415 := by
      have hnat : (102316912237933957097 : ℕ)^2048*10000000000000000^8415 ≤ 10055900185446601^8415*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102316912237933957097 100000000000000000000 10055900185446601 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055900185446601/10000000000000000 : ℝ)) (X := (102316912237933957097/100000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52316912237933957097/50000000000000000000 : ℝ) ≤ (5055900185446601/5000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (52316912237933957097/50000000000000000000 : ℝ)^2048 ≤ (5055900185446601/5000000000000000 : ℝ)^8415 := by
      have hnat : (52316912237933957097 : ℕ)^2048*5000000000000000^8415 ≤ 5055900185446601^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52316912237933957097 50000000000000000000 5055900185446601 5000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055900185446601/5000000000000000 : ℝ)) (X := (52316912237933957097/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55900185446601/4000000000000000 : ℝ)*(0 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55900185446601/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2316912237933957097/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55900185446601/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55900185446601/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055900185446601/10000000000000000 : ℝ) by norm_num, show 1+(2316912237933957097/100000000000000000000 : ℝ)+(0 : ℝ)=(102316912237933957097/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2316912237933957097/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55900185446601/4000000000000000 : ℝ)*(2/5 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55900185446601/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055900185446601/5000000000000000 : ℝ) by norm_num, show 1+2*(2316912237933957097/100000000000000000000 : ℝ)=(52316912237933957097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55900185446601/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55900185446601/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55900185446601/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55900185446601/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55900185446601/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55900185446601/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1866436857/10000000000 : ℝ)*X 0 0+(3017898887/5000000000 : ℝ)*X 0 1+(4790630377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689028741/1250000000 : ℝ)*X 1 0+(-515756889/2000000000 : ℝ)*X 1 1+(958126067/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378057473/2500000000 : ℝ)*X 2 0+(4790630379/10000000000 : ℝ)*X 2 1+(-2578784437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838903583/2000000000 : ℝ)*X 0 0+(3117619337/10000000000 : ℝ)*X 0 1+(2817132817/5000000000 : ℝ)*X 0 2+(838903583/2000000000 : ℝ)*X 1 0+(3117619337/10000000000 : ℝ)*X 1 1+(2817132817/5000000000 : ℝ)*X 1 2+(838903583/2000000000 : ℝ)*X 2 0+(3117619337/10000000000 : ℝ)*X 2 1+(2817132817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-467837183/2500000000 : ℝ)*X 0 0+(4822708181/10000000000 : ℝ)*X 0 1+(6002586713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173519181/10000000000 : ℝ)*X 1 0+(-683413107/5000000000 : ℝ)*X 1 1+(6002588627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173520163/10000000000 : ℝ)*X 2 0+(3001293573/5000000000 : ℝ)*X 2 1+(-1366827091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102222359/5000000000 : ℝ)*X 0 0+(222777467/400000000 : ℝ)*X 0 1+(796184439/2500000000 : ℝ)*X 0 2+(2102222359/5000000000 : ℝ)*X 1 0+(222777467/400000000 : ℝ)*X 1 1+(796184439/2500000000 : ℝ)*X 1 2+(2102222359/5000000000 : ℝ)*X 2 0+(222777467/400000000 : ℝ)*X 2 1+(796184439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1320265742757835738377279/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15281501/20000000000000 : ℝ)*(base1) + (1612720987/100000000000000 : ℝ)*(base19) + (374361253/25000000000000 : ℝ)*(base23) + (13753863/12500000000000 : ℝ)*(base24) + (91654403/25000000000000 : ℝ)*(upper3) + (600236390394707/100000000000000 : ℝ)*(major0) + (600236390394707/100000000000000 : ℝ)*(major1) + (600236390394707/100000000000000 : ℝ)*(major2) + (401555163127651/50000000000000 : ℝ)*(sp0) + (401556107123211/50000000000000 : ℝ)*(sp1) + (803112219491493/100000000000000 : ℝ)*(sp2) + (397355851524651/100000000000000 : ℝ)*(sp3) + (3577119611/100000000000000 : ℝ)*(sp4) + (561169111/20000000000000 : ℝ)*(sp7) + (397358733777711/100000000000000 : ℝ)*(f.failure) + (803113826967409/100000000000000 : ℝ)*(f.sum) + (128592956259093/200000000000000000000000000000 : ℝ)*base66 + (2018490921140907/400000000000000000000000000000 : ℝ)*base67 + (1570405137140907/400000000000000000000000000000 : ℝ)*base69 + (380480046859093/400000000000000000000000000000 : ℝ)*base72 + (348107417140907/200000000000000000000000000000 : ℝ)*base73 + (1498575587940907/400000000000000000000000000000 : ℝ)*base75 + (643923497140907/400000000000000000000000000000 : ℝ)*base77 + (280358717940907/400000000000000000000000000000 : ℝ)*base79 + (272317313059093/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (56779339/10000000000000000000000 : ℝ)*base89 + (56779339/10000000000000000000000 : ℝ)*base91 + (56779339/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2328585999415842047949/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92861669/25000000000000 : ℝ)*(base19) + (124553637/20000000000000 : ℝ)*(base23) + (104646943/100000000000000 : ℝ)*(base39) + (134211811/100000000000000 : ℝ)*(upper3) + (7918028326817/1250000000000 : ℝ)*(major0) + (7918028326817/1250000000000 : ℝ)*(major1) + (316721080749209/50000000000000 : ℝ)*(major2) + (728121111/50000000000000 : ℝ)*(sp1) + (1282532017/100000000000000 : ℝ)*(sp2) + (141413741/50000000000000 : ℝ)*(sp3) + (847543248966961/100000000000000 : ℝ)*(sp4) + (847541421278063/100000000000000 : ℝ)*(sp5) + (847541448313701/100000000000000 : ℝ)*(sp6) + (104835216200379/25000000000000 : ℝ)*(sp7) + (209670573814499/50000000000000 : ℝ)*(f.failure) + (847543353613903/100000000000000 : ℝ)*(f.sum) + (400146721249289/200000000000000000000000000000 : ℝ)*base65 + (394437992511391/200000000000000000000000000000 : ℝ)*base68 + (3415974585983/5000000000000000000000000000 : ℝ)*base70 + (358628444911391/200000000000000000000000000000 : ℝ)*base72 + (560916842049289/200000000000000000000000000000 : ℝ)*base73 + (989997975983/5000000000000000000000000000 : ℝ)*base76 + (845259925983/5000000000000000000000000000 : ℝ)*base78 + (8115677184017/5000000000000000000000000000 : ℝ)*base79 + (1511183639017/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (14896049/5000000000000000000000 : ℝ)*base90 + (14896049/5000000000000000000000 : ℝ)*base92 + (64896049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1223_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (371/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27507/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1223_s1_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065234479/10000000000 : ℝ)*x 0 + (5680392069/10000000000 : ℝ)*x 1 + (627347843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065234479/10000000000 : ℝ)^263 ≤ (6217674919131/50000000000000 : ℝ)^199 := by
    have hnat : (2065234479 : ℕ)^263*50000000000000^199 ≤ 6217674919131^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065234479 10000000000 6217674919131 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5680392069/10000000000 : ℝ)^263 ≤ (5919628001001/12500000000000 : ℝ)^199 := by
    have hnat : (5680392069 : ℕ)^263*12500000000000^199 ≤ 5919628001001^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680392069 10000000000 5919628001001 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627347843/1250000000 : ℝ)^263 ≤ (20103813067051/50000000000000 : ℝ)^199 := by
    have hnat : (627347843 : ℕ)^263*50000000000000^199 ≤ 20103813067051^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627347843 1250000000 20103813067051 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065234479/10000000000 : ℝ), (5680392069/10000000000 : ℝ), (627347843/1250000000 : ℝ)] ![(6217674919131/50000000000000 : ℝ), (5919628001001/12500000000000 : ℝ), (20103813067051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065234479/10000000000 : ℝ)|^263 ≤ (6217674919131/50000000000000 : ℝ)^199
        have hw : |(-2065234479/10000000000 : ℝ)|=(2065234479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5680392069/10000000000 : ℝ)|^263 ≤ (5919628001001/12500000000000 : ℝ)^199
        have hw : |(5680392069/10000000000 : ℝ)|=(5680392069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627347843/1250000000 : ℝ)|^263 ≤ (20103813067051/50000000000000 : ℝ)^199
        have hw : |(627347843/1250000000 : ℝ)|=(627347843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s1_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5414688567/10000000000 : ℝ)*x 0 + (-2420836769/10000000000 : ℝ)*x 1 + (156836961/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414688567/10000000000 : ℝ)^263 ≤ (173639532241/390625000000 : ℝ)^199 := by
    have hnat : (5414688567 : ℕ)^263*390625000000^199 ≤ 173639532241^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414688567 10000000000 173639532241 390625000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2420836769/10000000000 : ℝ)^263 ≤ (7670326757707/50000000000000 : ℝ)^199 := by
    have hnat : (2420836769 : ℕ)^263*50000000000000^199 ≤ 7670326757707^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420836769 10000000000 7670326757707 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156836961/312500000 : ℝ)^263 ≤ (20103813109403/50000000000000 : ℝ)^199 := by
    have hnat : (156836961 : ℕ)^263*50000000000000^199 ≤ 20103813109403^199*312500000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156836961 312500000 20103813109403 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414688567/10000000000 : ℝ), (-2420836769/10000000000 : ℝ), (156836961/312500000 : ℝ)] ![(173639532241/390625000000 : ℝ), (7670326757707/50000000000000 : ℝ), (20103813109403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414688567/10000000000 : ℝ)|^263 ≤ (173639532241/390625000000 : ℝ)^199
        have hw : |(5414688567/10000000000 : ℝ)|=(5414688567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2420836769/10000000000 : ℝ)|^263 ≤ (7670326757707/50000000000000 : ℝ)^199
        have hw : |(-2420836769/10000000000 : ℝ)|=(2420836769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156836961/312500000 : ℝ)|^263 ≤ (20103813109403/50000000000000 : ℝ)^199
        have hw : |(156836961/312500000 : ℝ)|=(156836961/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s1_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2707344293/5000000000 : ℝ)*x 0 + (2509391377/5000000000 : ℝ)*x 1 + (-2420836741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707344293/5000000000 : ℝ)^263 ≤ (138911626437/312500000000 : ℝ)^199 := by
    have hnat : (2707344293 : ℕ)^263*312500000000^199 ≤ 138911626437^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707344293 5000000000 138911626437 312500000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509391377/5000000000 : ℝ)^263 ≤ (20103813119991/50000000000000 : ℝ)^199 := by
    have hnat : (2509391377 : ℕ)^263*50000000000000^199 ≤ 20103813119991^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509391377 5000000000 20103813119991 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2420836741/10000000000 : ℝ)^263 ≤ (3835163320229/25000000000000 : ℝ)^199 := by
    have hnat : (2420836741 : ℕ)^263*25000000000000^199 ≤ 3835163320229^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420836741 10000000000 3835163320229 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707344293/5000000000 : ℝ), (2509391377/5000000000 : ℝ), (-2420836741/10000000000 : ℝ)] ![(138911626437/312500000000 : ℝ), (20103813119991/50000000000000 : ℝ), (3835163320229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707344293/5000000000 : ℝ)|^263 ≤ (138911626437/312500000000 : ℝ)^199
        have hw : |(2707344293/5000000000 : ℝ)|=(2707344293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509391377/5000000000 : ℝ)|^263 ≤ (20103813119991/50000000000000 : ℝ)^199
        have hw : |(2509391377/5000000000 : ℝ)|=(2509391377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2420836741/10000000000 : ℝ)|^263 ≤ (3835163320229/25000000000000 : ℝ)^199
        have hw : |(-2420836741/10000000000 : ℝ)|=(2420836741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s1_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1077626077/2500000000 : ℝ)*x 0 + (3692023563/10000000000 : ℝ)*x 1 + (157163223/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077626077/2500000000 : ℝ)^263 ≤ (1644217934391/5000000000000 : ℝ)^199 := by
    have hnat : (1077626077 : ℕ)^263*5000000000000^199 ≤ 1644217934391^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077626077 2500000000 1644217934391 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3692023563/10000000000 : ℝ)^263 ≤ (26797435635031/100000000000000 : ℝ)^199 := by
    have hnat : (3692023563 : ℕ)^263*100000000000000^199 ≤ 26797435635031^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692023563 10000000000 26797435635031 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157163223/312500000 : ℝ)^263 ≤ (40318205653887/100000000000000 : ℝ)^199 := by
    have hnat : (157163223 : ℕ)^263*100000000000000^199 ≤ 40318205653887^199*312500000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157163223 312500000 40318205653887 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077626077/2500000000 : ℝ), (3692023563/10000000000 : ℝ), (157163223/312500000 : ℝ)] ![(1644217934391/5000000000000 : ℝ), (26797435635031/100000000000000 : ℝ), (40318205653887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077626077/2500000000 : ℝ)|^263 ≤ (1644217934391/5000000000000 : ℝ)^199
        have hw : |(1077626077/2500000000 : ℝ)|=(1077626077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3692023563/10000000000 : ℝ)|^263 ≤ (26797435635031/100000000000000 : ℝ)^199
        have hw : |(3692023563/10000000000 : ℝ)|=(3692023563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157163223/312500000 : ℝ)|^263 ≤ (40318205653887/100000000000000 : ℝ)^199
        have hw : |(157163223/312500000 : ℝ)|=(157163223/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s1_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065929583/10000000000 : ℝ)*x 0 + (5027535369/10000000000 : ℝ)*x 1 + (5671474503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065929583/10000000000 : ℝ)^263 ≤ (6220440807241/50000000000000 : ℝ)^199 := by
    have hnat : (2065929583 : ℕ)^263*50000000000000^199 ≤ 6220440807241^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065929583 10000000000 6220440807241 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027535369/10000000000 : ℝ)^263 ≤ (8060064929031/20000000000000 : ℝ)^199 := by
    have hnat : (5027535369 : ℕ)^263*20000000000000^199 ≤ 8060064929031^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027535369 10000000000 8060064929031 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5671474503/10000000000 : ℝ)^263 ≤ (2953674607647/6250000000000 : ℝ)^199 := by
    have hnat : (5671474503 : ℕ)^263*6250000000000^199 ≤ 2953674607647^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671474503 10000000000 2953674607647 6250000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065929583/10000000000 : ℝ), (5027535369/10000000000 : ℝ), (5671474503/10000000000 : ℝ)] ![(6220440807241/50000000000000 : ℝ), (8060064929031/20000000000000 : ℝ), (2953674607647/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065929583/10000000000 : ℝ)|^263 ≤ (6220440807241/50000000000000 : ℝ)^199
        have hw : |(-2065929583/10000000000 : ℝ)|=(2065929583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5027535369/10000000000 : ℝ)|^263 ≤ (8060064929031/20000000000000 : ℝ)^199
        have hw : |(5027535369/10000000000 : ℝ)|=(5027535369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5671474503/10000000000 : ℝ)|^263 ≤ (2953674607647/6250000000000 : ℝ)^199
        have hw : |(5671474503/10000000000 : ℝ)|=(5671474503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s1_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2622196313/5000000000 : ℝ)*x 0 + (-176815091/1000000000 : ℝ)*x 1 + (708933467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622196313/5000000000 : ℝ)^263 ≤ (42613471959597/100000000000000 : ℝ)^199 := by
    have hnat : (2622196313 : ℕ)^263*100000000000000^199 ≤ 42613471959597^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622196313 5000000000 42613471959597 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176815091/1000000000 : ℝ)^263 ≤ (10127808826183/100000000000000 : ℝ)^199 := by
    have hnat : (176815091 : ℕ)^263*100000000000000^199 ≤ 10127808826183^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176815091 1000000000 10127808826183 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708933467/1250000000 : ℝ)^263 ≤ (11814679800049/25000000000000 : ℝ)^199 := by
    have hnat : (708933467 : ℕ)^263*25000000000000^199 ≤ 11814679800049^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708933467 1250000000 11814679800049 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622196313/5000000000 : ℝ), (-176815091/1000000000 : ℝ), (708933467/1250000000 : ℝ)] ![(42613471959597/100000000000000 : ℝ), (10127808826183/100000000000000 : ℝ), (11814679800049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622196313/5000000000 : ℝ)|^263 ≤ (42613471959597/100000000000000 : ℝ)^199
        have hw : |(2622196313/5000000000 : ℝ)|=(2622196313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176815091/1000000000 : ℝ)|^263 ≤ (10127808826183/100000000000000 : ℝ)^199
        have hw : |(-176815091/1000000000 : ℝ)|=(176815091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708933467/1250000000 : ℝ)|^263 ≤ (11814679800049/25000000000000 : ℝ)^199
        have hw : |(708933467/1250000000 : ℝ)|=(708933467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s1_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5244392713/10000000000 : ℝ)*x 0 + (5671468233/10000000000 : ℝ)*x 1 + (-1768150063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244392713/10000000000 : ℝ)^263 ≤ (4261347289387/10000000000000 : ℝ)^199 := by
    have hnat : (5244392713 : ℕ)^263*10000000000000^199 ≤ 4261347289387^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244392713 10000000000 4261347289387 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671468233/10000000000 : ℝ)^263 ≤ (47258724673449/100000000000000 : ℝ)^199 := by
    have hnat : (5671468233 : ℕ)^263*100000000000000^199 ≤ 47258724673449^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671468233 10000000000 47258724673449 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768150063/10000000000 : ℝ)^263 ≤ (202556048287/2000000000000 : ℝ)^199 := by
    have hnat : (1768150063 : ℕ)^263*2000000000000^199 ≤ 202556048287^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768150063 10000000000 202556048287 2000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244392713/10000000000 : ℝ), (5671468233/10000000000 : ℝ), (-1768150063/10000000000 : ℝ)] ![(4261347289387/10000000000000 : ℝ), (47258724673449/100000000000000 : ℝ), (202556048287/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244392713/10000000000 : ℝ)|^263 ≤ (4261347289387/10000000000000 : ℝ)^199
        have hw : |(5244392713/10000000000 : ℝ)|=(5244392713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671468233/10000000000 : ℝ)|^263 ≤ (47258724673449/100000000000000 : ℝ)^199
        have hw : |(5671468233/10000000000 : ℝ)|=(5671468233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1768150063/10000000000 : ℝ)|^263 ≤ (202556048287/2000000000000 : ℝ)^199
        have hw : |(-1768150063/10000000000 : ℝ)|=(1768150063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s1_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2155958111/5000000000 : ℝ)*x 0 + (1252881617/2500000000 : ℝ)*x 1 + (3710060471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155958111/5000000000 : ℝ)^263 ≤ (32898594920661/100000000000000 : ℝ)^199 := by
    have hnat : (2155958111 : ℕ)^263*100000000000000^199 ≤ 32898594920661^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155958111 5000000000 32898594920661 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252881617/2500000000 : ℝ)^263 ≤ (40130814768481/100000000000000 : ℝ)^199 := by
    have hnat : (1252881617 : ℕ)^263*100000000000000^199 ≤ 40130814768481^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252881617 2500000000 40130814768481 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3710060471/10000000000 : ℝ)^263 ≤ (13485295150929/50000000000000 : ℝ)^199 := by
    have hnat : (3710060471 : ℕ)^263*50000000000000^199 ≤ 13485295150929^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3710060471 10000000000 13485295150929 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155958111/5000000000 : ℝ), (1252881617/2500000000 : ℝ), (3710060471/10000000000 : ℝ)] ![(32898594920661/100000000000000 : ℝ), (40130814768481/100000000000000 : ℝ), (13485295150929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155958111/5000000000 : ℝ)|^263 ≤ (32898594920661/100000000000000 : ℝ)^199
        have hw : |(2155958111/5000000000 : ℝ)|=(2155958111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1252881617/2500000000 : ℝ)|^263 ≤ (40130814768481/100000000000000 : ℝ)^199
        have hw : |(1252881617/2500000000 : ℝ)|=(1252881617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3710060471/10000000000 : ℝ)|^263 ≤ (13485295150929/50000000000000 : ℝ)^199
        have hw : |(3710060471/10000000000 : ℝ)|=(3710060471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6091/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (251/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (371/50000 : ℝ) ^ (8415/2048 : ℝ) ≤ (17771778433/10000000000000000000 : ℝ) := by
    have hpowers : (371/50000 : ℝ)^8415 ≤ (17771778433/10000000000000000000 : ℝ)^2048 := by
      have hnat : (371 : ℕ)^8415*10000000000000000000^2048 ≤ 17771778433^2048*50000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        371 50000 17771778433 10000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (371/50000 : ℝ)) (X := (17771778433/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27507/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (497434293043722627/100000000000000000000 : ℝ) := by
    have hpowers : (27507/100000 : ℝ)^8415 ≤ (497434293043722627/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27507 : ℕ)^8415*100000000000000000000^2048 ≤ 497434293043722627^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27507 100000 497434293043722627 100000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27507/100000 : ℝ)) (X := (497434293043722627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000017771778433/5000000000000000000 : ℝ) ≤ (10000000008650411/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (5000000017771778433/5000000000000000000 : ℝ)^2048 ≤ (10000000008650411/10000000000000000 : ℝ)^8415 := by
      have hnat : (5000000017771778433 : ℕ)^2048*10000000000000000^8415 ≤ 10000000008650411^8415*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000017771778433 5000000000000000000 10000000008650411 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000008650411/10000000000000000 : ℝ)) (X := (5000000017771778433/5000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100497434470761506957/100000000000000000000 : ℝ) ≤ (10012083591529219/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (100497434470761506957/100000000000000000000 : ℝ)^2048 ≤ (10012083591529219/10000000000000000 : ℝ)^8415 := by
      have hnat : (100497434470761506957 : ℕ)^2048*10000000000000000^8415 ≤ 10012083591529219^8415*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100497434470761506957 100000000000000000000 10012083591529219 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012083591529219/10000000000000000 : ℝ)) (X := (100497434470761506957/100000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50497434293043722627/50000000000000000000 : ℝ) ≤ (10024167174408027/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50497434293043722627/50000000000000000000 : ℝ)^2048 ≤ (10024167174408027/10000000000000000 : ℝ)^8415 := by
      have hnat : (50497434293043722627 : ℕ)^2048*10000000000000000^8415 ≤ 10024167174408027^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50497434293043722627 50000000000000000000 10024167174408027 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024167174408027/10000000000000000 : ℝ)) (X := (50497434293043722627/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(17771778433/10000000000000000000 : ℝ) ≤ ((5049661664047850931/5050000000000000000 : ℝ)+2*(1510447859851/334562500000000 : ℝ)*(371/50000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (5049661664047850931/5050000000000000000 : ℝ)+2*(1510447859851/334562500000000 : ℝ)*(371/50000 : ℝ)=(10000000008650411/10000000000000000 : ℝ) by norm_num, show 1+2*(17771778433/10000000000000000000 : ℝ)=(5000000017771778433/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(497434293043722627/100000000000000000000 : ℝ)+(17771778433/10000000000000000000 : ℝ) ≤ ((5049661664047850931/5050000000000000000 : ℝ)+(1510447859851/334562500000000 : ℝ)*((27507/100000 : ℝ)+(371/50000 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (5049661664047850931/5050000000000000000 : ℝ)+(1510447859851/334562500000000 : ℝ)*((27507/100000 : ℝ)+(371/50000 : ℝ))=(10012083591529219/10000000000000000 : ℝ) by norm_num, show 1+(497434293043722627/100000000000000000000 : ℝ)+(17771778433/10000000000000000000 : ℝ)=(100497434470761506957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(497434293043722627/100000000000000000000 : ℝ) ≤ ((5049661664047850931/5050000000000000000 : ℝ)+2*(1510447859851/334562500000000 : ℝ)*(27507/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (5049661664047850931/5050000000000000000 : ℝ)+2*(1510447859851/334562500000000 : ℝ)*(27507/100000 : ℝ)=(10024167174408027/10000000000000000 : ℝ) by norm_num, show 1+2*(497434293043722627/100000000000000000000 : ℝ)=(50497434293043722627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5049661664047850931/5050000000000000000 : ℝ)*(X 1 0+X 2 0)+(1510447859851/334562500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (371/50000 : ℝ)) (hi := (27507/100000 : ℝ)) (c := (5049661664047850931/5050000000000000000 : ℝ)) (alpha := (1510447859851/334562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5049661664047850931/5050000000000000000 : ℝ)*(X 0 1+X 2 1)+(1510447859851/334562500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (371/50000 : ℝ)) (hi := (27507/100000 : ℝ)) (c := (5049661664047850931/5050000000000000000 : ℝ)) (alpha := (1510447859851/334562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5049661664047850931/5050000000000000000 : ℝ)*(X 0 2+X 1 2)+(1510447859851/334562500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (371/50000 : ℝ)) (hi := (27507/100000 : ℝ)) (c := (5049661664047850931/5050000000000000000 : ℝ)) (alpha := (1510447859851/334562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2065234479/10000000000 : ℝ)*X 0 0+(5680392069/10000000000 : ℝ)*X 0 1+(627347843/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414688567/10000000000 : ℝ)*X 1 0+(-2420836769/10000000000 : ℝ)*X 1 1+(156836961/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2707344293/5000000000 : ℝ)*X 2 0+(2509391377/5000000000 : ℝ)*X 2 1+(-2420836741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077626077/2500000000 : ℝ)*X 0 0+(3692023563/10000000000 : ℝ)*X 0 1+(157163223/312500000 : ℝ)*X 0 2+(1077626077/2500000000 : ℝ)*X 1 0+(3692023563/10000000000 : ℝ)*X 1 1+(157163223/312500000 : ℝ)*X 1 2+(1077626077/2500000000 : ℝ)*X 2 0+(3692023563/10000000000 : ℝ)*X 2 1+(157163223/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2065929583/10000000000 : ℝ)*X 0 0+(5027535369/10000000000 : ℝ)*X 0 1+(5671474503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622196313/5000000000 : ℝ)*X 1 0+(-176815091/1000000000 : ℝ)*X 1 1+(708933467/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244392713/10000000000 : ℝ)*X 2 0+(5671468233/10000000000 : ℝ)*X 2 1+(-1768150063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155958111/5000000000 : ℝ)*X 0 0+(1252881617/2500000000 : ℝ)*X 0 1+(3710060471/10000000000 : ℝ)*X 0 2+(2155958111/5000000000 : ℝ)*X 1 0+(1252881617/2500000000 : ℝ)*X 1 1+(3710060471/10000000000 : ℝ)*X 1 2+(2155958111/5000000000 : ℝ)*X 2 0+(1252881617/2500000000 : ℝ)*X 2 1+(3710060471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76035736195727563639723100577/13382500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67574219/100000000000000 : ℝ)*(base1) + (621662163/50000000000000 : ℝ)*(base19) + (1248628063/100000000000000 : ℝ)*(base23) + (136097439/100000000000000 : ℝ)*(upper3) + (147767931/100000000000000 : ℝ)*(upper5) + (1129659067769271/100000000000000 : ℝ)*(major0) + (1129659067769271/100000000000000 : ℝ)*(major1) + (1129659067769271/100000000000000 : ℝ)*(major2) + (1511472586283849/100000000000000 : ℝ)*(sp0) + (1511478177947859/100000000000000 : ℝ)*(sp1) + (755739086322061/50000000000000 : ℝ)*(sp2) + (373917484543231/50000000000000 : ℝ)*(sp3) + (1380512511/20000000000000 : ℝ)*(sp4) + (348821471/10000000000000 : ℝ)*(sp7) + (74783852487539/10000000000000 : ℝ)*(f.failure) + (302295884254437/20000000000000 : ℝ)*(f.sum) + (67457521052129/16728125000000000000000000000 : ℝ)*base66 + (79115372256374511047/26765000000000000000000000000000000 : ℝ)*base68 + (78957466812639511047/26765000000000000000000000000000000 : ℝ)*base70 + (44055422526729511047/26765000000000000000000000000000000 : ℝ)*base72 + (628374251058407/133825000000000000000000000000 : ℝ)*base74 + (159584115862094511047/26765000000000000000000000000000000 : ℝ)*base76 + (75744203971564511047/26765000000000000000000000000000000 : ℝ)*base78 + (26473183686554511047/26765000000000000000000000000000000 : ℝ)*base80 + (41473189522127/8364062500000000000000000000 : ℝ)*base82 + (3157089/1000000000000000000000 : ℝ)*base90 + (3157089/1000000000000000000000 : ℝ)*base92 + (3157089/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (697389403837221533524856937/63125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142582337/20000000000000 : ℝ)*(base19) + (2161138329/100000000000000 : ℝ)*(base23) + (30693857/25000000000000 : ℝ)*(lower3) + (155019921/25000000000000 : ℝ)*(lower4) + (290165514114203/25000000000000 : ℝ)*(major0) + (290165514114203/25000000000000 : ℝ)*(major1) + (290165514114203/25000000000000 : ℝ)*(major2) + (5143064519/50000000000000 : ℝ)*(sp0) + (397128197/50000000000000 : ℝ)*(sp1) + (1637648037/20000000000000 : ℝ)*(sp2) + (1552950839268369/100000000000000 : ℝ)*(sp4) + (97059976139333/6250000000000 : ℝ)*(sp5) + (388237694004723/25000000000000 : ℝ)*(sp6) + (38418130962889/5000000000000 : ℝ)*(sp7) + (38418130962889/5000000000000 : ℝ)*(f.failure) + (776480562698703/50000000000000 : ℝ)*(f.sum) + (993345196206521/133825000000000000000000000000 : ℝ)*base65 + (49736534116191081371/6691250000000000000000000000000000 : ℝ)*base68 + (14814006656076081371/6691250000000000000000000000000000 : ℝ)*base70 + (15219895385239831371/6691250000000000000000000000000000 : ℝ)*base72 + (187755267699773/66912500000000000000000000000 : ℝ)*base73 + (65963673539077331371/6691250000000000000000000000000000 : ℝ)*base76 + (33303531669039831371/6691250000000000000000000000000000 : ℝ)*base78 + (2077333439539831371/6691250000000000000000000000000000 : ℝ)*base80 + (818055688516421/133825000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (589939/500000000000000000000 : ℝ)*base90 + (589939/500000000000000000000 : ℝ)*base92 + (589939/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1223_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6091/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (251/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1223_s2_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057114059/5000000000 : ℝ)*x 0 + (1099212921/2000000000 : ℝ)*x 1 + (2585941201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057114059/5000000000 : ℝ)^263 ≤ (3206677321163/25000000000000 : ℝ)^199 := by
    have hnat : (1057114059 : ℕ)^263*25000000000000^199 ≤ 3206677321163^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057114059 5000000000 3206677321163 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099212921/2000000000 : ℝ)^263 ≤ (45336752416951/100000000000000 : ℝ)^199 := by
    have hnat : (1099212921 : ℕ)^263*100000000000000^199 ≤ 45336752416951^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099212921 2000000000 45336752416951 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585941201/5000000000 : ℝ)^263 ≤ (41836538278311/100000000000000 : ℝ)^199 := by
    have hnat : (2585941201 : ℕ)^263*100000000000000^199 ≤ 41836538278311^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585941201 5000000000 41836538278311 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057114059/5000000000 : ℝ), (1099212921/2000000000 : ℝ), (2585941201/5000000000 : ℝ)] ![(3206677321163/25000000000000 : ℝ), (45336752416951/100000000000000 : ℝ), (41836538278311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057114059/5000000000 : ℝ)|^263 ≤ (3206677321163/25000000000000 : ℝ)^199
        have hw : |(-1057114059/5000000000 : ℝ)|=(1057114059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099212921/2000000000 : ℝ)|^263 ≤ (45336752416951/100000000000000 : ℝ)^199
        have hw : |(1099212921/2000000000 : ℝ)|=(1099212921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585941201/5000000000 : ℝ)|^263 ≤ (41836538278311/100000000000000 : ℝ)^199
        have hw : |(2585941201/5000000000 : ℝ)|=(2585941201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s2_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (537046299/1000000000 : ℝ)*x 0 + (-2282264519/10000000000 : ℝ)*x 1 + (161621323/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537046299/1000000000 : ℝ)^263 ≤ (2198625867883/5000000000000 : ℝ)^199 := by
    have hnat : (537046299 : ℕ)^263*5000000000000^199 ≤ 2198625867883^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537046299 1000000000 2198625867883 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282264519/10000000000 : ℝ)^263 ≤ (2838189010387/20000000000000 : ℝ)^199 := by
    have hnat : (2282264519 : ℕ)^263*20000000000000^199 ≤ 2838189010387^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282264519 10000000000 2838189010387 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161621323/312500000 : ℝ)^263 ≤ (20918268786359/50000000000000 : ℝ)^199 := by
    have hnat : (161621323 : ℕ)^263*50000000000000^199 ≤ 20918268786359^199*312500000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161621323 312500000 20918268786359 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537046299/1000000000 : ℝ), (-2282264519/10000000000 : ℝ), (161621323/312500000 : ℝ)] ![(2198625867883/5000000000000 : ℝ), (2838189010387/20000000000000 : ℝ), (20918268786359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537046299/1000000000 : ℝ)|^263 ≤ (2198625867883/5000000000000 : ℝ)^199
        have hw : |(537046299/1000000000 : ℝ)|=(537046299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282264519/10000000000 : ℝ)|^263 ≤ (2838189010387/20000000000000 : ℝ)^199
        have hw : |(-2282264519/10000000000 : ℝ)|=(2282264519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161621323/312500000 : ℝ)|^263 ≤ (20918268786359/50000000000000 : ℝ)^199
        have hw : |(161621323/312500000 : ℝ)|=(161621323/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s2_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1342615699/2500000000 : ℝ)*x 0 + (1292970627/2500000000 : ℝ)*x 1 + (-2282264551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342615699/2500000000 : ℝ)^263 ≤ (21986257629181/50000000000000 : ℝ)^199 := by
    have hnat : (1342615699 : ℕ)^263*50000000000000^199 ≤ 21986257629181^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342615699 2500000000 21986257629181 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292970627/2500000000 : ℝ)^263 ≤ (20918269705767/50000000000000 : ℝ)^199 := by
    have hnat : (1292970627 : ℕ)^263*50000000000000^199 ≤ 20918269705767^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292970627 2500000000 20918269705767 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282264551/10000000000 : ℝ)^263 ≤ (141909453149/1000000000000 : ℝ)^199 := by
    have hnat : (2282264551 : ℕ)^263*1000000000000^199 ≤ 141909453149^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282264551 10000000000 141909453149 1000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342615699/2500000000 : ℝ), (1292970627/2500000000 : ℝ), (-2282264551/10000000000 : ℝ)] ![(21986257629181/50000000000000 : ℝ), (20918269705767/50000000000000 : ℝ), (141909453149/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342615699/2500000000 : ℝ)|^263 ≤ (21986257629181/50000000000000 : ℝ)^199
        have hw : |(1342615699/2500000000 : ℝ)|=(1342615699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292970627/2500000000 : ℝ)|^263 ≤ (20918269705767/50000000000000 : ℝ)^199
        have hw : |(1292970627/2500000000 : ℝ)|=(1292970627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282264551/10000000000 : ℝ)|^263 ≤ (141909453149/1000000000000 : ℝ)^199
        have hw : |(-2282264551/10000000000 : ℝ)|=(2282264551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s2_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2172153167/5000000000 : ℝ)*x 0 + (805742969/2000000000 : ℝ)*x 1 + (468392981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172153167/5000000000 : ℝ)^263 ≤ (6645118652099/20000000000000 : ℝ)^199 := by
    have hnat : (2172153167 : ℕ)^263*20000000000000^199 ≤ 6645118652099^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172153167 5000000000 6645118652099 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805742969/2000000000 : ℝ)^263 ≤ (30073564750721/100000000000000 : ℝ)^199 := by
    have hnat : (805742969 : ℕ)^263*100000000000000^199 ≤ 30073564750721^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805742969 2000000000 30073564750721 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468392981/1000000000 : ℝ)^263 ≤ (36700841975241/100000000000000 : ℝ)^199 := by
    have hnat : (468392981 : ℕ)^263*100000000000000^199 ≤ 36700841975241^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468392981 1000000000 36700841975241 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172153167/5000000000 : ℝ), (805742969/2000000000 : ℝ), (468392981/1000000000 : ℝ)] ![(6645118652099/20000000000000 : ℝ), (30073564750721/100000000000000 : ℝ), (36700841975241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172153167/5000000000 : ℝ)|^263 ≤ (6645118652099/20000000000000 : ℝ)^199
        have hw : |(2172153167/5000000000 : ℝ)|=(2172153167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805742969/2000000000 : ℝ)|^263 ≤ (30073564750721/100000000000000 : ℝ)^199
        have hw : |(805742969/2000000000 : ℝ)|=(805742969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468392981/1000000000 : ℝ)|^263 ≤ (36700841975241/100000000000000 : ℝ)^199
        have hw : |(468392981/1000000000 : ℝ)|=(468392981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s2_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114310593/10000000000 : ℝ)*x 0 + (1293498527/2500000000 : ℝ)*x 1 + (274696643/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114310593/10000000000 : ℝ)^263 ≤ (801710660837/6250000000000 : ℝ)^199 := by
    have hnat : (2114310593 : ℕ)^263*6250000000000^199 ≤ 801710660837^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114310593 10000000000 801710660837 6250000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293498527/2500000000 : ℝ)^263 ≤ (1674364622579/4000000000000 : ℝ)^199 := by
    have hnat : (1293498527 : ℕ)^263*4000000000000^199 ≤ 1674364622579^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293498527 2500000000 1674364622579 4000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274696643/500000000 : ℝ)^263 ≤ (45313513846261/100000000000000 : ℝ)^199 := by
    have hnat : (274696643 : ℕ)^263*100000000000000^199 ≤ 45313513846261^199*500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274696643 500000000 45313513846261 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114310593/10000000000 : ℝ), (1293498527/2500000000 : ℝ), (274696643/500000000 : ℝ)] ![(801710660837/6250000000000 : ℝ), (1674364622579/4000000000000 : ℝ), (45313513846261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114310593/10000000000 : ℝ)|^263 ≤ (801710660837/6250000000000 : ℝ)^199
        have hw : |(-2114310593/10000000000 : ℝ)|=(2114310593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293498527/2500000000 : ℝ)|^263 ≤ (1674364622579/4000000000000 : ℝ)^199
        have hw : |(1293498527/2500000000 : ℝ)|=(1293498527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274696643/500000000 : ℝ)|^263 ≤ (45313513846261/100000000000000 : ℝ)^199
        have hw : |(274696643/500000000 : ℝ)|=(274696643/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s2_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5287773891/10000000000 : ℝ)*x 0 + (-196021383/1000000000 : ℝ)*x 1 + (5493932897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287773891/10000000000 : ℝ)^263 ≤ (1723198069769/4000000000000 : ℝ)^199 := by
    have hnat : (5287773891 : ℕ)^263*4000000000000^199 ≤ 1723198069769^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287773891 10000000000 1723198069769 4000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196021383/1000000000 : ℝ)^263 ≤ (2321306800973/20000000000000 : ℝ)^199 := by
    have hnat : (196021383 : ℕ)^263*20000000000000^199 ≤ 2321306800973^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196021383 1000000000 2321306800973 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493932897/10000000000 : ℝ)^263 ≤ (2265675712479/5000000000000 : ℝ)^199 := by
    have hnat : (5493932897 : ℕ)^263*5000000000000^199 ≤ 2265675712479^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493932897 10000000000 2265675712479 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287773891/10000000000 : ℝ), (-196021383/1000000000 : ℝ), (5493932897/10000000000 : ℝ)] ![(1723198069769/4000000000000 : ℝ), (2321306800973/20000000000000 : ℝ), (2265675712479/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287773891/10000000000 : ℝ)|^263 ≤ (1723198069769/4000000000000 : ℝ)^199
        have hw : |(5287773891/10000000000 : ℝ)|=(5287773891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196021383/1000000000 : ℝ)|^263 ≤ (2321306800973/20000000000000 : ℝ)^199
        have hw : |(-196021383/1000000000 : ℝ)|=(196021383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493932897/10000000000 : ℝ)|^263 ≤ (2265675712479/5000000000000 : ℝ)^199
        have hw : |(5493932897/10000000000 : ℝ)|=(5493932897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s2_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (660971759/1250000000 : ℝ)*x 0 + (2746966473/5000000000 : ℝ)*x 1 + (-1960213511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660971759/1250000000 : ℝ)^263 ≤ (21539976846549/50000000000000 : ℝ)^199 := by
    have hnat : (660971759 : ℕ)^263*50000000000000^199 ≤ 21539976846549^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660971759 1250000000 21539976846549 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746966473/5000000000 : ℝ)^263 ≤ (22656757391853/50000000000000 : ℝ)^199 := by
    have hnat : (2746966473 : ℕ)^263*50000000000000^199 ≤ 22656757391853^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746966473 5000000000 22656757391853 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960213511/10000000000 : ℝ)^263 ≤ (1160653150859/10000000000000 : ℝ)^199 := by
    have hnat : (1960213511 : ℕ)^263*10000000000000^199 ≤ 1160653150859^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960213511 10000000000 1160653150859 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660971759/1250000000 : ℝ), (2746966473/5000000000 : ℝ), (-1960213511/10000000000 : ℝ)] ![(21539976846549/50000000000000 : ℝ), (22656757391853/50000000000000 : ℝ), (1160653150859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660971759/1250000000 : ℝ)|^263 ≤ (21539976846549/50000000000000 : ℝ)^199
        have hw : |(660971759/1250000000 : ℝ)|=(660971759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746966473/5000000000 : ℝ)|^263 ≤ (22656757391853/50000000000000 : ℝ)^199
        have hw : |(2746966473/5000000000 : ℝ)|=(2746966473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1960213511/10000000000 : ℝ)|^263 ≤ (1160653150859/10000000000000 : ℝ)^199
        have hw : |(-1960213511/10000000000 : ℝ)|=(1960213511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s2_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (868894499/2000000000 : ℝ)*x 0 + (292478869/625000000 : ℝ)*x 1 + (4033023043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868894499/2000000000 : ℝ)^263 ≤ (1661363639327/5000000000000 : ℝ)^199 := by
    have hnat : (868894499 : ℕ)^263*5000000000000^199 ≤ 1661363639327^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868894499 2000000000 1661363639327 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292478869/625000000 : ℝ)^263 ≤ (9164163107919/25000000000000 : ℝ)^199 := by
    have hnat : (292478869 : ℕ)^263*25000000000000^199 ≤ 9164163107919^199*625000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292478869 625000000 9164163107919 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033023043/10000000000 : ℝ)^263 ≤ (30116074776131/100000000000000 : ℝ)^199 := by
    have hnat : (4033023043 : ℕ)^263*100000000000000^199 ≤ 30116074776131^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033023043 10000000000 30116074776131 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868894499/2000000000 : ℝ), (292478869/625000000 : ℝ), (4033023043/10000000000 : ℝ)] ![(1661363639327/5000000000000 : ℝ), (9164163107919/25000000000000 : ℝ), (30116074776131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868894499/2000000000 : ℝ)|^263 ≤ (1661363639327/5000000000000 : ℝ)^199
        have hw : |(868894499/2000000000 : ℝ)|=(868894499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(292478869/625000000 : ℝ)|^263 ≤ (9164163107919/25000000000000 : ℝ)^199
        have hw : |(292478869/625000000 : ℝ)|=(292478869/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033023043/10000000000 : ℝ)|^263 ≤ (30116074776131/100000000000000 : ℝ)^199
        have hw : |(4033023043/10000000000 : ℝ)|=(4033023043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (251/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6091/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9421/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16273/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (251/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6091/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (251/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6091/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (251/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6091/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (251/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6091/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (251/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6091/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (251/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6091/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6091/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (101489970751043/10000000000000000000 : ℝ) := by
    have hpowers : (6091/100000 : ℝ)^8415 ≤ (101489970751043/10000000000000000000 : ℝ)^2048 := by
      have hnat : (6091 : ℕ)^8415*10000000000000000000^2048 ≤ 101489970751043^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6091 100000 101489970751043 10000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6091/100000 : ℝ)) (X := (101489970751043/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (251/1250 : ℝ) ^ (8415/2048 : ℝ) ≤ (34125189410225117/25000000000000000000 : ℝ) := by
    have hpowers : (251/1250 : ℝ)^8415 ≤ (34125189410225117/25000000000000000000 : ℝ)^2048 := by
      have hnat : (251 : ℕ)^8415*25000000000000000000^2048 ≤ 34125189410225117^2048*1250^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251 1250 34125189410225117 25000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (251/1250 : ℝ)) (X := (34125189410225117/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000101489970751043/5000000000000000000 : ℝ) ≤ (10000049399848849/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (5000101489970751043/5000000000000000000 : ℝ)^2048 ≤ (10000049399848849/10000000000000000 : ℝ)^8415 := by
      have hnat : (5000101489970751043 : ℕ)^2048*10000000000000000^8415 ≤ 10000049399848849^8415*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000101489970751043 5000000000000000000 10000049399848849 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000049399848849/10000000000000000 : ℝ)) (X := (5000101489970751043/5000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50068757828674205449/50000000000000000000 : ℝ) ≤ (10003345046561349/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50068757828674205449/50000000000000000000 : ℝ)^2048 ≤ (10003345046561349/10000000000000000 : ℝ)^8415 := by
      have hnat : (50068757828674205449 : ℕ)^2048*10000000000000000^8415 ≤ 10003345046561349^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50068757828674205449 50000000000000000000 10003345046561349 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003345046561349/10000000000000000 : ℝ)) (X := (50068757828674205449/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12534125189410225117/12500000000000000000 : ℝ) ≤ (10006640693273849/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (12534125189410225117/12500000000000000000 : ℝ)^2048 ≤ (10006640693273849/10000000000000000 : ℝ)^8415 := by
      have hnat : (12534125189410225117 : ℕ)^2048*10000000000000000^8415 ≤ 10006640693273849^8415*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12534125189410225117 12500000000000000000 10006640693273849 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006640693273849/10000000000000000 : ℝ)) (X := (12534125189410225117/12500000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(101489970751043/10000000000000000000 : ℝ) ≤ ((139850543486233873661/139890000000000000000 : ℝ)+2*(263651737/111912000000 : ℝ)*(6091/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (139850543486233873661/139890000000000000000 : ℝ)+2*(263651737/111912000000 : ℝ)*(6091/100000 : ℝ)=(10000049399848849/10000000000000000 : ℝ) by norm_num, show 1+2*(101489970751043/10000000000000000000 : ℝ)=(5000101489970751043/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34125189410225117/25000000000000000000 : ℝ)+(101489970751043/10000000000000000000 : ℝ) ≤ ((139850543486233873661/139890000000000000000 : ℝ)+(263651737/111912000000 : ℝ)*((251/1250 : ℝ)+(6091/100000 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (139850543486233873661/139890000000000000000 : ℝ)+(263651737/111912000000 : ℝ)*((251/1250 : ℝ)+(6091/100000 : ℝ))=(10003345046561349/10000000000000000 : ℝ) by norm_num, show 1+(34125189410225117/25000000000000000000 : ℝ)+(101489970751043/10000000000000000000 : ℝ)=(50068757828674205449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34125189410225117/25000000000000000000 : ℝ) ≤ ((139850543486233873661/139890000000000000000 : ℝ)+2*(263651737/111912000000 : ℝ)*(251/1250 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (139850543486233873661/139890000000000000000 : ℝ)+2*(263651737/111912000000 : ℝ)*(251/1250 : ℝ)=(10006640693273849/10000000000000000 : ℝ) by norm_num, show 1+2*(34125189410225117/25000000000000000000 : ℝ)=(12534125189410225117/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (139850543486233873661/139890000000000000000 : ℝ)*(X 1 0+X 2 0)+(263651737/111912000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (6091/100000 : ℝ)) (hi := (251/1250 : ℝ)) (c := (139850543486233873661/139890000000000000000 : ℝ)) (alpha := (263651737/111912000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (139850543486233873661/139890000000000000000 : ℝ)*(X 0 1+X 2 1)+(263651737/111912000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (6091/100000 : ℝ)) (hi := (251/1250 : ℝ)) (c := (139850543486233873661/139890000000000000000 : ℝ)) (alpha := (263651737/111912000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (139850543486233873661/139890000000000000000 : ℝ)*(X 0 2+X 1 2)+(263651737/111912000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (6091/100000 : ℝ)) (hi := (251/1250 : ℝ)) (c := (139850543486233873661/139890000000000000000 : ℝ)) (alpha := (263651737/111912000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1057114059/5000000000 : ℝ)*X 0 0+(1099212921/2000000000 : ℝ)*X 0 1+(2585941201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537046299/1000000000 : ℝ)*X 1 0+(-2282264519/10000000000 : ℝ)*X 1 1+(161621323/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342615699/2500000000 : ℝ)*X 2 0+(1292970627/2500000000 : ℝ)*X 2 1+(-2282264551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2172153167/5000000000 : ℝ)*X 0 0+(805742969/2000000000 : ℝ)*X 0 1+(468392981/1000000000 : ℝ)*X 0 2+(2172153167/5000000000 : ℝ)*X 1 0+(805742969/2000000000 : ℝ)*X 1 1+(468392981/1000000000 : ℝ)*X 1 2+(2172153167/5000000000 : ℝ)*X 2 0+(805742969/2000000000 : ℝ)*X 2 1+(468392981/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2114310593/10000000000 : ℝ)*X 0 0+(1293498527/2500000000 : ℝ)*X 0 1+(274696643/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287773891/10000000000 : ℝ)*X 1 0+(-196021383/1000000000 : ℝ)*X 1 1+(5493932897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660971759/1250000000 : ℝ)*X 2 0+(2746966473/5000000000 : ℝ)*X 2 1+(-1960213511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868894499/2000000000 : ℝ)*X 0 0+(292478869/625000000 : ℝ)*X 0 1+(4033023043/10000000000 : ℝ)*X 0 2+(868894499/2000000000 : ℝ)*X 1 0+(292478869/625000000 : ℝ)*X 1 1+(4033023043/10000000000 : ℝ)*X 1 2+(868894499/2000000000 : ℝ)*X 2 0+(292478869/625000000 : ℝ)*X 2 1+(4033023043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2433236915598525409743868647/291437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26430881/1562500000000 : ℝ)*(base19) + (365365589/25000000000000 : ℝ)*(base23) + (63738337/100000000000000 : ℝ)*(lower2) + (265181579/100000000000000 : ℝ)*(upper3) + (11934637/10000000000000 : ℝ)*(upper5) + (288184738333173/12500000000000 : ℝ)*(major0) + (288184738333173/12500000000000 : ℝ)*(major1) + (288184738333173/12500000000000 : ℝ)*(major2) + (3084704050824593/100000000000000 : ℝ)*(sp0) + (1542359426348107/50000000000000 : ℝ)*(sp1) + (1542359541405121/50000000000000 : ℝ)*(sp2) + (1526225127505471/100000000000000 : ℝ)*(sp3) + (8246724003/50000000000000 : ℝ)*(sp4) + (4931624901/50000000000000 : ℝ)*(sp7) + (190779373844409/12500000000000 : ℝ)*(f.failure) + (1542360272136299/50000000000000 : ℝ)*(f.sum) + (401285123791/1165750000000000000000000000 : ℝ)*base65 + (3303186837781914549/582875000000000000000000000000000 : ℝ)*base68 + (2890119719224164549/582875000000000000000000000000000 : ℝ)*base70 + (915062197852585451/582875000000000000000000000000000 : ℝ)*base71 + (38461282093231/4663000000000000000000000000 : ℝ)*base74 + (6336624619856585451/582875000000000000000000000000000 : ℝ)*base75 + (1621135539373085451/582875000000000000000000000000000 : ℝ)*base77 + (6148791379749460451/582875000000000000000000000000000 : ℝ)*base79 + (14372535803801/2331500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (13515459/1250000000000000000000 : ℝ)*base90 + (13515459/1250000000000000000000 : ℝ)*base92 + (13515459/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7297721737778899270077/4663000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33360731/5000000000000 : ℝ)*(base19) + (19834499/2000000000000 : ℝ)*(base23) + (66271943/100000000000000 : ℝ)*(upper2) + (115130977/100000000000000 : ℝ)*(upper3) + (29826893/100000000000000 : ℝ)*(upper5) + (584006958396227/25000000000000 : ℝ)*(major0) + (584006958396227/25000000000000 : ℝ)*(major1) + (584006958396227/25000000000000 : ℝ)*(major2) + (6119694807/100000000000000 : ℝ)*(sp1) + (12015146083/100000000000000 : ℝ)*(sp2) + (625119291689657/20000000000000 : ℝ)*(sp4) + (1562794835769429/50000000000000 : ℝ)*(sp5) + (781395862894313/25000000000000 : ℝ)*(sp6) + (48326848642311/3125000000000 : ℝ)*(sp7) + (48326848642311/3125000000000 : ℝ)*(f.failure) + (625119291689657/20000000000000 : ℝ)*(f.sum) + (9740351052083/2797800000000000000000000000 : ℝ)*base66 + (5543234251135922953/3497250000000000000000000000000000 : ℝ)*base68 + (859840037896077047/3497250000000000000000000000000000 : ℝ)*base69 + (20641200177079077047/3497250000000000000000000000000000 : ℝ)*base71 + (6962187131603/2797800000000000000000000000 : ℝ)*base74 + (9779129071989422953/3497250000000000000000000000000000 : ℝ)*base76 + (6197356617709922953/3497250000000000000000000000000000 : ℝ)*base78 + (12829023836248077047/3497250000000000000000000000000000 : ℝ)*base79 + (32072935779259/13989000000000000000000000000 : ℝ)*base82 + (2455261/312500000000000000000 : ℝ)*base90 + (2455261/312500000000000000000 : ℝ)*base92 + (2455261/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1223_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (251/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6091/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1223_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1223_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1223_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1223_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
