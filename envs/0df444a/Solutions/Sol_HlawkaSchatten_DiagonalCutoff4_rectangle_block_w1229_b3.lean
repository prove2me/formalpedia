-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1229_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:11.806837+00:00
-- url     : https://prove2.me/submissions/6ccf5818-be29-4a68-95c1-f62c7eed94fe

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
theorem support_rectangle_w1229_box_0 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001862917/10000000000 : ℝ)*x 0 + (10498123/19531250 : ℝ)*x 1 + (2687519309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001862917/10000000000 : ℝ)^4211 ≤ (11939371948973/100000000000000 : ℝ)^3187 := by
    have hnat : (2001862917 : ℕ)^4211*100000000000000^3187 ≤ 11939371948973^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001862917 10000000000 11939371948973 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10498123/19531250 : ℝ)^4211 ≤ (44030315951097/100000000000000 : ℝ)^3187 := by
    have hnat : (10498123 : ℕ)^4211*100000000000000^3187 ≤ 44030315951097^3187*19531250^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10498123 19531250 44030315951097 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687519309/5000000000 : ℝ)^4211 ≤ (22015156038117/50000000000000 : ℝ)^3187 := by
    have hnat : (2687519309 : ℕ)^4211*50000000000000^3187 ≤ 22015156038117^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687519309 5000000000 22015156038117 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001862917/10000000000 : ℝ), (10498123/19531250 : ℝ), (2687519309/5000000000 : ℝ)] ![(11939371948973/100000000000000 : ℝ), (44030315951097/100000000000000 : ℝ), (22015156038117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001862917/10000000000 : ℝ)|^4211 ≤ (11939371948973/100000000000000 : ℝ)^3187
        have hw : |(-2001862917/10000000000 : ℝ)|=(2001862917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10498123/19531250 : ℝ)|^4211 ≤ (44030315951097/100000000000000 : ℝ)^3187
        have hw : |(10498123/19531250 : ℝ)|=(10498123/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687519309/5000000000 : ℝ)|^4211 ≤ (22015156038117/50000000000000 : ℝ)^3187
        have hw : |(2687519309/5000000000 : ℝ)|=(2687519309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_1 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2648350197/5000000000 : ℝ)*x 0 + (-2108307299/10000000000 : ℝ)*x 1 + (5375039287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648350197/5000000000 : ℝ)^4211 ≤ (2159219960263/5000000000000 : ℝ)^3187 := by
    have hnat : (2648350197 : ℕ)^4211*5000000000000^3187 ≤ 2159219960263^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648350197 5000000000 2159219960263 5000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108307299/10000000000 : ℝ)^4211 ≤ (12785281462623/100000000000000 : ℝ)^3187 := by
    have hnat : (2108307299 : ℕ)^4211*100000000000000^3187 ≤ 12785281462623^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108307299 10000000000 12785281462623 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375039287/10000000000 : ℝ)^4211 ≤ (176121277269/400000000000 : ℝ)^3187 := by
    have hnat : (5375039287 : ℕ)^4211*400000000000^3187 ≤ 176121277269^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375039287 10000000000 176121277269 400000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648350197/5000000000 : ℝ), (-2108307299/10000000000 : ℝ), (5375039287/10000000000 : ℝ)] ![(2159219960263/5000000000000 : ℝ), (12785281462623/100000000000000 : ℝ), (176121277269/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648350197/5000000000 : ℝ)|^4211 ≤ (2159219960263/5000000000000 : ℝ)^3187
        have hw : |(2648350197/5000000000 : ℝ)|=(2648350197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108307299/10000000000 : ℝ)|^4211 ≤ (12785281462623/100000000000000 : ℝ)^3187
        have hw : |(-2108307299/10000000000 : ℝ)|=(2108307299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375039287/10000000000 : ℝ)|^4211 ≤ (176121277269/400000000000 : ℝ)^3187
        have hw : |(5375039287/10000000000 : ℝ)|=(5375039287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_2 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1324175503/2500000000 : ℝ)*x 0 + (2687519353/5000000000 : ℝ)*x 1 + (-2108305909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324175503/2500000000 : ℝ)^4211 ≤ (43184416635493/100000000000000 : ℝ)^3187 := by
    have hnat : (1324175503 : ℕ)^4211*100000000000000^3187 ≤ 43184416635493^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324175503 2500000000 43184416635493 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687519353/5000000000 : ℝ)^4211 ≤ (22015156514357/50000000000000 : ℝ)^3187 := by
    have hnat : (2687519353 : ℕ)^4211*50000000000000^3187 ≤ 22015156514357^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687519353 5000000000 22015156514357 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108305909/10000000000 : ℝ)^4211 ≤ (6392635162477/50000000000000 : ℝ)^3187 := by
    have hnat : (2108305909 : ℕ)^4211*50000000000000^3187 ≤ 6392635162477^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108305909 10000000000 6392635162477 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324175503/2500000000 : ℝ), (2687519353/5000000000 : ℝ), (-2108305909/10000000000 : ℝ)] ![(43184416635493/100000000000000 : ℝ), (22015156514357/50000000000000 : ℝ), (6392635162477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324175503/2500000000 : ℝ)|^4211 ≤ (43184416635493/100000000000000 : ℝ)^3187
        have hw : |(1324175503/2500000000 : ℝ)|=(1324175503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687519353/5000000000 : ℝ)|^4211 ≤ (22015156514357/50000000000000 : ℝ)^3187
        have hw : |(2687519353/5000000000 : ℝ)|=(2687519353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108305909/10000000000 : ℝ)|^4211 ≤ (6392635162477/50000000000000 : ℝ)^3187
        have hw : |(-2108305909/10000000000 : ℝ)|=(2108305909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_3 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4459219707/10000000000 : ℝ)*x 0 + (537660297/1250000000 : ℝ)*x 1 + (4301281697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4459219707/10000000000 : ℝ)^4211 ≤ (34400431165403/100000000000000 : ℝ)^3187 := by
    have hnat : (4459219707 : ℕ)^4211*100000000000000^3187 ≤ 34400431165403^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4459219707 10000000000 34400431165403 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537660297/1250000000 : ℝ)^4211 ≤ (1024993369767/3125000000000 : ℝ)^3187 := by
    have hnat : (537660297 : ℕ)^4211*3125000000000^3187 ≤ 1024993369767^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537660297 1250000000 1024993369767 3125000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4301281697/10000000000 : ℝ)^4211 ≤ (4099972623891/12500000000000 : ℝ)^3187 := by
    have hnat : (4301281697 : ℕ)^4211*12500000000000^3187 ≤ 4099972623891^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301281697 10000000000 4099972623891 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4459219707/10000000000 : ℝ), (537660297/1250000000 : ℝ), (4301281697/10000000000 : ℝ)] ![(34400431165403/100000000000000 : ℝ), (1024993369767/3125000000000 : ℝ), (4099972623891/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4459219707/10000000000 : ℝ)|^4211 ≤ (34400431165403/100000000000000 : ℝ)^3187
        have hw : |(4459219707/10000000000 : ℝ)|=(4459219707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537660297/1250000000 : ℝ)|^4211 ≤ (1024993369767/3125000000000 : ℝ)^3187
        have hw : |(537660297/1250000000 : ℝ)|=(537660297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4301281697/10000000000 : ℝ)|^4211 ≤ (4099972623891/12500000000000 : ℝ)^3187
        have hw : |(4301281697/10000000000 : ℝ)|=(4301281697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_4 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-562862857/2500000000 : ℝ)*x 0 + (5282149033/10000000000 : ℝ)*x 1 + (5282149039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (562862857/2500000000 : ℝ)^4211 ≤ (6972289000971/50000000000000 : ℝ)^3187 := by
    have hnat : (562862857 : ℕ)^4211*50000000000000^3187 ≤ 6972289000971^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562862857 2500000000 6972289000971 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282149033/10000000000 : ℝ)^4211 ≤ (10756927738979/25000000000000 : ℝ)^3187 := by
    have hnat : (5282149033 : ℕ)^4211*25000000000000^3187 ≤ 10756927738979^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282149033 10000000000 10756927738979 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282149039/10000000000 : ℝ)^4211 ≤ (8605542204099/20000000000000 : ℝ)^3187 := by
    have hnat : (5282149039 : ℕ)^4211*20000000000000^3187 ≤ 8605542204099^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282149039 10000000000 8605542204099 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-562862857/2500000000 : ℝ), (5282149033/10000000000 : ℝ), (5282149039/10000000000 : ℝ)] ![(6972289000971/50000000000000 : ℝ), (10756927738979/25000000000000 : ℝ), (8605542204099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-562862857/2500000000 : ℝ)|^4211 ≤ (6972289000971/50000000000000 : ℝ)^3187
        have hw : |(-562862857/2500000000 : ℝ)|=(562862857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282149033/10000000000 : ℝ)|^4211 ≤ (10756927738979/25000000000000 : ℝ)^3187
        have hw : |(5282149033/10000000000 : ℝ)|=(5282149033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282149039/10000000000 : ℝ)|^4211 ≤ (8605542204099/20000000000000 : ℝ)^3187
        have hw : |(5282149039/10000000000 : ℝ)|=(5282149039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_5 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362201051/10000000000 : ℝ)*x 0 + (-2145094887/10000000000 : ℝ)*x 1 + (5282149027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362201051/10000000000 : ℝ)^4211 ≤ (43891416211457/100000000000000 : ℝ)^3187 := by
    have hnat : (5362201051 : ℕ)^4211*100000000000000^3187 ≤ 43891416211457^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362201051 10000000000 43891416211457 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145094887/10000000000 : ℝ)^4211 ≤ (52323491547/400000000000 : ℝ)^3187 := by
    have hnat : (2145094887 : ℕ)^4211*400000000000^3187 ≤ 52323491547^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145094887 10000000000 52323491547 400000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282149027/10000000000 : ℝ)^4211 ≤ (5378463861417/12500000000000 : ℝ)^3187 := by
    have hnat : (5282149027 : ℕ)^4211*12500000000000^3187 ≤ 5378463861417^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282149027 10000000000 5378463861417 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362201051/10000000000 : ℝ), (-2145094887/10000000000 : ℝ), (5282149027/10000000000 : ℝ)] ![(43891416211457/100000000000000 : ℝ), (52323491547/400000000000 : ℝ), (5378463861417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362201051/10000000000 : ℝ)|^4211 ≤ (43891416211457/100000000000000 : ℝ)^3187
        have hw : |(5362201051/10000000000 : ℝ)|=(5362201051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145094887/10000000000 : ℝ)|^4211 ≤ (52323491547/400000000000 : ℝ)^3187
        have hw : |(-2145094887/10000000000 : ℝ)|=(2145094887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282149027/10000000000 : ℝ)|^4211 ≤ (5378463861417/12500000000000 : ℝ)^3187
        have hw : |(5282149027/10000000000 : ℝ)|=(5282149027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_6 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362200961/10000000000 : ℝ)*x 0 + (2641074551/5000000000 : ℝ)*x 1 + (-2145094907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362200961/10000000000 : ℝ)^4211 ≤ (43891415238077/100000000000000 : ℝ)^3187 := by
    have hnat : (5362200961 : ℕ)^4211*100000000000000^3187 ≤ 43891415238077^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362200961 10000000000 43891415238077 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641074551/5000000000 : ℝ)^4211 ≤ (1721108467943/4000000000000 : ℝ)^3187 := by
    have hnat : (2641074551 : ℕ)^4211*4000000000000^3187 ≤ 1721108467943^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641074551 5000000000 1721108467943 4000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145094907/10000000000 : ℝ)^4211 ≤ (6540436523949/50000000000000 : ℝ)^3187 := by
    have hnat : (2145094907 : ℕ)^4211*50000000000000^3187 ≤ 6540436523949^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145094907 10000000000 6540436523949 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362200961/10000000000 : ℝ), (2641074551/5000000000 : ℝ), (-2145094907/10000000000 : ℝ)] ![(43891415238077/100000000000000 : ℝ), (1721108467943/4000000000000 : ℝ), (6540436523949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362200961/10000000000 : ℝ)|^4211 ≤ (43891415238077/100000000000000 : ℝ)^3187
        have hw : |(5362200961/10000000000 : ℝ)|=(5362200961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641074551/5000000000 : ℝ)|^4211 ≤ (1721108467943/4000000000000 : ℝ)^3187
        have hw : |(2641074551/5000000000 : ℝ)|=(2641074551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145094907/10000000000 : ℝ)|^4211 ≤ (6540436523949/50000000000000 : ℝ)^3187
        have hw : |(-2145094907/10000000000 : ℝ)|=(2145094907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_7 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4245505817/10000000000 : ℝ)*x 0 + (4408118759/10000000000 : ℝ)*x 1 + (2204059411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245505817/10000000000 : ℝ)^4211 ≤ (32238972842697/100000000000000 : ℝ)^3187 := by
    have hnat : (4245505817 : ℕ)^4211*100000000000000^3187 ≤ 32238972842697^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245505817 10000000000 32238972842697 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408118759/10000000000 : ℝ)^4211 ≤ (33880513249907/100000000000000 : ℝ)^3187 := by
    have hnat : (4408118759 : ℕ)^4211*100000000000000^3187 ≤ 33880513249907^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408118759 10000000000 33880513249907 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204059411/5000000000 : ℝ)^4211 ≤ (33880513889701/100000000000000 : ℝ)^3187 := by
    have hnat : (2204059411 : ℕ)^4211*100000000000000^3187 ≤ 33880513889701^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204059411 5000000000 33880513889701 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245505817/10000000000 : ℝ), (4408118759/10000000000 : ℝ), (2204059411/5000000000 : ℝ)] ![(32238972842697/100000000000000 : ℝ), (33880513249907/100000000000000 : ℝ), (33880513889701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245505817/10000000000 : ℝ)|^4211 ≤ (32238972842697/100000000000000 : ℝ)^3187
        have hw : |(4245505817/10000000000 : ℝ)|=(4245505817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408118759/10000000000 : ℝ)|^4211 ≤ (33880513249907/100000000000000 : ℝ)^3187
        have hw : |(4408118759/10000000000 : ℝ)|=(4408118759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2204059411/5000000000 : ℝ)|^4211 ≤ (33880513889701/100000000000000 : ℝ)^3187
        have hw : |(2204059411/5000000000 : ℝ)|=(2204059411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_8 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199163989/10000000000 : ℝ)*x 0 + (521881221/1000000000 : ℝ)*x 1 + (5384652227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199163989/10000000000 : ℝ)^4211 ≤ (2703656384259/20000000000000 : ℝ)^3187 := by
    have hnat : (2199163989 : ℕ)^4211*20000000000000^3187 ≤ 2703656384259^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199163989 10000000000 2703656384259 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521881221/1000000000 : ℝ)^4211 ≤ (21173660923529/50000000000000 : ℝ)^3187 := by
    have hnat : (521881221 : ℕ)^4211*50000000000000^3187 ≤ 21173660923529^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521881221 1000000000 21173660923529 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384652227/10000000000 : ℝ)^4211 ≤ (11033599052269/25000000000000 : ℝ)^3187 := by
    have hnat : (5384652227 : ℕ)^4211*25000000000000^3187 ≤ 11033599052269^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384652227 10000000000 11033599052269 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199163989/10000000000 : ℝ), (521881221/1000000000 : ℝ), (5384652227/10000000000 : ℝ)] ![(2703656384259/20000000000000 : ℝ), (21173660923529/50000000000000 : ℝ), (11033599052269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199163989/10000000000 : ℝ)|^4211 ≤ (2703656384259/20000000000000 : ℝ)^3187
        have hw : |(-2199163989/10000000000 : ℝ)|=(2199163989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521881221/1000000000 : ℝ)|^4211 ≤ (21173660923529/50000000000000 : ℝ)^3187
        have hw : |(521881221/1000000000 : ℝ)|=(521881221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384652227/10000000000 : ℝ)|^4211 ≤ (11033599052269/25000000000000 : ℝ)^3187
        have hw : |(5384652227/10000000000 : ℝ)|=(5384652227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_9 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289919833/10000000000 : ℝ)*x 0 + (-1052215813/5000000000 : ℝ)*x 1 + (5384652091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289919833/10000000000 : ℝ)^4211 ≤ (10777842316997/25000000000000 : ℝ)^3187 := by
    have hnat : (5289919833 : ℕ)^4211*25000000000000^3187 ≤ 10777842316997^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289919833 10000000000 10777842316997 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052215813/5000000000 : ℝ)^4211 ≤ (6377117992141/50000000000000 : ℝ)^3187 := by
    have hnat : (1052215813 : ℕ)^4211*50000000000000^3187 ≤ 6377117992141^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052215813 5000000000 6377117992141 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384652091/10000000000 : ℝ)^4211 ≤ (8826878947243/20000000000000 : ℝ)^3187 := by
    have hnat : (5384652091 : ℕ)^4211*20000000000000^3187 ≤ 8826878947243^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384652091 10000000000 8826878947243 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289919833/10000000000 : ℝ), (-1052215813/5000000000 : ℝ), (5384652091/10000000000 : ℝ)] ![(10777842316997/25000000000000 : ℝ), (6377117992141/50000000000000 : ℝ), (8826878947243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289919833/10000000000 : ℝ)|^4211 ≤ (10777842316997/25000000000000 : ℝ)^3187
        have hw : |(5289919833/10000000000 : ℝ)|=(5289919833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1052215813/5000000000 : ℝ)|^4211 ≤ (6377117992141/50000000000000 : ℝ)^3187
        have hw : |(-1052215813/5000000000 : ℝ)|=(1052215813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384652091/10000000000 : ℝ)|^4211 ≤ (8826878947243/20000000000000 : ℝ)^3187
        have hw : |(5384652091/10000000000 : ℝ)|=(5384652091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_10 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289919733/10000000000 : ℝ)*x 0 + (1076930467/2000000000 : ℝ)*x 1 + (-2104431429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289919733/10000000000 : ℝ)^4211 ≤ (43111368191161/100000000000000 : ℝ)^3187 := by
    have hnat : (5289919733 : ℕ)^4211*100000000000000^3187 ≤ 43111368191161^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289919733 10000000000 43111368191161 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076930467/2000000000 : ℝ)^4211 ≤ (441343973787/1000000000000 : ℝ)^3187 := by
    have hnat : (1076930467 : ℕ)^4211*1000000000000^3187 ≤ 441343973787^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076930467 2000000000 441343973787 1000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104431429/10000000000 : ℝ)^4211 ≤ (1275423440671/10000000000000 : ℝ)^3187 := by
    have hnat : (2104431429 : ℕ)^4211*10000000000000^3187 ≤ 1275423440671^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104431429 10000000000 1275423440671 10000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289919733/10000000000 : ℝ), (1076930467/2000000000 : ℝ), (-2104431429/10000000000 : ℝ)] ![(43111368191161/100000000000000 : ℝ), (441343973787/1000000000000 : ℝ), (1275423440671/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289919733/10000000000 : ℝ)|^4211 ≤ (43111368191161/100000000000000 : ℝ)^3187
        have hw : |(5289919733/10000000000 : ℝ)|=(5289919733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076930467/2000000000 : ℝ)|^4211 ≤ (441343973787/1000000000000 : ℝ)^3187
        have hw : |(1076930467/2000000000 : ℝ)|=(1076930467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104431429/10000000000 : ℝ)|^4211 ≤ (1275423440671/10000000000000 : ℝ)^3187
        have hw : |(-2104431429/10000000000 : ℝ)|=(2104431429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_11 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4481063757/10000000000 : ℝ)*x 0 + (33517339/78125000 : ℝ)*x 1 + (536277443/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4481063757/10000000000 : ℝ)^4211 ≤ (34623265764043/100000000000000 : ℝ)^3187 := by
    have hnat : (4481063757 : ℕ)^4211*100000000000000^3187 ≤ 34623265764043^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481063757 10000000000 34623265764043 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33517339/78125000 : ℝ)^4211 ≤ (16344183172897/50000000000000 : ℝ)^3187 := by
    have hnat : (33517339 : ℕ)^4211*50000000000000^3187 ≤ 16344183172897^3187*78125000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33517339 78125000 16344183172897 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536277443/1250000000 : ℝ)^4211 ≤ (32688367876037/100000000000000 : ℝ)^3187 := by
    have hnat : (536277443 : ℕ)^4211*100000000000000^3187 ≤ 32688367876037^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536277443 1250000000 32688367876037 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4481063757/10000000000 : ℝ), (33517339/78125000 : ℝ), (536277443/1250000000 : ℝ)] ![(34623265764043/100000000000000 : ℝ), (16344183172897/50000000000000 : ℝ), (32688367876037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4481063757/10000000000 : ℝ)|^4211 ≤ (34623265764043/100000000000000 : ℝ)^3187
        have hw : |(4481063757/10000000000 : ℝ)|=(4481063757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33517339/78125000 : ℝ)|^4211 ≤ (16344183172897/50000000000000 : ℝ)^3187
        have hw : |(33517339/78125000 : ℝ)|=(33517339/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(536277443/1250000000 : ℝ)|^4211 ≤ (32688367876037/100000000000000 : ℝ)^3187
        have hw : |(536277443/1250000000 : ℝ)|=(536277443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_12 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-128401077/625000000 : ℝ)*x 0 + (1359289683/2500000000 : ℝ)*x 1 + (5274073849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128401077/625000000 : ℝ)^4211 ≤ (3088814847059/25000000000000 : ℝ)^3187 := by
    have hnat : (128401077 : ℕ)^4211*25000000000000^3187 ≤ 3088814847059^3187*625000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128401077 625000000 3088814847059 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359289683/2500000000 : ℝ)^4211 ≤ (44703922972349/100000000000000 : ℝ)^3187 := by
    have hnat : (1359289683 : ℕ)^4211*100000000000000^3187 ≤ 44703922972349^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359289683 2500000000 44703922972349 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274073849/10000000000 : ℝ)^4211 ≤ (42940817617327/100000000000000 : ℝ)^3187 := by
    have hnat : (5274073849 : ℕ)^4211*100000000000000^3187 ≤ 42940817617327^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274073849 10000000000 42940817617327 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128401077/625000000 : ℝ), (1359289683/2500000000 : ℝ), (5274073849/10000000000 : ℝ)] ![(3088814847059/25000000000000 : ℝ), (44703922972349/100000000000000 : ℝ), (42940817617327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128401077/625000000 : ℝ)|^4211 ≤ (3088814847059/25000000000000 : ℝ)^3187
        have hw : |(-128401077/625000000 : ℝ)|=(128401077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359289683/2500000000 : ℝ)|^4211 ≤ (44703922972349/100000000000000 : ℝ)^3187
        have hw : |(1359289683/2500000000 : ℝ)|=(1359289683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274073849/10000000000 : ℝ)|^4211 ≤ (42940817617327/100000000000000 : ℝ)^3187
        have hw : |(5274073849/10000000000 : ℝ)|=(5274073849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_13 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670986519/1250000000 : ℝ)*x 0 + (-2148237029/10000000000 : ℝ)*x 1 + (263703731/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670986519/1250000000 : ℝ)^4211 ≤ (43952977825489/100000000000000 : ℝ)^3187 := by
    have hnat : (670986519 : ℕ)^4211*100000000000000^3187 ≤ 43952977825489^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670986519 1250000000 43952977825489 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148237029/10000000000 : ℝ)^4211 ≤ (13106196248427/100000000000000 : ℝ)^3187 := by
    have hnat : (2148237029 : ℕ)^4211*100000000000000^3187 ≤ 13106196248427^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148237029 10000000000 13106196248427 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263703731/500000000 : ℝ)^4211 ≤ (2683801619479/6250000000000 : ℝ)^3187 := by
    have hnat : (263703731 : ℕ)^4211*6250000000000^3187 ≤ 2683801619479^3187*500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263703731 500000000 2683801619479 6250000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670986519/1250000000 : ℝ), (-2148237029/10000000000 : ℝ), (263703731/500000000 : ℝ)] ![(43952977825489/100000000000000 : ℝ), (13106196248427/100000000000000 : ℝ), (2683801619479/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670986519/1250000000 : ℝ)|^4211 ≤ (43952977825489/100000000000000 : ℝ)^3187
        have hw : |(670986519/1250000000 : ℝ)|=(670986519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148237029/10000000000 : ℝ)|^4211 ≤ (13106196248427/100000000000000 : ℝ)^3187
        have hw : |(-2148237029/10000000000 : ℝ)|=(2148237029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263703731/500000000 : ℝ)|^4211 ≤ (2683801619479/6250000000000 : ℝ)^3187
        have hw : |(263703731/500000000 : ℝ)|=(263703731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_14 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341973199/2500000000 : ℝ)*x 0 + (1318518561/2500000000 : ℝ)*x 1 + (-1074118333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341973199/2500000000 : ℝ)^4211 ≤ (8790596958587/20000000000000 : ℝ)^3187 := by
    have hnat : (1341973199 : ℕ)^4211*20000000000000^3187 ≤ 8790596958587^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341973199 2500000000 8790596958587 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318518561/2500000000 : ℝ)^4211 ≤ (8588164373339/20000000000000 : ℝ)^3187 := by
    have hnat : (1318518561 : ℕ)^4211*20000000000000^3187 ≤ 8588164373339^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318518561 2500000000 8588164373339 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074118333/5000000000 : ℝ)^4211 ≤ (6553096661113/50000000000000 : ℝ)^3187 := by
    have hnat : (1074118333 : ℕ)^4211*50000000000000^3187 ≤ 6553096661113^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074118333 5000000000 6553096661113 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341973199/2500000000 : ℝ), (1318518561/2500000000 : ℝ), (-1074118333/5000000000 : ℝ)] ![(8790596958587/20000000000000 : ℝ), (8588164373339/20000000000000 : ℝ), (6553096661113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341973199/2500000000 : ℝ)|^4211 ≤ (8790596958587/20000000000000 : ℝ)^3187
        have hw : |(1341973199/2500000000 : ℝ)|=(1341973199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318518561/2500000000 : ℝ)|^4211 ≤ (8588164373339/20000000000000 : ℝ)^3187
        have hw : |(1318518561/2500000000 : ℝ)|=(1318518561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1074118333/5000000000 : ℝ)|^4211 ≤ (6553096661113/50000000000000 : ℝ)^3187
        have hw : |(-1074118333/5000000000 : ℝ)|=(1074118333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_box_15 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4226696037/10000000000 : ℝ)*x 0 + (4417401443/10000000000 : ℝ)*x 1 + (2208700301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4226696037/10000000000 : ℝ)^4211 ≤ (32050378305059/100000000000000 : ℝ)^3187 := by
    have hnat : (4226696037 : ℕ)^4211*100000000000000^3187 ≤ 32050378305059^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226696037 10000000000 32050378305059 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417401443/10000000000 : ℝ)^4211 ≤ (8493703777979/25000000000000 : ℝ)^3187 := by
    have hnat : (4417401443 : ℕ)^4211*25000000000000^3187 ≤ 8493703777979^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417401443 10000000000 8493703777979 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208700301/5000000000 : ℝ)^4211 ≤ (16987403282697/50000000000000 : ℝ)^3187 := by
    have hnat : (2208700301 : ℕ)^4211*50000000000000^3187 ≤ 16987403282697^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208700301 5000000000 16987403282697 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4226696037/10000000000 : ℝ), (4417401443/10000000000 : ℝ), (2208700301/5000000000 : ℝ)] ![(32050378305059/100000000000000 : ℝ), (8493703777979/25000000000000 : ℝ), (16987403282697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4226696037/10000000000 : ℝ)|^4211 ≤ (32050378305059/100000000000000 : ℝ)^3187
        have hw : |(4226696037/10000000000 : ℝ)|=(4226696037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417401443/10000000000 : ℝ)|^4211 ≤ (8493703777979/25000000000000 : ℝ)^3187
        have hw : |(4417401443/10000000000 : ℝ)|=(4417401443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208700301/5000000000 : ℝ)|^4211 ≤ (16987403282697/50000000000000 : ℝ)^3187
        have hw : |(2208700301/5000000000 : ℝ)|=(2208700301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1229_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15561/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59367/100000 : ℝ) ∧ (8007/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83317/100000 : ℝ) := by
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
  have lower0 : (11463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11463/100000 : ℝ) ^ (8421/2048 : ℝ) ≤ (13552121459882197/100000000000000000000 : ℝ) := by
    have hpowers : (11463/100000 : ℝ)^8421 ≤ (13552121459882197/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11463 : ℕ)^8421*100000000000000000000^2048 ≤ 13552121459882197^2048*100000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11463 100000 13552121459882197 100000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11463/100000 : ℝ)) (X := (13552121459882197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (8421/2048 : ℝ) ≤ (31722339180467173/100000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^8421 ≤ (31722339180467173/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14097 : ℕ)^8421*100000000000000000000^2048 ≤ 31722339180467173^2048*100000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 31722339180467173 100000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (31722339180467173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013552121459882197/50000000000000000000 : ℝ) ≤ (1250082388963937/1250000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (50013552121459882197/50000000000000000000 : ℝ)^2048 ≤ (1250082388963937/1250000000000000 : ℝ)^8421 := by
      have hnat : (50013552121459882197 : ℕ)^2048*1250000000000000^8421 ≤ 1250082388963937^8421*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013552121459882197 50000000000000000000 1250082388963937 1250000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250082388963937/1250000000000000 : ℝ)) (X := (50013552121459882197/50000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004527446064034937/10000000000000000000 : ℝ) ≤ (10001100893179169/10000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (10004527446064034937/10000000000000000000 : ℝ)^2048 ≤ (10001100893179169/10000000000000000 : ℝ)^8421 := by
      have hnat : (10004527446064034937 : ℕ)^2048*10000000000000000^8421 ≤ 10001100893179169^8421*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004527446064034937 10000000000000000000 10001100893179169 10000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001100893179169/10000000000000000 : ℝ)) (X := (10004527446064034937/10000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031722339180467173/50000000000000000000 : ℝ) ≤ (5000771337323421/5000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (50031722339180467173/50000000000000000000 : ℝ)^2048 ≤ (5000771337323421/5000000000000000 : ℝ)^8421 := by
      have hnat : (50031722339180467173 : ℕ)^2048*5000000000000000^8421 ≤ 5000771337323421^8421*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031722339180467173 50000000000000000000 5000771337323421 5000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000771337323421/5000000000000000 : ℝ)) (X := (50031722339180467173/50000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13552121459882197/100000000000000000000 : ℝ) ≤ ((4388601303053368211/4390000000000000000 : ℝ)+2*(441781467673/263400000000000 : ℝ)*(11463/100000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (4388601303053368211/4390000000000000000 : ℝ)+2*(441781467673/263400000000000 : ℝ)*(11463/100000 : ℝ)=(1250082388963937/1250000000000000 : ℝ) by norm_num, show 1+2*(13552121459882197/100000000000000000000 : ℝ)=(50013552121459882197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31722339180467173/100000000000000000000 : ℝ)+(13552121459882197/100000000000000000000 : ℝ) ≤ ((4388601303053368211/4390000000000000000 : ℝ)+(441781467673/263400000000000 : ℝ)*((14097/100000 : ℝ)+(11463/100000 : ℝ)))^(8421/2048 : ℝ) := by
    rw [show (4388601303053368211/4390000000000000000 : ℝ)+(441781467673/263400000000000 : ℝ)*((14097/100000 : ℝ)+(11463/100000 : ℝ))=(10001100893179169/10000000000000000 : ℝ) by norm_num, show 1+(31722339180467173/100000000000000000000 : ℝ)+(13552121459882197/100000000000000000000 : ℝ)=(10004527446064034937/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31722339180467173/100000000000000000000 : ℝ) ≤ ((4388601303053368211/4390000000000000000 : ℝ)+2*(441781467673/263400000000000 : ℝ)*(14097/100000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (4388601303053368211/4390000000000000000 : ℝ)+2*(441781467673/263400000000000 : ℝ)*(14097/100000 : ℝ)=(5000771337323421/5000000000000000 : ℝ) by norm_num, show 1+2*(31722339180467173/100000000000000000000 : ℝ)=(50031722339180467173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4388601303053368211/4390000000000000000 : ℝ)*(X 1 0+X 2 0)+(441781467673/263400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (4388601303053368211/4390000000000000000 : ℝ)) (alpha := (441781467673/263400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4388601303053368211/4390000000000000000 : ℝ)*(X 0 1+X 2 1)+(441781467673/263400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (4388601303053368211/4390000000000000000 : ℝ)) (alpha := (441781467673/263400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4388601303053368211/4390000000000000000 : ℝ)*(X 0 2+X 1 2)+(441781467673/263400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (4388601303053368211/4390000000000000000 : ℝ)) (alpha := (441781467673/263400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2001862917/10000000000 : ℝ)*X 0 0+(10498123/19531250 : ℝ)*X 0 1+(2687519309/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648350197/5000000000 : ℝ)*X 1 0+(-2108307299/10000000000 : ℝ)*X 1 1+(5375039287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1324175503/2500000000 : ℝ)*X 2 0+(2687519353/5000000000 : ℝ)*X 2 1+(-2108305909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4459219707/10000000000 : ℝ)*X 0 0+(537660297/1250000000 : ℝ)*X 0 1+(4301281697/10000000000 : ℝ)*X 0 2+(4459219707/10000000000 : ℝ)*X 1 0+(537660297/1250000000 : ℝ)*X 1 1+(4301281697/10000000000 : ℝ)*X 1 2+(4459219707/10000000000 : ℝ)*X 2 0+(537660297/1250000000 : ℝ)*X 2 1+(4301281697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-562862857/2500000000 : ℝ)*X 0 0+(5282149033/10000000000 : ℝ)*X 0 1+(5282149039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362201051/10000000000 : ℝ)*X 1 0+(-2145094887/10000000000 : ℝ)*X 1 1+(5282149027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362200961/10000000000 : ℝ)*X 2 0+(2641074551/5000000000 : ℝ)*X 2 1+(-2145094907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4245505817/10000000000 : ℝ)*X 0 0+(4408118759/10000000000 : ℝ)*X 0 1+(2204059411/5000000000 : ℝ)*X 0 2+(4245505817/10000000000 : ℝ)*X 1 0+(4408118759/10000000000 : ℝ)*X 1 1+(2204059411/5000000000 : ℝ)*X 1 2+(4245505817/10000000000 : ℝ)*X 2 0+(4408118759/10000000000 : ℝ)*X 2 1+(2204059411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2199163989/10000000000 : ℝ)*X 0 0+(521881221/1000000000 : ℝ)*X 0 1+(5384652227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289919833/10000000000 : ℝ)*X 1 0+(-1052215813/5000000000 : ℝ)*X 1 1+(5384652091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289919733/10000000000 : ℝ)*X 2 0+(1076930467/2000000000 : ℝ)*X 2 1+(-2104431429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4481063757/10000000000 : ℝ)*X 0 0+(33517339/78125000 : ℝ)*X 0 1+(536277443/1250000000 : ℝ)*X 0 2+(4481063757/10000000000 : ℝ)*X 1 0+(33517339/78125000 : ℝ)*X 1 1+(536277443/1250000000 : ℝ)*X 1 2+(4481063757/10000000000 : ℝ)*X 2 0+(33517339/78125000 : ℝ)*X 2 1+(536277443/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-128401077/625000000 : ℝ)*X 0 0+(1359289683/2500000000 : ℝ)*X 0 1+(5274073849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((670986519/1250000000 : ℝ)*X 1 0+(-2148237029/10000000000 : ℝ)*X 1 1+(263703731/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1341973199/2500000000 : ℝ)*X 2 0+(1318518561/2500000000 : ℝ)*X 2 1+(-1074118333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4226696037/10000000000 : ℝ)*X 0 0+(4417401443/10000000000 : ℝ)*X 0 1+(2208700301/5000000000 : ℝ)*X 0 2+(4226696037/10000000000 : ℝ)*X 1 0+(4417401443/10000000000 : ℝ)*X 1 1+(2208700301/5000000000 : ℝ)*X 1 2+(4226696037/10000000000 : ℝ)*X 2 0+(4417401443/10000000000 : ℝ)*X 2 1+(2208700301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15561/25000 : ℝ) ≤ (-27324136162221103923316323117161/43900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7393407/100000000000000 : ℝ)*(upper0) + (159481/625000000000 : ℝ)*(upper1) + (46766053/100000000000000 : ℝ)*(upper2) + (5307/25000000000 : ℝ)*(upper3) + (44408893/100000000000000 : ℝ)*(upper5) + (798471888395183/20000000000000 : ℝ)*(major0) + (798471888395183/20000000000000 : ℝ)*(major1) + (798471888395183/20000000000000 : ℝ)*(major2) + (11564841/5000000000000 : ℝ)*(sp1) + (4633038591/100000000000000 : ℝ)*(sp3) + (5364562422856503/100000000000000 : ℝ)*(sp4) + (5364562191559683/100000000000000 : ℝ)*(sp5) + (5364562422856503/100000000000000 : ℝ)*(sp6) + (2640899084064481/100000000000000 : ℝ)*(sp7) + (82528241159471/3125000000000 : ℝ)*(f.failure) + (5364562422856503/100000000000000 : ℝ)*(f.sum) + (10653540484861/2634000000000000000000000000 : ℝ)*base66 + (1576868848588467161/263400000000000000000000000000000 : ℝ)*base68 + (13950034869782732839/263400000000000000000000000000000 : ℝ)*base69 + (1519234250600667161/263400000000000000000000000000000 : ℝ)*base72 + (11203727149237/2634000000000000000000000000 : ℝ)*base74 + (5191953036414867161/263400000000000000000000000000000 : ℝ)*base76 + (2998205619398667161/263400000000000000000000000000000 : ℝ)*base78 + (12336683351987732839/263400000000000000000000000000000 : ℝ)*base79 + (367079212633/2634000000000000000000000000 : ℝ)*base82 + (494123/312500000000000000000 : ℝ)*base90 + (494123/312500000000000000000 : ℝ)*base92 + (494123/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59367/100000 : ℝ) ≤ (65157828662432828627604890865591/109750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30050711/25000000000000 : ℝ)*(upper0) + (278349039/100000000000000 : ℝ)*(lower1) + (7380289/625000000000 : ℝ)*(upper4) + (2028977250278527/50000000000000 : ℝ)*(major0) + (2028977250278527/50000000000000 : ℝ)*(major1) + (2028977250278527/50000000000000 : ℝ)*(major2) + (5411792360150261/100000000000000 : ℝ)*(sp0) + (2705909722427547/50000000000000 : ℝ)*(sp1) + (5411772846564747/100000000000000 : ℝ)*(sp2) + (2684253634688587/100000000000000 : ℝ)*(sp3) + (5625532171/100000000000000 : ℝ)*(sp5) + (52223822519/100000000000000 : ℝ)*(sp6) + (253266977/625000000000 : ℝ)*(sp7) + (6542047401/20000000000000 : ℝ)*(sp8) + (2684294157404907/100000000000000 : ℝ)*(f.failure) + (2705912535193633/50000000000000 : ℝ)*(f.sum) + (856679927939/411562500000000000000000000 : ℝ)*base66 + (4569708125816334409/658500000000000000000000000000000 : ℝ)*base68 + (4320691659594665591/658500000000000000000000000000000 : ℝ)*base69 + (5684576828054334409/658500000000000000000000000000000 : ℝ)*base72 + (46053691575203/3292500000000000000000000000 : ℝ)*base73 + (3103726921917665591/658500000000000000000000000000000 : ℝ)*base75 + (8163956396165334409/658500000000000000000000000000000 : ℝ)*base78 + (17887160455955334409/658500000000000000000000000000000 : ℝ)*base80 + (4688714395277/823125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (35445791/10000000000000000000000 : ℝ)*base90 + (35445791/10000000000000000000000 : ℝ)*base92 + (35445791/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (8007/10000 : ℝ) ≤ (87879894737614159338003983730003/109750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136567/6250000000000 : ℝ)*(upper0) + (3530171/25000000000000 : ℝ)*(lower1) + (47084009/50000000000000 : ℝ)*(lower3) + (6778709/20000000000000 : ℝ)*(upper4) + (4524883757019891/100000000000000 : ℝ)*(major0) + (4524883757019891/100000000000000 : ℝ)*(major1) + (4524883757019891/100000000000000 : ℝ)*(major2) + (1019127253/50000000000000 : ℝ)*(sp0) + (138880576247/100000000000000 : ℝ)*(sp2) + (15688193997/50000000000000 : ℝ)*(sp3) + (6029911601315777/100000000000000 : ℝ)*(sp8) + (6029913639570283/100000000000000 : ℝ)*(sp9) + (1507443689748509/25000000000000 : ℝ)*(sp10) + (2922980044667/97656250000 : ℝ)*(sp11) + (1496581471063501/50000000000000 : ℝ)*(f.failure) + (6029913639570283/100000000000000 : ℝ)*(f.sum) + (25150839328129/4390000000000000000000000000 : ℝ)*base66 + (470918734065864999/439000000000000000000000000000000 : ℝ)*base68 + (17093507987845135001/439000000000000000000000000000000 : ℝ)*base69 + (372562385098864999/439000000000000000000000000000000 : ℝ)*base72 + (30595512081699/4390000000000000000000000000 : ℝ)*base74 + (12267520411528864999/439000000000000000000000000000000 : ℝ)*base76 + (1176326876205864999/439000000000000000000000000000000 : ℝ)*base78 + (7309145969689864999/439000000000000000000000000000000 : ℝ)*base80 + (297062013306711/4390000000000000000000000000 : ℝ)*base81 + (26348487/5000000000000000000000 : ℝ)*base89 + (26348487/5000000000000000000000 : ℝ)*base91 + (26348487/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83317/100000 : ℝ) ≤ (-182876145795572131487425545820877/219500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59155497/100000000000000 : ℝ)*(lower0) + (7671883/50000000000000 : ℝ)*(upper1) + (98721427/25000000000000 : ℝ)*(lower2) + (59917977/12500000000000 : ℝ)*(upper3) + (65344803/12500000000000 : ℝ)*(upper5) + (4560288377856469/100000000000000 : ℝ)*(major0) + (4560288377856469/100000000000000 : ℝ)*(major1) + (4560288377856469/100000000000000 : ℝ)*(major2) + (2169380431/20000000000000 : ℝ)*(sp4) + (74278350359/25000000000000 : ℝ)*(sp7) + (245270192288149/4000000000000 : ℝ)*(sp12) + (153294141352647/2500000000000 : ℝ)*(sp13) + (153294141352647/2500000000000 : ℝ)*(sp14) + (188517850779513/6250000000000 : ℝ)*(sp15) + (754145681468411/25000000000000 : ℝ)*(f.failure) + (153294141352647/2500000000000 : ℝ)*(f.sum) + (28294352660077/13170000000000000000000000000 : ℝ)*base65 + (37677143987283229123/1317000000000000000000000000000000 : ℝ)*base68 + (46466266145201770877/1317000000000000000000000000000000 : ℝ)*base69 + (9400509505871770877/1317000000000000000000000000000000 : ℝ)*base71 + (86922883699477/13170000000000000000000000000 : ℝ)*base73 + (15513343222691770877/1317000000000000000000000000000000 : ℝ)*base75 + (7761915595631770877/1317000000000000000000000000000000 : ℝ)*base77 + (18701033466168229123/1317000000000000000000000000000000 : ℝ)*base80 + (80395858302877/13170000000000000000000000000 : ℝ)*base81 + (19575343/2500000000000000000000 : ℝ)*base90 + (19575343/2500000000000000000000 : ℝ)*base92 + (19575343/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1229_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59367/100000 : ℝ) else (8007/10000 : ℝ) ≤ X j i ∧ X j i ≤ (83317/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1229_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1229_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59367/100000 : ℝ) else (8007/10000 : ℝ) ≤ X j i ∧ X j i ≤ (83317/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1229_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59367/100000 : ℝ) else (8007/10000 : ℝ) ≤ X j i ∧ X j i ≤ (83317/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1229_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
