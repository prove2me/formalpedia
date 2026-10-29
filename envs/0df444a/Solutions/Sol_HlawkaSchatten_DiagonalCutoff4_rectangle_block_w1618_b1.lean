-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1618_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:12.113919+00:00
-- url     : https://prove2.me/submissions/1be46682-a706-417c-bcbf-495265a31ac9

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
theorem support_rectangle_w1618_s3_0 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1684258843/10000000000 : ℝ)*x 0 + (2728726909/5000000000 : ℝ)*x 1 + (5181164081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1684258843/10000000000 : ℝ)^4791 ≤ (5189077878251/50000000000000 : ℝ)^3767 := by
    have hnat : (1684258843 : ℕ)^4791*50000000000000^3767 ≤ 5189077878251^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684258843 10000000000 5189077878251 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728726909/5000000000 : ℝ)^4791 ≤ (46290826558529/100000000000000 : ℝ)^3767 := by
    have hnat : (2728726909 : ℕ)^4791*100000000000000^3767 ≤ 46290826558529^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728726909 5000000000 46290826558529 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181164081/10000000000 : ℝ)^4791 ≤ (43331017676927/100000000000000 : ℝ)^3767 := by
    have hnat : (5181164081 : ℕ)^4791*100000000000000^3767 ≤ 43331017676927^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181164081 10000000000 43331017676927 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1684258843/10000000000 : ℝ), (2728726909/5000000000 : ℝ), (5181164081/10000000000 : ℝ)] ![(5189077878251/50000000000000 : ℝ), (46290826558529/100000000000000 : ℝ), (43331017676927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1684258843/10000000000 : ℝ)|^4791 ≤ (5189077878251/50000000000000 : ℝ)^3767
        have hw : |(-1684258843/10000000000 : ℝ)|=(1684258843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728726909/5000000000 : ℝ)|^4791 ≤ (46290826558529/100000000000000 : ℝ)^3767
        have hw : |(2728726909/5000000000 : ℝ)|=(2728726909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181164081/10000000000 : ℝ)|^4791 ≤ (43331017676927/100000000000000 : ℝ)^3767
        have hw : |(5181164081/10000000000 : ℝ)|=(5181164081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s3_1 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334533971/625000000 : ℝ)*x 0 + (-1826689559/10000000000 : ℝ)*x 1 + (2590582143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334533971/625000000 : ℝ)^4791 ≤ (11290509941819/25000000000000 : ℝ)^3767 := by
    have hnat : (334533971 : ℕ)^4791*25000000000000^3767 ≤ 11290509941819^3767*625000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334533971 625000000 11290509941819 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1826689559/10000000000 : ℝ)^4791 ≤ (11506940355767/100000000000000 : ℝ)^3767 := by
    have hnat : (1826689559 : ℕ)^4791*100000000000000^3767 ≤ 11506940355767^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826689559 10000000000 11506940355767 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590582143/5000000000 : ℝ)^4791 ≤ (43331019857427/100000000000000 : ℝ)^3767 := by
    have hnat : (2590582143 : ℕ)^4791*100000000000000^3767 ≤ 43331019857427^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590582143 5000000000 43331019857427 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334533971/625000000 : ℝ), (-1826689559/10000000000 : ℝ), (2590582143/5000000000 : ℝ)] ![(11290509941819/25000000000000 : ℝ), (11506940355767/100000000000000 : ℝ), (43331019857427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334533971/625000000 : ℝ)|^4791 ≤ (11290509941819/25000000000000 : ℝ)^3767
        have hw : |(334533971/625000000 : ℝ)|=(334533971/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1826689559/10000000000 : ℝ)|^4791 ≤ (11506940355767/100000000000000 : ℝ)^3767
        have hw : |(-1826689559/10000000000 : ℝ)|=(1826689559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590582143/5000000000 : ℝ)|^4791 ≤ (43331019857427/100000000000000 : ℝ)^3767
        have hw : |(2590582143/5000000000 : ℝ)|=(2590582143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s3_2 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669067943/1250000000 : ℝ)*x 0 + (5181164507/10000000000 : ℝ)*x 1 + (-228336157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669067943/1250000000 : ℝ)^4791 ≤ (14451852753/32000000000 : ℝ)^3767 := by
    have hnat : (669067943 : ℕ)^4791*32000000000^3767 ≤ 14451852753^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669067943 1250000000 14451852753 32000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181164507/10000000000 : ℝ)^4791 ≤ (43331022208111/100000000000000 : ℝ)^3767 := by
    have hnat : (5181164507 : ℕ)^4791*100000000000000^3767 ≤ 43331022208111^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181164507 10000000000 43331022208111 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228336157/1250000000 : ℝ)^4791 ≤ (1438367241027/12500000000000 : ℝ)^3767 := by
    have hnat : (228336157 : ℕ)^4791*12500000000000^3767 ≤ 1438367241027^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228336157 1250000000 1438367241027 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669067943/1250000000 : ℝ), (5181164507/10000000000 : ℝ), (-228336157/1250000000 : ℝ)] ![(14451852753/32000000000 : ℝ), (43331022208111/100000000000000 : ℝ), (1438367241027/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669067943/1250000000 : ℝ)|^4791 ≤ (14451852753/32000000000 : ℝ)^3767
        have hw : |(669067943/1250000000 : ℝ)|=(669067943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181164507/10000000000 : ℝ)|^4791 ≤ (43331022208111/100000000000000 : ℝ)^3767
        have hw : |(5181164507/10000000000 : ℝ)|=(5181164507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228336157/1250000000 : ℝ)|^4791 ≤ (1438367241027/12500000000000 : ℝ)^3767
        have hw : |(-228336157/1250000000 : ℝ)|=(228336157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s3_3 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205938529/10000000000 : ℝ)*x 0 + (1936766889/5000000000 : ℝ)*x 1 + (569953507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205938529/10000000000 : ℝ)^4791 ≤ (3323655040229/10000000000000 : ℝ)^3767 := by
    have hnat : (4205938529 : ℕ)^4791*10000000000000^3767 ≤ 3323655040229^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205938529 10000000000 3323655040229 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936766889/5000000000 : ℝ)^4791 ≤ (935385853053/3125000000000 : ℝ)^3767 := by
    have hnat : (1936766889 : ℕ)^4791*3125000000000^3767 ≤ 935385853053^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936766889 5000000000 935385853053 3125000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569953507/1250000000 : ℝ)^4791 ≤ (18415551147773/50000000000000 : ℝ)^3767 := by
    have hnat : (569953507 : ℕ)^4791*50000000000000^3767 ≤ 18415551147773^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569953507 1250000000 18415551147773 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205938529/10000000000 : ℝ), (1936766889/5000000000 : ℝ), (569953507/1250000000 : ℝ)] ![(3323655040229/10000000000000 : ℝ), (935385853053/3125000000000 : ℝ), (18415551147773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205938529/10000000000 : ℝ)|^4791 ≤ (3323655040229/10000000000000 : ℝ)^3767
        have hw : |(4205938529/10000000000 : ℝ)|=(4205938529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936766889/5000000000 : ℝ)|^4791 ≤ (935385853053/3125000000000 : ℝ)^3767
        have hw : |(1936766889/5000000000 : ℝ)|=(1936766889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569953507/1250000000 : ℝ)|^4791 ≤ (18415551147773/50000000000000 : ℝ)^3767
        have hw : |(569953507/1250000000 : ℝ)|=(569953507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s3_4 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1684328627/10000000000 : ℝ)*x 0 + (2591615467/5000000000 : ℝ)*x 1 + (1091073007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1684328627/10000000000 : ℝ)^4791 ≤ (10378702646781/100000000000000 : ℝ)^3767 := by
    have hnat : (1684328627 : ℕ)^4791*100000000000000^3767 ≤ 10378702646781^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684328627 10000000000 10378702646781 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591615467/5000000000 : ℝ)^4791 ≤ (21676501560131/50000000000000 : ℝ)^3767 := by
    have hnat : (2591615467 : ℕ)^4791*50000000000000^3767 ≤ 21676501560131^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591615467 5000000000 21676501560131 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091073007/2000000000 : ℝ)^4791 ≤ (46268294226303/100000000000000 : ℝ)^3767 := by
    have hnat : (1091073007 : ℕ)^4791*100000000000000^3767 ≤ 46268294226303^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091073007 2000000000 46268294226303 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1684328627/10000000000 : ℝ), (2591615467/5000000000 : ℝ), (1091073007/2000000000 : ℝ)] ![(10378702646781/100000000000000 : ℝ), (21676501560131/50000000000000 : ℝ), (46268294226303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1684328627/10000000000 : ℝ)|^4791 ≤ (10378702646781/100000000000000 : ℝ)^3767
        have hw : |(-1684328627/10000000000 : ℝ)|=(1684328627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591615467/5000000000 : ℝ)|^4791 ≤ (21676501560131/50000000000000 : ℝ)^3767
        have hw : |(2591615467/5000000000 : ℝ)|=(2591615467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091073007/2000000000 : ℝ)|^4791 ≤ (46268294226303/100000000000000 : ℝ)^3767
        have hw : |(1091073007/2000000000 : ℝ)|=(1091073007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s3_5 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319766433/2500000000 : ℝ)*x 0 + (-776244219/5000000000 : ℝ)*x 1 + (5455365033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319766433/2500000000 : ℝ)^4791 ≤ (44375018868517/100000000000000 : ℝ)^3767 := by
    have hnat : (1319766433 : ℕ)^4791*100000000000000^3767 ≤ 44375018868517^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319766433 2500000000 44375018868517 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776244219/5000000000 : ℝ)^4791 ≤ (4678343457463/50000000000000 : ℝ)^3767 := by
    have hnat : (776244219 : ℕ)^4791*50000000000000^3767 ≤ 4678343457463^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776244219 5000000000 4678343457463 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455365033/10000000000 : ℝ)^4791 ≤ (4626829420473/10000000000000 : ℝ)^3767 := by
    have hnat : (5455365033 : ℕ)^4791*10000000000000^3767 ≤ 4626829420473^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455365033 10000000000 4626829420473 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319766433/2500000000 : ℝ), (-776244219/5000000000 : ℝ), (5455365033/10000000000 : ℝ)] ![(44375018868517/100000000000000 : ℝ), (4678343457463/50000000000000 : ℝ), (4626829420473/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319766433/2500000000 : ℝ)|^4791 ≤ (44375018868517/100000000000000 : ℝ)^3767
        have hw : |(1319766433/2500000000 : ℝ)|=(1319766433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-776244219/5000000000 : ℝ)|^4791 ≤ (4678343457463/50000000000000 : ℝ)^3767
        have hw : |(-776244219/5000000000 : ℝ)|=(776244219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455365033/10000000000 : ℝ)|^4791 ≤ (4626829420473/10000000000000 : ℝ)^3767
        have hw : |(5455365033/10000000000 : ℝ)|=(5455365033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s3_6 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41242701/78125000 : ℝ)*x 0 + (5455365039/10000000000 : ℝ)*x 1 + (-310497687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41242701/78125000 : ℝ)^4791 ≤ (22187509412877/50000000000000 : ℝ)^3767 := by
    have hnat : (41242701 : ℕ)^4791*50000000000000^3767 ≤ 22187509412877^3767*78125000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41242701 78125000 22187509412877 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455365039/10000000000 : ℝ)^4791 ≤ (925365885389/2000000000000 : ℝ)^3767 := by
    have hnat : (5455365039 : ℕ)^4791*2000000000000^3767 ≤ 925365885389^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455365039 10000000000 925365885389 2000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310497687/2000000000 : ℝ)^4791 ≤ (935668689193/10000000000000 : ℝ)^3767 := by
    have hnat : (310497687 : ℕ)^4791*10000000000000^3767 ≤ 935668689193^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310497687 2000000000 935668689193 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41242701/78125000 : ℝ), (5455365039/10000000000 : ℝ), (-310497687/2000000000 : ℝ)] ![(22187509412877/50000000000000 : ℝ), (925365885389/2000000000000 : ℝ), (935668689193/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41242701/78125000 : ℝ)|^4791 ≤ (22187509412877/50000000000000 : ℝ)^3767
        have hw : |(41242701/78125000 : ℝ)|=(41242701/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455365039/10000000000 : ℝ)|^4791 ≤ (925365885389/2000000000000 : ℝ)^3767
        have hw : |(5455365039/10000000000 : ℝ)|=(5455365039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310497687/2000000000 : ℝ)|^4791 ≤ (935668689193/10000000000000 : ℝ)^3767
        have hw : |(-310497687/2000000000 : ℝ)|=(310497687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s3_7 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2103055763/5000000000 : ℝ)*x 0 + (71163999/156250000 : ℝ)*x 1 + (24241999/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103055763/5000000000 : ℝ)^4791 ≤ (830957227549/2500000000000 : ℝ)^3767 := by
    have hnat : (2103055763 : ℕ)^4791*2500000000000^3767 ≤ 830957227549^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103055763 5000000000 830957227549 2500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71163999/156250000 : ℝ)^4791 ≤ (9194596460371/25000000000000 : ℝ)^3767 := by
    have hnat : (71163999 : ℕ)^4791*25000000000000^3767 ≤ 9194596460371^3767*156250000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71163999 156250000 9194596460371 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24241999/62500000 : ℝ)^4791 ≤ (29983325049663/100000000000000 : ℝ)^3767 := by
    have hnat : (24241999 : ℕ)^4791*100000000000000^3767 ≤ 29983325049663^3767*62500000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24241999 62500000 29983325049663 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103055763/5000000000 : ℝ), (71163999/156250000 : ℝ), (24241999/62500000 : ℝ)] ![(830957227549/2500000000000 : ℝ), (9194596460371/25000000000000 : ℝ), (29983325049663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103055763/5000000000 : ℝ)|^4791 ≤ (830957227549/2500000000000 : ℝ)^3767
        have hw : |(2103055763/5000000000 : ℝ)|=(2103055763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71163999/156250000 : ℝ)|^4791 ≤ (9194596460371/25000000000000 : ℝ)^3767
        have hw : |(71163999/156250000 : ℝ)|=(71163999/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24241999/62500000 : ℝ)|^4791 ≤ (29983325049663/100000000000000 : ℝ)^3767
        have hw : |(24241999/62500000 : ℝ)|=(24241999/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1618_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10477/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8169/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16461/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16461/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16461/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16461/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16461/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16461/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10367/100000 : ℝ) ^ (4787/1024 : ℝ) ≤ (2502479283502547/100000000000000000000 : ℝ) := by
    have hpowers : (10367/100000 : ℝ)^4787 ≤ (2502479283502547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10367 : ℕ)^4787*100000000000000000000^1024 ≤ 2502479283502547^1024*100000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10367 100000 2502479283502547 100000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10367/100000 : ℝ)) (X := (2502479283502547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16461/100000 : ℝ) ^ (4787/1024 : ℝ) ≤ (21731306673136073/100000000000000000000 : ℝ) := by
    have hpowers : (16461/100000 : ℝ)^4787 ≤ (21731306673136073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16461 : ℕ)^4787*100000000000000000000^1024 ≤ 21731306673136073^1024*100000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16461 100000 21731306673136073 100000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16461/100000 : ℝ)) (X := (21731306673136073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002502479283502547/50000000000000000000 : ℝ) ≤ (1000010706030409/1000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (50002502479283502547/50000000000000000000 : ℝ)^1024 ≤ (1000010706030409/1000000000000000 : ℝ)^4787 := by
      have hnat : (50002502479283502547 : ℕ)^1024*1000000000000000^4787 ≤ 1000010706030409^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002502479283502547 50000000000000000000 1000010706030409 1000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000010706030409/1000000000000000 : ℝ)) (X := (50002502479283502547/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001211689297831931/5000000000000000000 : ℝ) ≤ (156258099094393/156250000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (5001211689297831931/5000000000000000000 : ℝ)^1024 ≤ (156258099094393/156250000000000 : ℝ)^4787 := by
      have hnat : (5001211689297831931 : ℕ)^1024*156250000000000^4787 ≤ 156258099094393^4787*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001211689297831931 5000000000000000000 156258099094393 156250000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156258099094393/156250000000000 : ℝ)) (X := (5001211689297831931/5000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021731306673136073/50000000000000000000 : ℝ) ≤ (5000464811889107/5000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (50021731306673136073/50000000000000000000 : ℝ)^1024 ≤ (5000464811889107/5000000000000000 : ℝ)^4787 := by
      have hnat : (50021731306673136073 : ℕ)^1024*5000000000000000^4787 ≤ 5000464811889107^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021731306673136073 50000000000000000000 5000464811889107 5000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000464811889107/5000000000000000 : ℝ)) (X := (50021731306673136073/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2502479283502547/100000000000000000000 : ℝ) ≤ ((7616515613744610119/7617500000000000000 : ℝ)+2*(205640868531/304700000000000 : ℝ)*(10367/100000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (7616515613744610119/7617500000000000000 : ℝ)+2*(205640868531/304700000000000 : ℝ)*(10367/100000 : ℝ)=(1000010706030409/1000000000000000 : ℝ) by norm_num, show 1+2*(2502479283502547/100000000000000000000 : ℝ)=(50002502479283502547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21731306673136073/100000000000000000000 : ℝ)+(2502479283502547/100000000000000000000 : ℝ) ≤ ((7616515613744610119/7617500000000000000 : ℝ)+(205640868531/304700000000000 : ℝ)*((16461/100000 : ℝ)+(10367/100000 : ℝ)))^(4787/1024 : ℝ) := by
    rw [show (7616515613744610119/7617500000000000000 : ℝ)+(205640868531/304700000000000 : ℝ)*((16461/100000 : ℝ)+(10367/100000 : ℝ))=(156258099094393/156250000000000 : ℝ) by norm_num, show 1+(21731306673136073/100000000000000000000 : ℝ)+(2502479283502547/100000000000000000000 : ℝ)=(5001211689297831931/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21731306673136073/100000000000000000000 : ℝ) ≤ ((7616515613744610119/7617500000000000000 : ℝ)+2*(205640868531/304700000000000 : ℝ)*(16461/100000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (7616515613744610119/7617500000000000000 : ℝ)+2*(205640868531/304700000000000 : ℝ)*(16461/100000 : ℝ)=(5000464811889107/5000000000000000 : ℝ) by norm_num, show 1+2*(21731306673136073/100000000000000000000 : ℝ)=(50021731306673136073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7616515613744610119/7617500000000000000 : ℝ)*(X 1 0+X 2 0)+(205640868531/304700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (10367/100000 : ℝ)) (hi := (16461/100000 : ℝ)) (c := (7616515613744610119/7617500000000000000 : ℝ)) (alpha := (205640868531/304700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7616515613744610119/7617500000000000000 : ℝ)*(X 0 1+X 2 1)+(205640868531/304700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (10367/100000 : ℝ)) (hi := (16461/100000 : ℝ)) (c := (7616515613744610119/7617500000000000000 : ℝ)) (alpha := (205640868531/304700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7616515613744610119/7617500000000000000 : ℝ)*(X 0 2+X 1 2)+(205640868531/304700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (10367/100000 : ℝ)) (hi := (16461/100000 : ℝ)) (c := (7616515613744610119/7617500000000000000 : ℝ)) (alpha := (205640868531/304700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1684258843/10000000000 : ℝ)*X 0 0+(2728726909/5000000000 : ℝ)*X 0 1+(5181164081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334533971/625000000 : ℝ)*X 1 0+(-1826689559/10000000000 : ℝ)*X 1 1+(2590582143/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669067943/1250000000 : ℝ)*X 2 0+(5181164507/10000000000 : ℝ)*X 2 1+(-228336157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205938529/10000000000 : ℝ)*X 0 0+(1936766889/5000000000 : ℝ)*X 0 1+(569953507/1250000000 : ℝ)*X 0 2+(4205938529/10000000000 : ℝ)*X 1 0+(1936766889/5000000000 : ℝ)*X 1 1+(569953507/1250000000 : ℝ)*X 1 2+(4205938529/10000000000 : ℝ)*X 2 0+(1936766889/5000000000 : ℝ)*X 2 1+(569953507/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1684328627/10000000000 : ℝ)*X 0 0+(2591615467/5000000000 : ℝ)*X 0 1+(1091073007/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319766433/2500000000 : ℝ)*X 1 0+(-776244219/5000000000 : ℝ)*X 1 1+(5455365033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41242701/78125000 : ℝ)*X 2 0+(5455365039/10000000000 : ℝ)*X 2 1+(-310497687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103055763/5000000000 : ℝ)*X 0 0+(71163999/156250000 : ℝ)*X 0 1+(24241999/62500000 : ℝ)*X 0 2+(2103055763/5000000000 : ℝ)*X 1 0+(71163999/156250000 : ℝ)*X 1 1+(24241999/62500000 : ℝ)*X 1 2+(2103055763/5000000000 : ℝ)*X 2 0+(71163999/156250000 : ℝ)*X 2 1+(24241999/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2121060910506430969387632963/190437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1272337841/100000000000000 : ℝ)*(base19) + (1082968093/100000000000000 : ℝ)*(base23) + (104256521/100000000000000 : ℝ)*(lower2) + (70084649/50000000000000 : ℝ)*(upper3) + (229492769/100000000000000 : ℝ)*(upper5) + (1269240704206759/50000000000000 : ℝ)*(major0) + (1269240704206759/50000000000000 : ℝ)*(major1) + (1269240704206759/50000000000000 : ℝ)*(major2) + (452425610885913/12500000000000 : ℝ)*(sp0) + (1809711784502933/50000000000000 : ℝ)*(sp1) + (1809711879187807/50000000000000 : ℝ)*(sp2) + (145753168019467/10000000000000 : ℝ)*(sp3) + (9977128201/50000000000000 : ℝ)*(sp4) + (5924027579/100000000000000 : ℝ)*(sp7) + (182192200527781/12500000000000 : ℝ)*(f.failure) + (1809712420671853/50000000000000 : ℝ)*(f.sum) + (5823821708143/3808750000000000000000000000 : ℝ)*base66 + (96952215465847211/34625000000000000000000000000000 : ℝ)*base67 + (225403495497902789/34625000000000000000000000000000 : ℝ)*base70 + (186025784413152789/34625000000000000000000000000000 : ℝ)*base72 + (2324239713901/1904375000000000000000000000 : ℝ)*base73 + (376093918624652789/34625000000000000000000000000000 : ℝ)*base76 + (208128786123152789/34625000000000000000000000000000 : ℝ)*base78 + (51833549745097211/34625000000000000000000000000000 : ℝ)*base79 + (39499958388251/7617500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7893613/1250000000000000000000 : ℝ)*base90 + (7893613/1250000000000000000000 : ℝ)*base92 + (7893613/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37616154466884384933442023/4328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133172487/10000000000000 : ℝ)*(base19) + (1436487967/100000000000000 : ℝ)*(base23) + (11539133/6250000000000 : ℝ)*(upper3) + (47708911/100000000000000 : ℝ)*(lower4) + (89064787/50000000000000 : ℝ)*(upper5) + (322152393872573/12500000000000 : ℝ)*(major0) + (322152393872573/12500000000000 : ℝ)*(major1) + (322152393872573/12500000000000 : ℝ)*(major2) + (15312112991/100000000000000 : ℝ)*(sp1) + (16545963069/100000000000000 : ℝ)*(sp2) + (918664521940553/25000000000000 : ℝ)*(sp4) + (3674641443924351/100000000000000 : ℝ)*(sp5) + (459330013163897/12500000000000 : ℝ)*(sp6) + (1479779924495717/100000000000000 : ℝ)*(sp7) + (1479779924495717/100000000000000 : ℝ)*(f.failure) + (918664521940553/25000000000000 : ℝ)*(f.sum) + (2266024995267/692500000000000000000000000 : ℝ)*base65 + (35822264218881017/8656250000000000000000000000000 : ℝ)*base67 + (2629782010756017/8656250000000000000000000000000 : ℝ)*base69 + (3320831656068517/8656250000000000000000000000000 : ℝ)*base71 + (4818883231539/1385000000000000000000000000 : ℝ)*base73 + (53100908162224767/8656250000000000000000000000000 : ℝ)*base75 + (3536966031806483/8656250000000000000000000000000 : ℝ)*base78 + (27795307675037267/8656250000000000000000000000000 : ℝ)*base79 + (371952064387/173125000000000000000000000 : ℝ)*base82 + (25746541/10000000000000000000000 : ℝ)*base90 + (25746541/10000000000000000000000 : ℝ)*base92 + (25746541/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1618_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8169/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1618_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1618_s4_0 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1684356039/10000000000 : ℝ)*x 0 + (682121201/1250000000 : ℝ)*x 1 + (2590791777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1684356039/10000000000 : ℝ)^4791 ≤ (10378917473589/100000000000000 : ℝ)^3767 := by
    have hnat : (1684356039 : ℕ)^4791*100000000000000^3767 ≤ 10378917473589^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684356039 10000000000 10378917473589 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682121201/1250000000 : ℝ)^4791 ≤ (46285603030447/100000000000000 : ℝ)^3767 := by
    have hnat : (682121201 : ℕ)^4791*100000000000000^3767 ≤ 46285603030447^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682121201 1250000000 46285603030447 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590791777/5000000000 : ℝ)^4791 ≤ (10833869871249/25000000000000 : ℝ)^3767 := by
    have hnat : (2590791777 : ℕ)^4791*25000000000000^3767 ≤ 10833869871249^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590791777 5000000000 10833869871249 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1684356039/10000000000 : ℝ), (682121201/1250000000 : ℝ), (2590791777/5000000000 : ℝ)] ![(10378917473589/100000000000000 : ℝ), (46285603030447/100000000000000 : ℝ), (10833869871249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1684356039/10000000000 : ℝ)|^4791 ≤ (10378917473589/100000000000000 : ℝ)^3767
        have hw : |(-1684356039/10000000000 : ℝ)|=(1684356039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682121201/1250000000 : ℝ)|^4791 ≤ (46285603030447/100000000000000 : ℝ)^3767
        have hw : |(682121201/1250000000 : ℝ)|=(682121201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590791777/5000000000 : ℝ)|^4791 ≤ (10833869871249/25000000000000 : ℝ)^3767
        have hw : |(2590791777/5000000000 : ℝ)|=(2590791777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s4_1 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676206901/5000000000 : ℝ)*x 0 + (-456576669/2500000000 : ℝ)*x 1 + (1295395889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676206901/5000000000 : ℝ)^4791 ≤ (2258032379223/5000000000000 : ℝ)^3767 := by
    have hnat : (2676206901 : ℕ)^4791*5000000000000^3767 ≤ 2258032379223^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676206901 5000000000 2258032379223 5000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456576669/2500000000 : ℝ)^4791 ≤ (1437984111557/12500000000000 : ℝ)^3767 := by
    have hnat : (456576669 : ℕ)^4791*12500000000000^3767 ≤ 1437984111557^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456576669 2500000000 1437984111557 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295395889/2500000000 : ℝ)^4791 ≤ (4333547950627/10000000000000 : ℝ)^3767 := by
    have hnat : (1295395889 : ℕ)^4791*10000000000000^3767 ≤ 4333547950627^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295395889 2500000000 4333547950627 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676206901/5000000000 : ℝ), (-456576669/2500000000 : ℝ), (1295395889/2500000000 : ℝ)] ![(2258032379223/5000000000000 : ℝ), (1437984111557/12500000000000 : ℝ), (4333547950627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676206901/5000000000 : ℝ)|^4791 ≤ (2258032379223/5000000000000 : ℝ)^3767
        have hw : |(2676206901/5000000000 : ℝ)|=(2676206901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456576669/2500000000 : ℝ)|^4791 ≤ (1437984111557/12500000000000 : ℝ)^3767
        have hw : |(-456576669/2500000000 : ℝ)|=(456576669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295395889/2500000000 : ℝ)|^4791 ≤ (4333547950627/10000000000000 : ℝ)^3767
        have hw : |(1295395889/2500000000 : ℝ)|=(1295395889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s4_2 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352413803/10000000000 : ℝ)*x 0 + (2590791777/5000000000 : ℝ)*x 1 + (-913153339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352413803/10000000000 : ℝ)^4791 ≤ (45160647595191/100000000000000 : ℝ)^3767 := by
    have hnat : (5352413803 : ℕ)^4791*100000000000000^3767 ≤ 45160647595191^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352413803 10000000000 45160647595191 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590791777/5000000000 : ℝ)^4791 ≤ (10833869871249/25000000000000 : ℝ)^3767 := by
    have hnat : (2590791777 : ℕ)^4791*25000000000000^3767 ≤ 10833869871249^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590791777 5000000000 10833869871249 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (913153339/5000000000 : ℝ)^4791 ≤ (5751936454239/50000000000000 : ℝ)^3767 := by
    have hnat : (913153339 : ℕ)^4791*50000000000000^3767 ≤ 5751936454239^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913153339 5000000000 5751936454239 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352413803/10000000000 : ℝ), (2590791777/5000000000 : ℝ), (-913153339/5000000000 : ℝ)] ![(45160647595191/100000000000000 : ℝ), (10833869871249/25000000000000 : ℝ), (5751936454239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352413803/10000000000 : ℝ)|^4791 ≤ (45160647595191/100000000000000 : ℝ)^3767
        have hw : |(5352413803/10000000000 : ℝ)|=(5352413803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590791777/5000000000 : ℝ)|^4791 ≤ (10833869871249/25000000000000 : ℝ)^3767
        have hw : |(2590791777/5000000000 : ℝ)|=(2590791777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-913153339/5000000000 : ℝ)|^4791 ≤ (5751936454239/50000000000000 : ℝ)^3767
        have hw : |(-913153339/5000000000 : ℝ)|=(913153339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s4_3 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525750191/1250000000 : ℝ)*x 0 + (774929699/2000000000 : ℝ)*x 1 + (2279249981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525750191/1250000000 : ℝ)^4791 ≤ (33237183569057/100000000000000 : ℝ)^3767 := by
    have hnat : (525750191 : ℕ)^4791*100000000000000^3767 ≤ 33237183569057^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525750191 1250000000 33237183569057 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774929699/2000000000 : ℝ)^4791 ≤ (14971651567681/50000000000000 : ℝ)^3767 := by
    have hnat : (774929699 : ℕ)^4791*50000000000000^3767 ≤ 14971651567681^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774929699 2000000000 14971651567681 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279249981/5000000000 : ℝ)^4791 ≤ (36819513280297/100000000000000 : ℝ)^3767 := by
    have hnat : (2279249981 : ℕ)^4791*100000000000000^3767 ≤ 36819513280297^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279249981 5000000000 36819513280297 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525750191/1250000000 : ℝ), (774929699/2000000000 : ℝ), (2279249981/5000000000 : ℝ)] ![(33237183569057/100000000000000 : ℝ), (14971651567681/50000000000000 : ℝ), (36819513280297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525750191/1250000000 : ℝ)|^4791 ≤ (33237183569057/100000000000000 : ℝ)^3767
        have hw : |(525750191/1250000000 : ℝ)|=(525750191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(774929699/2000000000 : ℝ)|^4791 ≤ (14971651567681/50000000000000 : ℝ)^3767
        have hw : |(774929699/2000000000 : ℝ)|=(774929699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2279249981/5000000000 : ℝ)|^4791 ≤ (36819513280297/100000000000000 : ℝ)^3767
        have hw : |(2279249981/5000000000 : ℝ)|=(2279249981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s4_4 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1684424957/10000000000 : ℝ)*x 0 + (64795461/125000000 : ℝ)*x 1 + (2727447349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1684424957/10000000000 : ℝ)^4791 ≤ (5189728792773/50000000000000 : ℝ)^3767 := by
    have hnat : (1684424957 : ℕ)^4791*50000000000000^3767 ≤ 5189728792773^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684424957 10000000000 5189728792773 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64795461/125000000 : ℝ)^4791 ≤ (43357321512317/100000000000000 : ℝ)^3767 := by
    have hnat : (64795461 : ℕ)^4791*100000000000000^3767 ≤ 43357321512317^3767*125000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64795461 125000000 43357321512317 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727447349/5000000000 : ℝ)^4791 ≤ (11565805220669/25000000000000 : ℝ)^3767 := by
    have hnat : (2727447349 : ℕ)^4791*25000000000000^3767 ≤ 11565805220669^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727447349 5000000000 11565805220669 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1684424957/10000000000 : ℝ), (64795461/125000000 : ℝ), (2727447349/5000000000 : ℝ)] ![(5189728792773/50000000000000 : ℝ), (43357321512317/100000000000000 : ℝ), (11565805220669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1684424957/10000000000 : ℝ)|^4791 ≤ (5189728792773/50000000000000 : ℝ)^3767
        have hw : |(-1684424957/10000000000 : ℝ)|=(1684424957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64795461/125000000 : ℝ)|^4791 ≤ (43357321512317/100000000000000 : ℝ)^3767
        have hw : |(64795461/125000000 : ℝ)|=(64795461/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727447349/5000000000 : ℝ)|^4791 ≤ (11565805220669/25000000000000 : ℝ)^3767
        have hw : |(2727447349/5000000000 : ℝ)|=(2727447349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s4_5 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279176701/10000000000 : ℝ)*x 0 + (-77649769/500000000 : ℝ)*x 1 + (1363723697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279176701/10000000000 : ℝ)^4791 ≤ (22188102612141/50000000000000 : ℝ)^3767 := by
    have hnat : (5279176701 : ℕ)^4791*50000000000000^3767 ≤ 22188102612141^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279176701 10000000000 22188102612141 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77649769/500000000 : ℝ)^4791 ≤ (2340143226549/25000000000000 : ℝ)^3767 := by
    have hnat : (77649769 : ℕ)^4791*25000000000000^3767 ≤ 2340143226549^3767*500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77649769 500000000 2340143226549 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363723697/2500000000 : ℝ)^4791 ≤ (2313161092673/5000000000000 : ℝ)^3767 := by
    have hnat : (1363723697 : ℕ)^4791*5000000000000^3767 ≤ 2313161092673^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363723697 2500000000 2313161092673 5000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279176701/10000000000 : ℝ), (-77649769/500000000 : ℝ), (1363723697/2500000000 : ℝ)] ![(22188102612141/50000000000000 : ℝ), (2340143226549/25000000000000 : ℝ), (2313161092673/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279176701/10000000000 : ℝ)|^4791 ≤ (22188102612141/50000000000000 : ℝ)^3767
        have hw : |(5279176701/10000000000 : ℝ)|=(5279176701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77649769/500000000 : ℝ)|^4791 ≤ (2340143226549/25000000000000 : ℝ)^3767
        have hw : |(-77649769/500000000 : ℝ)|=(77649769/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363723697/2500000000 : ℝ)|^4791 ≤ (2313161092673/5000000000000 : ℝ)^3767
        have hw : |(1363723697/2500000000 : ℝ)|=(1363723697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s4_6 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319794181/2500000000 : ℝ)*x 0 + (5454894727/10000000000 : ℝ)*x 1 + (-1552995433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319794181/2500000000 : ℝ)^4791 ≤ (44376205470173/100000000000000 : ℝ)^3767 := by
    have hnat : (1319794181 : ℕ)^4791*100000000000000^3767 ≤ 44376205470173^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319794181 2500000000 44376205470173 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454894727/10000000000 : ℝ)^4791 ≤ (11565805298871/25000000000000 : ℝ)^3767 := by
    have hnat : (5454894727 : ℕ)^4791*25000000000000^3767 ≤ 11565805298871^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454894727 10000000000 11565805298871 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552995433/10000000000 : ℝ)^4791 ≤ (1170071664061/12500000000000 : ℝ)^3767 := by
    have hnat : (1552995433 : ℕ)^4791*12500000000000^3767 ≤ 1170071664061^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552995433 10000000000 1170071664061 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319794181/2500000000 : ℝ), (5454894727/10000000000 : ℝ), (-1552995433/10000000000 : ℝ)] ![(44376205470173/100000000000000 : ℝ), (11565805298871/25000000000000 : ℝ), (1170071664061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319794181/2500000000 : ℝ)|^4791 ≤ (44376205470173/100000000000000 : ℝ)^3767
        have hw : |(1319794181/2500000000 : ℝ)|=(1319794181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454894727/10000000000 : ℝ)|^4791 ≤ (11565805298871/25000000000000 : ℝ)^3767
        have hw : |(5454894727/10000000000 : ℝ)|=(5454894727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1552995433/10000000000 : ℝ)|^4791 ≤ (1170071664061/12500000000000 : ℝ)^3767
        have hw : |(-1552995433/10000000000 : ℝ)|=(1552995433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s4_7 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84123451/200000000 : ℝ)*x 0 + (455340111/1000000000 : ℝ)*x 1 + (3879801061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84123451/200000000 : ℝ)^4791 ≤ (16619451212977/50000000000000 : ℝ)^3767 := by
    have hnat : (84123451 : ℕ)^4791*50000000000000^3767 ≤ 16619451212977^3767*200000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84123451 200000000 16619451212977 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455340111/1000000000 : ℝ)^4791 ≤ (735342840469/2000000000000 : ℝ)^3767 := by
    have hnat : (455340111 : ℕ)^4791*2000000000000^3767 ≤ 735342840469^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455340111 1000000000 735342840469 2000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3879801061/10000000000 : ℝ)^4791 ≤ (7498488882309/25000000000000 : ℝ)^3767 := by
    have hnat : (3879801061 : ℕ)^4791*25000000000000^3767 ≤ 7498488882309^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3879801061 10000000000 7498488882309 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84123451/200000000 : ℝ), (455340111/1000000000 : ℝ), (3879801061/10000000000 : ℝ)] ![(16619451212977/50000000000000 : ℝ), (735342840469/2000000000000 : ℝ), (7498488882309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84123451/200000000 : ℝ)|^4791 ≤ (16619451212977/50000000000000 : ℝ)^3767
        have hw : |(84123451/200000000 : ℝ)|=(84123451/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(455340111/1000000000 : ℝ)|^4791 ≤ (735342840469/2000000000000 : ℝ)^3767
        have hw : |(455340111/1000000000 : ℝ)|=(455340111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3879801061/10000000000 : ℝ)|^4791 ≤ (7498488882309/25000000000000 : ℝ)^3767
        have hw : |(3879801061/10000000000 : ℝ)|=(3879801061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1618_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8169/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5243/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2041/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8169/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8169/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8169/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8169/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8169/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8169/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10477/100000 : ℝ) ^ (4787/1024 : ℝ) ≤ (1314525687198409/50000000000000000000 : ℝ) := by
    have hpowers : (10477/100000 : ℝ)^4787 ≤ (1314525687198409/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10477 : ℕ)^4787*50000000000000000000^1024 ≤ 1314525687198409^1024*100000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10477 100000 1314525687198409 50000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10477/100000 : ℝ)) (X := (1314525687198409/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8169/50000 : ℝ) ^ (4787/1024 : ℝ) ≤ (20982560832920507/100000000000000000000 : ℝ) := by
    have hpowers : (8169/50000 : ℝ)^4787 ≤ (20982560832920507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8169 : ℕ)^4787*100000000000000000000^1024 ≤ 20982560832920507^1024*50000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8169 50000 20982560832920507 100000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8169/50000 : ℝ)) (X := (20982560832920507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001314525687198409/25000000000000000000 : ℝ) ≤ (2000022495032141/2000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (25001314525687198409/25000000000000000000 : ℝ)^1024 ≤ (2000022495032141/2000000000000000 : ℝ)^4787 := by
      have hnat : (25001314525687198409 : ℕ)^1024*2000000000000000^4787 ≤ 2000022495032141^4787*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001314525687198409 25000000000000000000 2000022495032141 2000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000022495032141/2000000000000000 : ℝ)) (X := (25001314525687198409/25000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000944464488292693/4000000000000000000 : ℝ) ≤ (1000050503545801/1000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (4000944464488292693/4000000000000000000 : ℝ)^1024 ≤ (1000050503545801/1000000000000000 : ℝ)^4787 := by
      have hnat : (4000944464488292693 : ℕ)^1024*1000000000000000^4787 ≤ 1000050503545801^4787*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000944464488292693 4000000000000000000 1000050503545801 1000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000050503545801/1000000000000000 : ℝ)) (X := (4000944464488292693/4000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020982560832920507/50000000000000000000 : ℝ) ≤ (2000179519151063/2000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (50020982560832920507/50000000000000000000 : ℝ)^1024 ≤ (2000179519151063/2000000000000000 : ℝ)^4787 := by
      have hnat : (50020982560832920507 : ℕ)^1024*2000000000000000^4787 ≤ 2000179519151063^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020982560832920507 50000000000000000000 2000179519151063 2000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000179519151063/2000000000000000 : ℝ)) (X := (50020982560832920507/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1314525687198409/50000000000000000000 : ℝ) ≤ ((11720486701689432607/11722000000000000000 : ℝ)+2*(78512059461/117220000000000 : ℝ)*(10477/100000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (11720486701689432607/11722000000000000000 : ℝ)+2*(78512059461/117220000000000 : ℝ)*(10477/100000 : ℝ)=(2000022495032141/2000000000000000 : ℝ) by norm_num, show 1+2*(1314525687198409/50000000000000000000 : ℝ)=(25001314525687198409/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20982560832920507/100000000000000000000 : ℝ)+(1314525687198409/50000000000000000000 : ℝ) ≤ ((11720486701689432607/11722000000000000000 : ℝ)+(78512059461/117220000000000 : ℝ)*((8169/50000 : ℝ)+(10477/100000 : ℝ)))^(4787/1024 : ℝ) := by
    rw [show (11720486701689432607/11722000000000000000 : ℝ)+(78512059461/117220000000000 : ℝ)*((8169/50000 : ℝ)+(10477/100000 : ℝ))=(1000050503545801/1000000000000000 : ℝ) by norm_num, show 1+(20982560832920507/100000000000000000000 : ℝ)+(1314525687198409/50000000000000000000 : ℝ)=(4000944464488292693/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20982560832920507/100000000000000000000 : ℝ) ≤ ((11720486701689432607/11722000000000000000 : ℝ)+2*(78512059461/117220000000000 : ℝ)*(8169/50000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (11720486701689432607/11722000000000000000 : ℝ)+2*(78512059461/117220000000000 : ℝ)*(8169/50000 : ℝ)=(2000179519151063/2000000000000000 : ℝ) by norm_num, show 1+2*(20982560832920507/100000000000000000000 : ℝ)=(50020982560832920507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11720486701689432607/11722000000000000000 : ℝ)*(X 1 0+X 2 0)+(78512059461/117220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (8169/50000 : ℝ)) (c := (11720486701689432607/11722000000000000000 : ℝ)) (alpha := (78512059461/117220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11720486701689432607/11722000000000000000 : ℝ)*(X 0 1+X 2 1)+(78512059461/117220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (8169/50000 : ℝ)) (c := (11720486701689432607/11722000000000000000 : ℝ)) (alpha := (78512059461/117220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11720486701689432607/11722000000000000000 : ℝ)*(X 0 2+X 1 2)+(78512059461/117220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (8169/50000 : ℝ)) (c := (11720486701689432607/11722000000000000000 : ℝ)) (alpha := (78512059461/117220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1684356039/10000000000 : ℝ)*X 0 0+(682121201/1250000000 : ℝ)*X 0 1+(2590791777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676206901/5000000000 : ℝ)*X 1 0+(-456576669/2500000000 : ℝ)*X 1 1+(1295395889/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352413803/10000000000 : ℝ)*X 2 0+(2590791777/5000000000 : ℝ)*X 2 1+(-913153339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525750191/1250000000 : ℝ)*X 0 0+(774929699/2000000000 : ℝ)*X 0 1+(2279249981/5000000000 : ℝ)*X 0 2+(525750191/1250000000 : ℝ)*X 1 0+(774929699/2000000000 : ℝ)*X 1 1+(2279249981/5000000000 : ℝ)*X 1 2+(525750191/1250000000 : ℝ)*X 2 0+(774929699/2000000000 : ℝ)*X 2 1+(2279249981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1684424957/10000000000 : ℝ)*X 0 0+(64795461/125000000 : ℝ)*X 0 1+(2727447349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279176701/10000000000 : ℝ)*X 1 0+(-77649769/500000000 : ℝ)*X 1 1+(1363723697/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319794181/2500000000 : ℝ)*X 2 0+(5454894727/10000000000 : ℝ)*X 2 1+(-1552995433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((84123451/200000000 : ℝ)*X 0 0+(455340111/1000000000 : ℝ)*X 0 1+(3879801061/10000000000 : ℝ)*X 0 2+(84123451/200000000 : ℝ)*X 1 0+(455340111/1000000000 : ℝ)*X 1 1+(3879801061/10000000000 : ℝ)*X 1 2+(84123451/200000000 : ℝ)*X 2 0+(455340111/1000000000 : ℝ)*X 2 1+(3879801061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (747508259057958994202935689/73262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (833012353/50000000000000 : ℝ)*(base19) + (62383213/4000000000000 : ℝ)*(base23) + (57336569/100000000000000 : ℝ)*(lower2) + (126040143/50000000000000 : ℝ)*(upper3) + (172982589/100000000000000 : ℝ)*(upper5) + (636703728654309/25000000000000 : ℝ)*(major0) + (636703728654309/25000000000000 : ℝ)*(major1) + (636703728654309/25000000000000 : ℝ)*(major2) + (3631286802401697/100000000000000 : ℝ)*(sp0) + (3631305311407253/100000000000000 : ℝ)*(sp1) + (1815652708925817/50000000000000 : ℝ)*(sp2) + (146231368326747/10000000000000 : ℝ)*(sp3) + (20175030261/100000000000000 : ℝ)*(sp4) + (2207107511/25000000000000 : ℝ)*(sp7) + (1462322511697513/100000000000000 : ℝ)*(f.failure) + (1815653488715979/50000000000000 : ℝ)*(f.sum) + (147343930349/1465250000000000000000000000 : ℝ)*base65 + (3143009511424746437/293050000000000000000000000000000 : ℝ)*base68 + (834303937426446437/293050000000000000000000000000000 : ℝ)*base70 + (1750797921950746437/293050000000000000000000000000000 : ℝ)*base72 + (18753037761493/2930500000000000000000000000 : ℝ)*base74 + (180387581780046437/293050000000000000000000000000000 : ℝ)*base76 + (1347444426711453563/293050000000000000000000000000000 : ℝ)*base77 + (5128182016803746437/293050000000000000000000000000000 : ℝ)*base80 + (3224998890887/732625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15807249/10000000000000000000000 : ℝ)*base90 + (15807249/10000000000000000000000 : ℝ)*base92 + (15807249/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (705018055440606446178167223/73262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191017229/12500000000000 : ℝ)*(base19) + (50517801/3125000000000 : ℝ)*(base23) + (533647153/100000000000000 : ℝ)*(lower1) + (194086161/100000000000000 : ℝ)*(upper3) + (18248141/50000000000000 : ℝ)*(lower4) + (37697903/20000000000000 : ℝ)*(upper5) + (646382769614563/25000000000000 : ℝ)*(major0) + (646382769614563/25000000000000 : ℝ)*(major1) + (646382769614563/25000000000000 : ℝ)*(major2) + (233414427/100000000000000 : ℝ)*(sp2) + (921627348545201/25000000000000 : ℝ)*(sp4) + (3686507866042971/100000000000000 : ℝ)*(sp5) + (460813443024593/12500000000000 : ℝ)*(sp6) + (185569055245387/12500000000000 : ℝ)*(sp7) + (185569055245387/12500000000000 : ℝ)*(f.failure) + (921627348545201/25000000000000 : ℝ)*(f.sum) + (6563176411/73262500000000000000000000 : ℝ)*base65 + (3966784447235444259/293050000000000000000000000000000 : ℝ)*base68 + (1198907846557844259/293050000000000000000000000000000 : ℝ)*base70 + (4320860759067994259/293050000000000000000000000000000 : ℝ)*base72 + (2411133944901/732625000000000000000000000 : ℝ)*base74 + (20809452524436355741/293050000000000000000000000000000 : ℝ)*base75 + (1837995766999294259/293050000000000000000000000000000 : ℝ)*base78 + (1476812131099744259/293050000000000000000000000000000 : ℝ)*base80 + (2471415385347/2930500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5935549/1250000000000000000000 : ℝ)*base89 + (5935549/1250000000000000000000 : ℝ)*base91 + (5935549/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1618_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8169/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5243/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1618_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1618_s5_0 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210545461/1250000000 : ℝ)*x 0 + (5456931101/10000000000 : ℝ)*x 1 + (518161697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210545461/1250000000 : ℝ)^4791 ≤ (5189488709341/50000000000000 : ℝ)^3767 := by
    have hnat : (210545461 : ℕ)^4791*50000000000000^3767 ≤ 5189488709341^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210545461 1250000000 5189488709341 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456931101/10000000000 : ℝ)^4791 ≤ (4628518763263/10000000000000 : ℝ)^3767 := by
    have hnat : (5456931101 : ℕ)^4791*10000000000000^3767 ≤ 4628518763263^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456931101 10000000000 4628518763263 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518161697/1000000000 : ℝ)^4791 ≤ (8667166985031/20000000000000 : ℝ)^3767 := by
    have hnat : (518161697 : ℕ)^4791*20000000000000^3767 ≤ 8667166985031^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518161697 1000000000 8667166985031 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210545461/1250000000 : ℝ), (5456931101/10000000000 : ℝ), (518161697/1000000000 : ℝ)] ![(5189488709341/50000000000000 : ℝ), (4628518763263/10000000000000 : ℝ), (8667166985031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210545461/1250000000 : ℝ)|^4791 ≤ (5189488709341/50000000000000 : ℝ)^3767
        have hw : |(-210545461/1250000000 : ℝ)|=(210545461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456931101/10000000000 : ℝ)|^4791 ≤ (4628518763263/10000000000000 : ℝ)^3767
        have hw : |(5456931101/10000000000 : ℝ)|=(5456931101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518161697/1000000000 : ℝ)|^4791 ≤ (8667166985031/20000000000000 : ℝ)^3767
        have hw : |(518161697/1000000000 : ℝ)|=(518161697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s5_1 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83631303/156250000 : ℝ)*x 0 + (-114142257/625000000 : ℝ)*x 1 + (2590808539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83631303/156250000 : ℝ)^4791 ≤ (9032107174913/20000000000000 : ℝ)^3767 := by
    have hnat : (83631303 : ℕ)^4791*20000000000000^3767 ≤ 9032107174913^3767*156250000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83631303 156250000 9032107174913 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114142257/625000000 : ℝ)^4791 ≤ (1150362803681/10000000000000 : ℝ)^3767 := by
    have hnat : (114142257 : ℕ)^4791*10000000000000^3767 ≤ 1150362803681^3767*625000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114142257 625000000 1150362803681 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590808539/5000000000 : ℝ)^4791 ≤ (43335836073933/100000000000000 : ℝ)^3767 := by
    have hnat : (2590808539 : ℕ)^4791*100000000000000^3767 ≤ 43335836073933^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590808539 5000000000 43335836073933 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83631303/156250000 : ℝ), (-114142257/625000000 : ℝ), (2590808539/5000000000 : ℝ)] ![(9032107174913/20000000000000 : ℝ), (1150362803681/10000000000000 : ℝ), (43335836073933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83631303/156250000 : ℝ)|^4791 ≤ (9032107174913/20000000000000 : ℝ)^3767
        have hw : |(83631303/156250000 : ℝ)|=(83631303/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114142257/625000000 : ℝ)|^4791 ≤ (1150362803681/10000000000000 : ℝ)^3767
        have hw : |(-114142257/625000000 : ℝ)|=(114142257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590808539/5000000000 : ℝ)|^4791 ≤ (43335836073933/100000000000000 : ℝ)^3767
        have hw : |(2590808539/5000000000 : ℝ)|=(2590808539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s5_2 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352403517/10000000000 : ℝ)*x 0 + (1295404297/2500000000 : ℝ)*x 1 + (-1826275799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352403517/10000000000 : ℝ)^4791 ≤ (22580268607971/50000000000000 : ℝ)^3767 := by
    have hnat : (5352403517 : ℕ)^4791*50000000000000^3767 ≤ 22580268607971^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352403517 10000000000 22580268607971 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295404297/2500000000 : ℝ)^4791 ≤ (8667167448797/20000000000000 : ℝ)^3767 := by
    have hnat : (1295404297 : ℕ)^4791*20000000000000^3767 ≤ 8667167448797^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295404297 2500000000 8667167448797 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1826275799/10000000000 : ℝ)^4791 ≤ (11503625529297/100000000000000 : ℝ)^3767 := by
    have hnat : (1826275799 : ℕ)^4791*100000000000000^3767 ≤ 11503625529297^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826275799 10000000000 11503625529297 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352403517/10000000000 : ℝ), (1295404297/2500000000 : ℝ), (-1826275799/10000000000 : ℝ)] ![(22580268607971/50000000000000 : ℝ), (8667167448797/20000000000000 : ℝ), (11503625529297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352403517/10000000000 : ℝ)|^4791 ≤ (22580268607971/50000000000000 : ℝ)^3767
        have hw : |(5352403517/10000000000 : ℝ)|=(5352403517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295404297/2500000000 : ℝ)|^4791 ≤ (8667167448797/20000000000000 : ℝ)^3767
        have hw : |(1295404297/2500000000 : ℝ)|=(1295404297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1826275799/10000000000 : ℝ)|^4791 ≤ (11503625529297/100000000000000 : ℝ)^3767
        have hw : |(-1826275799/10000000000 : ℝ)|=(1826275799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s5_3 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206006283/10000000000 : ℝ)*x 0 + (6054277/15625000 : ℝ)*x 1 + (2279205181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206006283/10000000000 : ℝ)^4791 ≤ (6647446271787/20000000000000 : ℝ)^3767 := by
    have hnat : (4206006283 : ℕ)^4791*20000000000000^3767 ≤ 6647446271787^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206006283 10000000000 6647446271787 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6054277/15625000 : ℝ)^4791 ≤ (29944175782963/100000000000000 : ℝ)^3767 := by
    have hnat : (6054277 : ℕ)^4791*100000000000000^3767 ≤ 29944175782963^3767*15625000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6054277 15625000 29944175782963 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279205181/5000000000 : ℝ)^4791 ≤ (36818592844527/100000000000000 : ℝ)^3767 := by
    have hnat : (2279205181 : ℕ)^4791*100000000000000^3767 ≤ 36818592844527^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279205181 5000000000 36818592844527 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206006283/10000000000 : ℝ), (6054277/15625000 : ℝ), (2279205181/5000000000 : ℝ)] ![(6647446271787/20000000000000 : ℝ), (29944175782963/100000000000000 : ℝ), (36818592844527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206006283/10000000000 : ℝ)|^4791 ≤ (6647446271787/20000000000000 : ℝ)^3767
        have hw : |(4206006283/10000000000 : ℝ)|=(4206006283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6054277/15625000 : ℝ)|^4791 ≤ (29944175782963/100000000000000 : ℝ)^3767
        have hw : |(6054277/15625000 : ℝ)|=(6054277/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2279205181/5000000000 : ℝ)|^4791 ≤ (36818592844527/100000000000000 : ℝ)^3767
        have hw : |(2279205181/5000000000 : ℝ)|=(2279205181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s5_4 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1684432511/10000000000 : ℝ)*x 0 + (1295917357/2500000000 : ℝ)*x 1 + (545485711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1684432511/10000000000 : ℝ)^4791 ≤ (324359899587/3125000000000 : ℝ)^3767 := by
    have hnat : (1684432511 : ℕ)^4791*3125000000000^3767 ≤ 324359899587^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684432511 10000000000 324359899587 3125000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295917357/2500000000 : ℝ)^4791 ≤ (43357667756991/100000000000000 : ℝ)^3767 := by
    have hnat : (1295917357 : ℕ)^4791*100000000000000^3767 ≤ 43357667756991^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295917357 2500000000 43357667756991 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545485711/1000000000 : ℝ)^4791 ≤ (46262815440563/100000000000000 : ℝ)^3767 := by
    have hnat : (545485711 : ℕ)^4791*100000000000000^3767 ≤ 46262815440563^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545485711 1000000000 46262815440563 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1684432511/10000000000 : ℝ), (1295917357/2500000000 : ℝ), (545485711/1000000000 : ℝ)] ![(324359899587/3125000000000 : ℝ), (43357667756991/100000000000000 : ℝ), (46262815440563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1684432511/10000000000 : ℝ)|^4791 ≤ (324359899587/3125000000000 : ℝ)^3767
        have hw : |(-1684432511/10000000000 : ℝ)|=(1684432511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295917357/2500000000 : ℝ)|^4791 ≤ (43357667756991/100000000000000 : ℝ)^3767
        have hw : |(1295917357/2500000000 : ℝ)|=(1295917357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545485711/1000000000 : ℝ)|^4791 ≤ (46262815440563/100000000000000 : ℝ)^3767
        have hw : |(545485711/1000000000 : ℝ)|=(545485711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s5_5 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279185511/10000000000 : ℝ)*x 0 + (-1553035879/10000000000 : ℝ)*x 1 + (2727428637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279185511/10000000000 : ℝ)^4791 ≤ (22188149705593/50000000000000 : ℝ)^3767 := by
    have hnat : (5279185511 : ℕ)^4791*50000000000000^3767 ≤ 22188149705593^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279185511 10000000000 22188149705593 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553035879/10000000000 : ℝ)^4791 ≤ (4680441684171/50000000000000 : ℝ)^3767 := by
    have hnat : (1553035879 : ℕ)^4791*50000000000000^3767 ≤ 4680441684171^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553035879 10000000000 4680441684171 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727428637/5000000000 : ℝ)^4791 ≤ (5782852151193/12500000000000 : ℝ)^3767 := by
    have hnat : (2727428637 : ℕ)^4791*12500000000000^3767 ≤ 5782852151193^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727428637 5000000000 5782852151193 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279185511/10000000000 : ℝ), (-1553035879/10000000000 : ℝ), (2727428637/5000000000 : ℝ)] ![(22188149705593/50000000000000 : ℝ), (4680441684171/50000000000000 : ℝ), (5782852151193/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279185511/10000000000 : ℝ)|^4791 ≤ (22188149705593/50000000000000 : ℝ)^3767
        have hw : |(5279185511/10000000000 : ℝ)|=(5279185511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1553035879/10000000000 : ℝ)|^4791 ≤ (4680441684171/50000000000000 : ℝ)^3767
        have hw : |(-1553035879/10000000000 : ℝ)|=(1553035879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727428637/5000000000 : ℝ)|^4791 ≤ (5782852151193/12500000000000 : ℝ)^3767
        have hw : |(2727428637/5000000000 : ℝ)|=(2727428637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s5_6 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639592637/5000000000 : ℝ)*x 0 + (1090971473/2000000000 : ℝ)*x 1 + (-19412951/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639592637/5000000000 : ℝ)^4791 ≤ (69337963871/156250000000 : ℝ)^3767 := by
    have hnat : (2639592637 : ℕ)^4791*156250000000^3767 ≤ 69337963871^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639592637 5000000000 69337963871 156250000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090971473/2000000000 : ℝ)^4791 ≤ (5782852273889/12500000000000 : ℝ)^3767 := by
    have hnat : (1090971473 : ℕ)^4791*12500000000000^3767 ≤ 5782852273889^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090971473 2000000000 5782852273889 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19412951/125000000 : ℝ)^4791 ≤ (4680442454599/50000000000000 : ℝ)^3767 := by
    have hnat : (19412951 : ℕ)^4791*50000000000000^3767 ≤ 4680442454599^3767*125000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19412951 125000000 4680442454599 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639592637/5000000000 : ℝ), (1090971473/2000000000 : ℝ), (-19412951/125000000 : ℝ)] ![(69337963871/156250000000 : ℝ), (5782852273889/12500000000000 : ℝ), (4680442454599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639592637/5000000000 : ℝ)|^4791 ≤ (69337963871/156250000000 : ℝ)^3767
        have hw : |(2639592637/5000000000 : ℝ)|=(2639592637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090971473/2000000000 : ℝ)|^4791 ≤ (5782852273889/12500000000000 : ℝ)^3767
        have hw : |(1090971473/2000000000 : ℝ)|=(1090971473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19412951/125000000 : ℝ)|^4791 ≤ (4680442454599/50000000000000 : ℝ)^3767
        have hw : |(-19412951/125000000 : ℝ)|=(19412951/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s5_7 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (420617747/1000000000 : ℝ)*x 0 + (4553314047/10000000000 : ℝ)*x 1 + (3879886967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420617747/1000000000 : ℝ)^4791 ≤ (2077434492169/6250000000000 : ℝ)^3767 := by
    have hnat : (420617747 : ℕ)^4791*6250000000000^3767 ≤ 2077434492169^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420617747 1000000000 2077434492169 6250000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553314047/10000000000 : ℝ)^4791 ≤ (36766247921559/100000000000000 : ℝ)^3767 := by
    have hnat : (4553314047 : ℕ)^4791*100000000000000^3767 ≤ 36766247921559^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553314047 10000000000 36766247921559 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3879886967/10000000000 : ℝ)^4791 ≤ (29994800184787/100000000000000 : ℝ)^3767 := by
    have hnat : (3879886967 : ℕ)^4791*100000000000000^3767 ≤ 29994800184787^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3879886967 10000000000 29994800184787 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420617747/1000000000 : ℝ), (4553314047/10000000000 : ℝ), (3879886967/10000000000 : ℝ)] ![(2077434492169/6250000000000 : ℝ), (36766247921559/100000000000000 : ℝ), (29994800184787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420617747/1000000000 : ℝ)|^4791 ≤ (2077434492169/6250000000000 : ℝ)^3767
        have hw : |(420617747/1000000000 : ℝ)|=(420617747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553314047/10000000000 : ℝ)|^4791 ≤ (36766247921559/100000000000000 : ℝ)^3767
        have hw : |(4553314047/10000000000 : ℝ)|=(4553314047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3879886967/10000000000 : ℝ)|^4791 ≤ (29994800184787/100000000000000 : ℝ)^3767
        have hw : |(3879886967/10000000000 : ℝ)|=(3879886967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1618_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5243/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16327/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2041/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5243/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2041/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5243/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2041/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5243/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2041/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5243/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2041/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5243/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2041/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5243/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5243/50000 : ℝ) ^ (4787/1024 : ℝ) ≤ (2639625721744701/100000000000000000000 : ℝ) := by
    have hpowers : (5243/50000 : ℝ)^4787 ≤ (2639625721744701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5243 : ℕ)^4787*100000000000000000000^1024 ≤ 2639625721744701^1024*50000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5243 50000 2639625721744701 100000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5243/50000 : ℝ)) (X := (2639625721744701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2041/12500 : ℝ) ^ (4787/1024 : ℝ) ≤ (10461295375219049/50000000000000000000 : ℝ) := by
    have hpowers : (2041/12500 : ℝ)^4787 ≤ (10461295375219049/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2041 : ℕ)^4787*50000000000000000000^1024 ≤ 10461295375219049^1024*12500^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2041 12500 10461295375219049 50000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2041/12500 : ℝ)) (X := (10461295375219049/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002639625721744701/50000000000000000000 : ℝ) ≤ (5000056463769683/5000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (50002639625721744701/50000000000000000000 : ℝ)^1024 ≤ (5000056463769683/5000000000000000 : ℝ)^4787 := by
      have hnat : (50002639625721744701 : ℕ)^1024*5000000000000000^4787 ≤ 5000056463769683^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002639625721744701 50000000000000000000 5000056463769683 5000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000056463769683/5000000000000000 : ℝ)) (X := (50002639625721744701/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100023562216472182799/100000000000000000000 : ℝ) ≤ (5000251989508237/5000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (100023562216472182799/100000000000000000000 : ℝ)^1024 ≤ (5000251989508237/5000000000000000 : ℝ)^4787 := by
      have hnat : (100023562216472182799 : ℕ)^1024*5000000000000000^4787 ≤ 5000251989508237^4787*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100023562216472182799 100000000000000000000 5000251989508237 5000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000251989508237/5000000000000000 : ℝ)) (X := (100023562216472182799/100000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010461295375219049/25000000000000000000 : ℝ) ≤ (5000447515246791/5000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (25010461295375219049/25000000000000000000 : ℝ)^1024 ≤ (5000447515246791/5000000000000000 : ℝ)^4787 := by
      have hnat : (25010461295375219049 : ℕ)^1024*5000000000000000^4787 ≤ 5000447515246791^4787*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010461295375219049 25000000000000000000 5000447515246791 5000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000447515246791/5000000000000000 : ℝ)) (X := (25010461295375219049/25000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2639625721744701/100000000000000000000 : ℝ) ≤ ((14603114647776766799/14605000000000000000 : ℝ)+2*(97762869277/146050000000000 : ℝ)*(5243/50000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (14603114647776766799/14605000000000000000 : ℝ)+2*(97762869277/146050000000000 : ℝ)*(5243/50000 : ℝ)=(5000056463769683/5000000000000000 : ℝ) by norm_num, show 1+2*(2639625721744701/100000000000000000000 : ℝ)=(50002639625721744701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10461295375219049/50000000000000000000 : ℝ)+(2639625721744701/100000000000000000000 : ℝ) ≤ ((14603114647776766799/14605000000000000000 : ℝ)+(97762869277/146050000000000 : ℝ)*((2041/12500 : ℝ)+(5243/50000 : ℝ)))^(4787/1024 : ℝ) := by
    rw [show (14603114647776766799/14605000000000000000 : ℝ)+(97762869277/146050000000000 : ℝ)*((2041/12500 : ℝ)+(5243/50000 : ℝ))=(5000251989508237/5000000000000000 : ℝ) by norm_num, show 1+(10461295375219049/50000000000000000000 : ℝ)+(2639625721744701/100000000000000000000 : ℝ)=(100023562216472182799/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10461295375219049/50000000000000000000 : ℝ) ≤ ((14603114647776766799/14605000000000000000 : ℝ)+2*(97762869277/146050000000000 : ℝ)*(2041/12500 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (14603114647776766799/14605000000000000000 : ℝ)+2*(97762869277/146050000000000 : ℝ)*(2041/12500 : ℝ)=(5000447515246791/5000000000000000 : ℝ) by norm_num, show 1+2*(10461295375219049/50000000000000000000 : ℝ)=(25010461295375219049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14603114647776766799/14605000000000000000 : ℝ)*(X 1 0+X 2 0)+(97762869277/146050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (5243/50000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (14603114647776766799/14605000000000000000 : ℝ)) (alpha := (97762869277/146050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14603114647776766799/14605000000000000000 : ℝ)*(X 0 1+X 2 1)+(97762869277/146050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (5243/50000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (14603114647776766799/14605000000000000000 : ℝ)) (alpha := (97762869277/146050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14603114647776766799/14605000000000000000 : ℝ)*(X 0 2+X 1 2)+(97762869277/146050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (5243/50000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (14603114647776766799/14605000000000000000 : ℝ)) (alpha := (97762869277/146050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-210545461/1250000000 : ℝ)*X 0 0+(5456931101/10000000000 : ℝ)*X 0 1+(518161697/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83631303/156250000 : ℝ)*X 1 0+(-114142257/625000000 : ℝ)*X 1 1+(2590808539/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352403517/10000000000 : ℝ)*X 2 0+(1295404297/2500000000 : ℝ)*X 2 1+(-1826275799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206006283/10000000000 : ℝ)*X 0 0+(6054277/15625000 : ℝ)*X 0 1+(2279205181/5000000000 : ℝ)*X 0 2+(4206006283/10000000000 : ℝ)*X 1 0+(6054277/15625000 : ℝ)*X 1 1+(2279205181/5000000000 : ℝ)*X 1 2+(4206006283/10000000000 : ℝ)*X 2 0+(6054277/15625000 : ℝ)*X 2 1+(2279205181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1684432511/10000000000 : ℝ)*X 0 0+(1295917357/2500000000 : ℝ)*X 0 1+(545485711/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279185511/10000000000 : ℝ)*X 1 0+(-1553035879/10000000000 : ℝ)*X 1 1+(2727428637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639592637/5000000000 : ℝ)*X 2 0+(1090971473/2000000000 : ℝ)*X 2 1+(-19412951/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((420617747/1000000000 : ℝ)*X 0 0+(4553314047/10000000000 : ℝ)*X 0 1+(3879886967/10000000000 : ℝ)*X 0 2+(420617747/1000000000 : ℝ)*X 1 0+(4553314047/10000000000 : ℝ)*X 1 1+(3879886967/10000000000 : ℝ)*X 1 2+(420617747/1000000000 : ℝ)*X 2 0+(4553314047/10000000000 : ℝ)*X 2 1+(3879886967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20777740870933697445256599/2852539062500000000000000000000 : ℝ) := by norm_num
    linear_combination (272499681/25000000000000 : ℝ)*(base19) + (285139543/25000000000000 : ℝ)*(base23) + (9170819/50000000000000 : ℝ)*(lower2) + (1403889/10000000000000 : ℝ)*(upper3) + (120057501/50000000000000 : ℝ)*(upper5) + (79608603542113/3125000000000 : ℝ)*(major0) + (79608603542113/3125000000000 : ℝ)*(major1) + (79608603542113/3125000000000 : ℝ)*(major2) + (1816114271633689/50000000000000 : ℝ)*(sp0) + (3632247596448177/100000000000000 : ℝ)*(sp1) + (454030943236091/12500000000000 : ℝ)*(sp2) + (45709226650587/3125000000000 : ℝ)*(sp3) + (10071589761/50000000000000 : ℝ)*(sp4) + (201394729/3125000000000 : ℝ)*(sp7) + (11427357011329/781250000000 : ℝ)*(f.failure) + (36322486864469/1000000000000 : ℝ)*(f.sum) + (4837024468267/7302500000000000000000000000 : ℝ)*base65 + (34561695859990219/1984375000000000000000000000000 : ℝ)*base67 + (31229653347208969/1984375000000000000000000000000 : ℝ)*base69 + (14867353648708969/1984375000000000000000000000000 : ℝ)*base71 + (4112663358219/912812500000000000000000000 : ℝ)*base73 + (16535632844052719/1984375000000000000000000000000 : ℝ)*base75 + (20997405539583969/1984375000000000000000000000000 : ℝ)*base77 + (31255170949208969/1984375000000000000000000000000 : ℝ)*base79 + (3022283551187/1825625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (997417/78125000000000000000 : ℝ)*base90 + (997417/78125000000000000000 : ℝ)*base92 + (997417/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (595199615126843391333678651/73025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40883823/4000000000000 : ℝ)*(base19) + (996181569/100000000000000 : ℝ)*(base23) + (9274199/3125000000000 : ℝ)*(lower1) + (57064279/25000000000000 : ℝ)*(upper3) + (64848363/100000000000000 : ℝ)*(lower4) + (73696467/100000000000000 : ℝ)*(upper5) + (258620258648183/10000000000000 : ℝ)*(major0) + (258620258648183/10000000000000 : ℝ)*(major1) + (258620258648183/10000000000000 : ℝ)*(major2) + (302659983/25000000000000 : ℝ)*(sp2) + (3687466894859869/100000000000000 : ℝ)*(sp4) + (1843732936382147/50000000000000 : ℝ)*(sp5) + (3687464688038367/100000000000000 : ℝ)*(sp6) + (1484938006416181/100000000000000 : ℝ)*(sp7) + (1484938006416181/100000000000000 : ℝ)*(f.failure) + (3687466894859869/100000000000000 : ℝ)*(f.sum) + (7662278298367/2921000000000000000000000000 : ℝ)*base66 + (133829341846922879/6350000000000000000000000000000 : ℝ)*base67 + (35603594483377121/6350000000000000000000000000000 : ℝ)*base70 + (128447291745827121/6350000000000000000000000000000 : ℝ)*base72 + (12775340031837/2921000000000000000000000000 : ℝ)*base74 + (27634699867477121/6350000000000000000000000000000 : ℝ)*base76 + (4418483212627121/6350000000000000000000000000000 : ℝ)*base78 + (3759185179272879/6350000000000000000000000000000 : ℝ)*base79 + (2535576709663/584200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13413187/10000000000000000000000 : ℝ)*base89 + (13413187/10000000000000000000000 : ℝ)*base91 + (13413187/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1618_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5243/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16327/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1618_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1618_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16327/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1618_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1618_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1618_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16327/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1618_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
