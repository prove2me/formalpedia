-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1644_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:52.894854+00:00
-- url     : https://prove2.me/submissions/f7e4247f-2b15-4c41-b832-57449cdc5a5f

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
theorem support_rectangle_w1644_box_0 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1362164251/10000000000 : ℝ)*x 0 + (1352386033/2500000000 : ℝ)*x 1 + (2704771713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362164251/10000000000 : ℝ)^4895 ≤ (40195388373/500000000000 : ℝ)^3871 := by
    have hnat : (1362164251 : ℕ)^4895*500000000000^3871 ≤ 40195388373^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362164251 10000000000 40195388373 500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352386033/2500000000 : ℝ)^4895 ≤ (45980464951587/100000000000000 : ℝ)^3871 := by
    have hnat : (1352386033 : ℕ)^4895*100000000000000^3871 ≤ 45980464951587^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352386033 2500000000 45980464951587 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704771713/5000000000 : ℝ)^4895 ≤ (9196091472649/20000000000000 : ℝ)^3871 := by
    have hnat : (2704771713 : ℕ)^4895*20000000000000^3871 ≤ 9196091472649^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704771713 5000000000 9196091472649 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1362164251/10000000000 : ℝ), (1352386033/2500000000 : ℝ), (2704771713/5000000000 : ℝ)] ![(40195388373/500000000000 : ℝ), (45980464951587/100000000000000 : ℝ), (9196091472649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1362164251/10000000000 : ℝ)|^4895 ≤ (40195388373/500000000000 : ℝ)^3871
        have hw : |(-1362164251/10000000000 : ℝ)|=(1362164251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352386033/2500000000 : ℝ)|^4895 ≤ (45980464951587/100000000000000 : ℝ)^3871
        have hw : |(1352386033/2500000000 : ℝ)|=(1352386033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704771713/5000000000 : ℝ)|^4895 ≤ (9196091472649/20000000000000 : ℝ)^3871
        have hw : |(2704771713/5000000000 : ℝ)|=(2704771713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_1 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251158359/10000000000 : ℝ)*x 0 + (-792378701/5000000000 : ℝ)*x 1 + (2704771797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251158359/10000000000 : ℝ)^4895 ≤ (44284718193431/100000000000000 : ℝ)^3871 := by
    have hnat : (5251158359 : ℕ)^4895*100000000000000^3871 ≤ 44284718193431^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251158359 10000000000 44284718193431 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (792378701/5000000000 : ℝ)^4895 ≤ (152106603349/1562500000000 : ℝ)^3871 := by
    have hnat : (792378701 : ℕ)^4895*1562500000000^3871 ≤ 152106603349^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792378701 5000000000 152106603349 1562500000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704771797/5000000000 : ℝ)^4895 ≤ (45980459168969/100000000000000 : ℝ)^3871 := by
    have hnat : (2704771797 : ℕ)^4895*100000000000000^3871 ≤ 45980459168969^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704771797 5000000000 45980459168969 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251158359/10000000000 : ℝ), (-792378701/5000000000 : ℝ), (2704771797/5000000000 : ℝ)] ![(44284718193431/100000000000000 : ℝ), (152106603349/1562500000000 : ℝ), (45980459168969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251158359/10000000000 : ℝ)|^4895 ≤ (44284718193431/100000000000000 : ℝ)^3871
        have hw : |(5251158359/10000000000 : ℝ)|=(5251158359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-792378701/5000000000 : ℝ)|^4895 ≤ (152106603349/1562500000000 : ℝ)^3871
        have hw : |(-792378701/5000000000 : ℝ)|=(792378701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704771797/5000000000 : ℝ)|^4895 ≤ (45980459168969/100000000000000 : ℝ)^3871
        have hw : |(2704771797/5000000000 : ℝ)|=(2704771797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_2 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65639483/125000000 : ℝ)*x 0 + (5409543571/10000000000 : ℝ)*x 1 + (-198094631/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65639483/125000000 : ℝ)^4895 ≤ (5535590148759/12500000000000 : ℝ)^3871 := by
    have hnat : (65639483 : ℕ)^4895*12500000000000^3871 ≤ 5535590148759^3871*125000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65639483 125000000 5535590148759 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409543571/10000000000 : ℝ)^4895 ≤ (45980458921757/100000000000000 : ℝ)^3871 := by
    have hnat : (5409543571 : ℕ)^4895*100000000000000^3871 ≤ 45980458921757^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409543571 10000000000 45980458921757 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198094631/1250000000 : ℝ)^4895 ≤ (1946963972911/20000000000000 : ℝ)^3871 := by
    have hnat : (198094631 : ℕ)^4895*20000000000000^3871 ≤ 1946963972911^3871*1250000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198094631 1250000000 1946963972911 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65639483/125000000 : ℝ), (5409543571/10000000000 : ℝ), (-198094631/1250000000 : ℝ)] ![(5535590148759/12500000000000 : ℝ), (45980458921757/100000000000000 : ℝ), (1946963972911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65639483/125000000 : ℝ)|^4895 ≤ (5535590148759/12500000000000 : ℝ)^3871
        have hw : |(65639483/125000000 : ℝ)|=(65639483/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409543571/10000000000 : ℝ)|^4895 ≤ (45980458921757/100000000000000 : ℝ)^3871
        have hw : |(5409543571/10000000000 : ℝ)|=(5409543571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198094631/1250000000 : ℝ)|^4895 ≤ (1946963972911/20000000000000 : ℝ)^3871
        have hw : |(-198094631/1250000000 : ℝ)|=(198094631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_3 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4462578751/10000000000 : ℝ)*x 0 + (1014722629/2500000000 : ℝ)*x 1 + (811778153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462578751/10000000000 : ℝ)^4895 ≤ (9012192560539/25000000000000 : ℝ)^3871 := by
    have hnat : (4462578751 : ℕ)^4895*25000000000000^3871 ≤ 9012192560539^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462578751 10000000000 9012192560539 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014722629/2500000000 : ℝ)^4895 ≤ (3996951704077/12500000000000 : ℝ)^3871 := by
    have hnat : (1014722629 : ℕ)^4895*12500000000000^3871 ≤ 3996951704077^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014722629 2500000000 3996951704077 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (811778153/2000000000 : ℝ)^4895 ≤ (15987808056561/50000000000000 : ℝ)^3871 := by
    have hnat : (811778153 : ℕ)^4895*50000000000000^3871 ≤ 15987808056561^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811778153 2000000000 15987808056561 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462578751/10000000000 : ℝ), (1014722629/2500000000 : ℝ), (811778153/2000000000 : ℝ)] ![(9012192560539/25000000000000 : ℝ), (3996951704077/12500000000000 : ℝ), (15987808056561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462578751/10000000000 : ℝ)|^4895 ≤ (9012192560539/25000000000000 : ℝ)^3871
        have hw : |(4462578751/10000000000 : ℝ)|=(4462578751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014722629/2500000000 : ℝ)|^4895 ≤ (3996951704077/12500000000000 : ℝ)^3871
        have hw : |(1014722629/2500000000 : ℝ)|=(1014722629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(811778153/2000000000 : ℝ)|^4895 ≤ (15987808056561/50000000000000 : ℝ)^3871
        have hw : |(811778153/2000000000 : ℝ)|=(811778153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_4 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-236636339/1250000000 : ℝ)*x 0 + (1043115171/2000000000 : ℝ)*x 1 + (5215576361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236636339/1250000000 : ℝ)^4895 ≤ (6094397400051/50000000000000 : ℝ)^3871 := by
    have hnat : (236636339 : ℕ)^4895*50000000000000^3871 ≤ 6094397400051^3871*1250000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236636339 1250000000 6094397400051 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043115171/2000000000 : ℝ)^4895 ≤ (5488199987321/12500000000000 : ℝ)^3871 := by
    have hnat : (1043115171 : ℕ)^4895*12500000000000^3871 ≤ 5488199987321^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043115171 2000000000 5488199987321 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215576361/10000000000 : ℝ)^4895 ≤ (43905605284957/100000000000000 : ℝ)^3871 := by
    have hnat : (5215576361 : ℕ)^4895*100000000000000^3871 ≤ 43905605284957^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215576361 10000000000 43905605284957 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236636339/1250000000 : ℝ), (1043115171/2000000000 : ℝ), (5215576361/10000000000 : ℝ)] ![(6094397400051/50000000000000 : ℝ), (5488199987321/12500000000000 : ℝ), (43905605284957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236636339/1250000000 : ℝ)|^4895 ≤ (6094397400051/50000000000000 : ℝ)^3871
        have hw : |(-236636339/1250000000 : ℝ)|=(236636339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043115171/2000000000 : ℝ)|^4895 ≤ (5488199987321/12500000000000 : ℝ)^3871
        have hw : |(1043115171/2000000000 : ℝ)|=(1043115171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215576361/10000000000 : ℝ)|^4895 ≤ (43905605284957/100000000000000 : ℝ)^3871
        have hw : |(5215576361/10000000000 : ℝ)|=(5215576361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_5 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42065631/78125000 : ℝ)*x 0 + (-52117637/312500000 : ℝ)*x 1 + (5215576653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42065631/78125000 : ℝ)^4895 ≤ (22855190673417/50000000000000 : ℝ)^3871 := by
    have hnat : (42065631 : ℕ)^4895*50000000000000^3871 ≤ 22855190673417^3871*78125000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42065631 78125000 22855190673417 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52117637/312500000 : ℝ)^4895 ≤ (1038401024033/10000000000000 : ℝ)^3871 := by
    have hnat : (52117637 : ℕ)^4895*10000000000000^3871 ≤ 1038401024033^3871*312500000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52117637 312500000 1038401024033 10000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215576653/10000000000 : ℝ)^4895 ≤ (10976402098327/25000000000000 : ℝ)^3871 := by
    have hnat : (5215576653 : ℕ)^4895*25000000000000^3871 ≤ 10976402098327^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215576653 10000000000 10976402098327 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42065631/78125000 : ℝ), (-52117637/312500000 : ℝ), (5215576653/10000000000 : ℝ)] ![(22855190673417/50000000000000 : ℝ), (1038401024033/10000000000000 : ℝ), (10976402098327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42065631/78125000 : ℝ)|^4895 ≤ (22855190673417/50000000000000 : ℝ)^3871
        have hw : |(42065631/78125000 : ℝ)|=(42065631/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52117637/312500000 : ℝ)|^4895 ≤ (1038401024033/10000000000000 : ℝ)^3871
        have hw : |(-52117637/312500000 : ℝ)|=(52117637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215576653/10000000000 : ℝ)|^4895 ≤ (10976402098327/25000000000000 : ℝ)^3871
        have hw : |(5215576653/10000000000 : ℝ)|=(5215576653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_6 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384401169/10000000000 : ℝ)*x 0 + (1043115099/2000000000 : ℝ)*x 1 + (-416941351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384401169/10000000000 : ℝ)^4895 ≤ (22855192825809/50000000000000 : ℝ)^3871 := by
    have hnat : (5384401169 : ℕ)^4895*50000000000000^3871 ≤ 22855192825809^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384401169 10000000000 22855192825809 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043115099/2000000000 : ℝ)^4895 ≤ (8781119213271/20000000000000 : ℝ)^3871 := by
    have hnat : (1043115099 : ℕ)^4895*20000000000000^3871 ≤ 8781119213271^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043115099 2000000000 8781119213271 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416941351/2500000000 : ℝ)^4895 ≤ (5192009135577/50000000000000 : ℝ)^3871 := by
    have hnat : (416941351 : ℕ)^4895*50000000000000^3871 ≤ 5192009135577^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416941351 2500000000 5192009135577 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384401169/10000000000 : ℝ), (1043115099/2000000000 : ℝ), (-416941351/2500000000 : ℝ)] ![(22855192825809/50000000000000 : ℝ), (8781119213271/20000000000000 : ℝ), (5192009135577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384401169/10000000000 : ℝ)|^4895 ≤ (22855192825809/50000000000000 : ℝ)^3871
        have hw : |(5384401169/10000000000 : ℝ)|=(5384401169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043115099/2000000000 : ℝ)|^4895 ≤ (8781119213271/20000000000000 : ℝ)^3871
        have hw : |(1043115099/2000000000 : ℝ)|=(1043115099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416941351/2500000000 : ℝ)|^4895 ≤ (5192009135577/50000000000000 : ℝ)^3871
        have hw : |(-416941351/2500000000 : ℝ)|=(416941351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_7 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3901750013/10000000000 : ℝ)*x 0 + (4338977941/10000000000 : ℝ)*x 1 + (33898259/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3901750013/10000000000 : ℝ)^4895 ≤ (30418292999823/100000000000000 : ℝ)^3871 := by
    have hnat : (3901750013 : ℕ)^4895*100000000000000^3871 ≤ 30418292999823^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3901750013 10000000000 30418292999823 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4338977941/10000000000 : ℝ)^4895 ≤ (34790857491587/100000000000000 : ℝ)^3871 := by
    have hnat : (4338977941 : ℕ)^4895*100000000000000^3871 ≤ 34790857491587^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338977941 10000000000 34790857491587 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33898259/78125000 : ℝ)^4895 ≤ (17395424745847/50000000000000 : ℝ)^3871 := by
    have hnat : (33898259 : ℕ)^4895*50000000000000^3871 ≤ 17395424745847^3871*78125000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33898259 78125000 17395424745847 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3901750013/10000000000 : ℝ), (4338977941/10000000000 : ℝ), (33898259/78125000 : ℝ)] ![(30418292999823/100000000000000 : ℝ), (34790857491587/100000000000000 : ℝ), (17395424745847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3901750013/10000000000 : ℝ)|^4895 ≤ (30418292999823/100000000000000 : ℝ)^3871
        have hw : |(3901750013/10000000000 : ℝ)|=(3901750013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4338977941/10000000000 : ℝ)|^4895 ≤ (34790857491587/100000000000000 : ℝ)^3871
        have hw : |(4338977941/10000000000 : ℝ)|=(4338977941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33898259/78125000 : ℝ)|^4895 ≤ (17395424745847/50000000000000 : ℝ)^3871
        have hw : |(33898259/78125000 : ℝ)|=(33898259/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_8 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-889944109/5000000000 : ℝ)*x 0 + (634527097/1250000000 : ℝ)*x 1 + (679884113/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889944109/5000000000 : ℝ)^4895 ≤ (1409315678441/12500000000000 : ℝ)^3871 := by
    have hnat : (889944109 : ℕ)^4895*12500000000000^3871 ≤ 1409315678441^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889944109 5000000000 1409315678441 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634527097/1250000000 : ℝ)^4895 ≤ (10606848721139/25000000000000 : ℝ)^3871 := by
    have hnat : (634527097 : ℕ)^4895*25000000000000^3871 ≤ 10606848721139^3871*1250000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634527097 1250000000 10606848721139 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679884113/1250000000 : ℝ)^4895 ≤ (46298079675189/100000000000000 : ℝ)^3871 := by
    have hnat : (679884113 : ℕ)^4895*100000000000000^3871 ≤ 46298079675189^3871*1250000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679884113 1250000000 46298079675189 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889944109/5000000000 : ℝ), (634527097/1250000000 : ℝ), (679884113/1250000000 : ℝ)] ![(1409315678441/12500000000000 : ℝ), (10606848721139/25000000000000 : ℝ), (46298079675189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889944109/5000000000 : ℝ)|^4895 ≤ (1409315678441/12500000000000 : ℝ)^3871
        have hw : |(-889944109/5000000000 : ℝ)|=(889944109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(634527097/1250000000 : ℝ)|^4895 ≤ (10606848721139/25000000000000 : ℝ)^3871
        have hw : |(634527097/1250000000 : ℝ)|=(634527097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679884113/1250000000 : ℝ)|^4895 ≤ (46298079675189/100000000000000 : ℝ)^3871
        have hw : |(679884113/1250000000 : ℝ)|=(679884113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_9 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230872871/10000000000 : ℝ)*x 0 + (-314337377/2000000000 : ℝ)*x 1 + (5439074279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230872871/10000000000 : ℝ)^4895 ≤ (44068500323247/100000000000000 : ℝ)^3871 := by
    have hnat : (5230872871 : ℕ)^4895*100000000000000^3871 ≤ 44068500323247^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230872871 10000000000 44068500323247 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314337377/2000000000 : ℝ)^4895 ≤ (9633405193777/100000000000000 : ℝ)^3871 := by
    have hnat : (314337377 : ℕ)^4895*100000000000000^3871 ≤ 9633405193777^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314337377 2000000000 9633405193777 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439074279/10000000000 : ℝ)^4895 ≤ (23149047237741/50000000000000 : ℝ)^3871 := by
    have hnat : (5439074279 : ℕ)^4895*50000000000000^3871 ≤ 23149047237741^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439074279 10000000000 23149047237741 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230872871/10000000000 : ℝ), (-314337377/2000000000 : ℝ), (5439074279/10000000000 : ℝ)] ![(44068500323247/100000000000000 : ℝ), (9633405193777/100000000000000 : ℝ), (23149047237741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230872871/10000000000 : ℝ)|^4895 ≤ (44068500323247/100000000000000 : ℝ)^3871
        have hw : |(5230872871/10000000000 : ℝ)|=(5230872871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-314337377/2000000000 : ℝ)|^4895 ≤ (9633405193777/100000000000000 : ℝ)^3871
        have hw : |(-314337377/2000000000 : ℝ)|=(314337377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439074279/10000000000 : ℝ)|^4895 ≤ (23149047237741/50000000000000 : ℝ)^3871
        have hw : |(5439074279/10000000000 : ℝ)|=(5439074279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_10 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615436299/5000000000 : ℝ)*x 0 + (1359768499/2500000000 : ℝ)*x 1 + (-1571687653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615436299/5000000000 : ℝ)^4895 ≤ (440684974149/1000000000000 : ℝ)^3871 := by
    have hnat : (2615436299 : ℕ)^4895*1000000000000^3871 ≤ 440684974149^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615436299 5000000000 440684974149 1000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359768499/2500000000 : ℝ)^4895 ≤ (46298091429313/100000000000000 : ℝ)^3871 := by
    have hnat : (1359768499 : ℕ)^4895*100000000000000^3871 ≤ 46298091429313^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359768499 2500000000 46298091429313 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1571687653/10000000000 : ℝ)^4895 ≤ (2408352786587/25000000000000 : ℝ)^3871 := by
    have hnat : (1571687653 : ℕ)^4895*25000000000000^3871 ≤ 2408352786587^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571687653 10000000000 2408352786587 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615436299/5000000000 : ℝ), (1359768499/2500000000 : ℝ), (-1571687653/10000000000 : ℝ)] ![(440684974149/1000000000000 : ℝ), (46298091429313/100000000000000 : ℝ), (2408352786587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615436299/5000000000 : ℝ)|^4895 ≤ (440684974149/1000000000000 : ℝ)^3871
        have hw : |(2615436299/5000000000 : ℝ)|=(2615436299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359768499/2500000000 : ℝ)|^4895 ≤ (46298091429313/100000000000000 : ℝ)^3871
        have hw : |(1359768499/2500000000 : ℝ)|=(1359768499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1571687653/10000000000 : ℝ)|^4895 ≤ (2408352786587/25000000000000 : ℝ)^3871
        have hw : |(-1571687653/10000000000 : ℝ)|=(1571687653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_11 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2272788879/5000000000 : ℝ)*x 0 + (2008086911/5000000000 : ℝ)*x 1 + (4016172687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272788879/5000000000 : ℝ)^4895 ≤ (36898672945703/100000000000000 : ℝ)^3871 := by
    have hnat : (2272788879 : ℕ)^4895*100000000000000^3871 ≤ 36898672945703^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272788879 5000000000 36898672945703 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008086911/5000000000 : ℝ)^4895 ≤ (6310133832101/20000000000000 : ℝ)^3871 := by
    have hnat : (2008086911 : ℕ)^4895*20000000000000^3871 ≤ 6310133832101^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008086911 5000000000 6310133832101 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016172687/10000000000 : ℝ)^4895 ≤ (15775328942689/50000000000000 : ℝ)^3871 := by
    have hnat : (4016172687 : ℕ)^4895*50000000000000^3871 ≤ 15775328942689^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016172687 10000000000 15775328942689 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2272788879/5000000000 : ℝ), (2008086911/5000000000 : ℝ), (4016172687/10000000000 : ℝ)] ![(36898672945703/100000000000000 : ℝ), (6310133832101/20000000000000 : ℝ), (15775328942689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2272788879/5000000000 : ℝ)|^4895 ≤ (36898672945703/100000000000000 : ℝ)^3871
        have hw : |(2272788879/5000000000 : ℝ)|=(2272788879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008086911/5000000000 : ℝ)|^4895 ≤ (6310133832101/20000000000000 : ℝ)^3871
        have hw : |(2008086911/5000000000 : ℝ)|=(2008086911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016172687/10000000000 : ℝ)|^4895 ≤ (15775328942689/50000000000000 : ℝ)^3871
        have hw : |(4016172687/10000000000 : ℝ)|=(4016172687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_12 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1473675501/10000000000 : ℝ)*x 0 + (5543530407/10000000000 : ℝ)*x 1 + (5195744839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1473675501/10000000000 : ℝ)^4895 ≤ (555006778349/6250000000000 : ℝ)^3871 := by
    have hnat : (1473675501 : ℕ)^4895*6250000000000^3871 ≤ 555006778349^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473675501 10000000000 555006778349 6250000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5543530407/10000000000 : ℝ)^4895 ≤ (47425287265601/100000000000000 : ℝ)^3871 := by
    have hnat : (5543530407 : ℕ)^4895*100000000000000^3871 ≤ 47425287265601^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543530407 10000000000 47425287265601 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195744839/10000000000 : ℝ)^4895 ≤ (10923651066063/25000000000000 : ℝ)^3871 := by
    have hnat : (5195744839 : ℕ)^4895*25000000000000^3871 ≤ 10923651066063^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195744839 10000000000 10923651066063 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1473675501/10000000000 : ℝ), (5543530407/10000000000 : ℝ), (5195744839/10000000000 : ℝ)] ![(555006778349/6250000000000 : ℝ), (47425287265601/100000000000000 : ℝ), (10923651066063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1473675501/10000000000 : ℝ)|^4895 ≤ (555006778349/6250000000000 : ℝ)^3871
        have hw : |(-1473675501/10000000000 : ℝ)|=(1473675501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5543530407/10000000000 : ℝ)|^4895 ≤ (47425287265601/100000000000000 : ℝ)^3871
        have hw : |(5543530407/10000000000 : ℝ)|=(5543530407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195744839/10000000000 : ℝ)|^4895 ≤ (10923651066063/25000000000000 : ℝ)^3871
        have hw : |(5195744839/10000000000 : ℝ)|=(5195744839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_13 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699016987/5000000000 : ℝ)*x 0 + (-1675964483/10000000000 : ℝ)*x 1 + (649468067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699016987/5000000000 : ℝ)^4895 ≤ (45856784461727/100000000000000 : ℝ)^3871 := by
    have hnat : (2699016987 : ℕ)^4895*100000000000000^3871 ≤ 45856784461727^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699016987 5000000000 45856784461727 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1675964483/10000000000 : ℝ)^4895 ≤ (5224307241141/50000000000000 : ℝ)^3871 := by
    have hnat : (1675964483 : ℕ)^4895*50000000000000^3871 ≤ 5224307241141^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675964483 10000000000 5224307241141 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649468067/1250000000 : ℝ)^4895 ≤ (8738920208411/20000000000000 : ℝ)^3871 := by
    have hnat : (649468067 : ℕ)^4895*20000000000000^3871 ≤ 8738920208411^3871*1250000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649468067 1250000000 8738920208411 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699016987/5000000000 : ℝ), (-1675964483/10000000000 : ℝ), (649468067/1250000000 : ℝ)] ![(45856784461727/100000000000000 : ℝ), (5224307241141/50000000000000 : ℝ), (8738920208411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699016987/5000000000 : ℝ)|^4895 ≤ (45856784461727/100000000000000 : ℝ)^3871
        have hw : |(2699016987/5000000000 : ℝ)|=(2699016987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1675964483/10000000000 : ℝ)|^4895 ≤ (5224307241141/50000000000000 : ℝ)^3871
        have hw : |(-1675964483/10000000000 : ℝ)|=(1675964483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649468067/1250000000 : ℝ)|^4895 ≤ (8738920208411/20000000000000 : ℝ)^3871
        have hw : |(649468067/1250000000 : ℝ)|=(649468067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_14 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699017029/5000000000 : ℝ)*x 0 + (1298936057/2500000000 : ℝ)*x 1 + (-104747799/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699017029/5000000000 : ℝ)^4895 ≤ (573209817051/1250000000000 : ℝ)^3871 := by
    have hnat : (2699017029 : ℕ)^4895*1250000000000^3871 ≤ 573209817051^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699017029 5000000000 573209817051 1250000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298936057/2500000000 : ℝ)^4895 ≤ (21847298883343/50000000000000 : ℝ)^3871 := by
    have hnat : (1298936057 : ℕ)^4895*50000000000000^3871 ≤ 21847298883343^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298936057 2500000000 21847298883343 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104747799/625000000 : ℝ)^4895 ≤ (261215421381/2500000000000 : ℝ)^3871 := by
    have hnat : (104747799 : ℕ)^4895*2500000000000^3871 ≤ 261215421381^3871*625000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104747799 625000000 261215421381 2500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699017029/5000000000 : ℝ), (1298936057/2500000000 : ℝ), (-104747799/625000000 : ℝ)] ![(573209817051/1250000000000 : ℝ), (21847298883343/50000000000000 : ℝ), (261215421381/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699017029/5000000000 : ℝ)|^4895 ≤ (573209817051/1250000000000 : ℝ)^3871
        have hw : |(2699017029/5000000000 : ℝ)|=(2699017029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298936057/2500000000 : ℝ)|^4895 ≤ (21847298883343/50000000000000 : ℝ)^3871
        have hw : |(1298936057/2500000000 : ℝ)|=(1298936057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104747799/625000000 : ℝ)|^4895 ≤ (261215421381/2500000000000 : ℝ)^3871
        have hw : |(-104747799/625000000 : ℝ)|=(104747799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_box_15 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (120086931/312500000 : ℝ)*x 0 + (1091890637/2500000000 : ℝ)*x 1 + (1091890559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120086931/312500000 : ℝ)^4895 ≤ (14919064553817/50000000000000 : ℝ)^3871 := by
    have hnat : (120086931 : ℕ)^4895*50000000000000^3871 ≤ 14919064553817^3871*312500000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120086931 312500000 14919064553817 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091890637/2500000000 : ℝ)^4895 ≤ (17540468512793/50000000000000 : ℝ)^3871 := by
    have hnat : (1091890637 : ℕ)^4895*50000000000000^3871 ≤ 17540468512793^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091890637 2500000000 17540468512793 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091890559/2500000000 : ℝ)^4895 ≤ (35080933856631/100000000000000 : ℝ)^3871 := by
    have hnat : (1091890559 : ℕ)^4895*100000000000000^3871 ≤ 35080933856631^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091890559 2500000000 35080933856631 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(120086931/312500000 : ℝ), (1091890637/2500000000 : ℝ), (1091890559/2500000000 : ℝ)] ![(14919064553817/50000000000000 : ℝ), (17540468512793/50000000000000 : ℝ), (35080933856631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(120086931/312500000 : ℝ)|^4895 ≤ (14919064553817/50000000000000 : ℝ)^3871
        have hw : |(120086931/312500000 : ℝ)|=(120086931/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091890637/2500000000 : ℝ)|^4895 ≤ (17540468512793/50000000000000 : ℝ)^3871
        have hw : |(1091890637/2500000000 : ℝ)|=(1091890637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091890559/2500000000 : ℝ)|^4895 ≤ (35080933856631/100000000000000 : ℝ)^3871
        have hw : |(1091890559/2500000000 : ℝ)|=(1091890559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1644_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65043/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58561/100000 : ℝ) ∧ (81087/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17633/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10639/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10639/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10639/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10639/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10639/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10639/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10639/100000 : ℝ) ^ (4891/1024 : ℝ) ≤ (562420266784867/25000000000000000000 : ℝ) := by
    have hpowers : (10639/100000 : ℝ)^4891 ≤ (562420266784867/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10639 : ℕ)^4891*25000000000000000000^1024 ≤ 562420266784867^1024*100000^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10639 100000 562420266784867 25000000000000000000 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10639/100000 : ℝ)) (X := (562420266784867/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16279/100000 : ℝ) ^ (4891/1024 : ℝ) ≤ (2144640674544679/12500000000000000000 : ℝ) := by
    have hpowers : (16279/100000 : ℝ)^4891 ≤ (2144640674544679/12500000000000000000 : ℝ)^1024 := by
      have hnat : (16279 : ℕ)^4891*12500000000000000000^1024 ≤ 2144640674544679^1024*100000^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16279 100000 2144640674544679 12500000000000000000 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16279/100000 : ℝ)) (X := (2144640674544679/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500562420266784867/12500000000000000000 : ℝ) ≤ (312502943713503/312500000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (12500562420266784867/12500000000000000000 : ℝ)^1024 ≤ (312502943713503/312500000000000 : ℝ)^4891 := by
      have hnat : (12500562420266784867 : ℕ)^1024*312500000000000^4891 ≤ 312502943713503^4891*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500562420266784867 12500000000000000000 312502943713503 312500000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312502943713503/312500000000000 : ℝ)) (X := (12500562420266784867/12500000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000194068064634969/1000000000000000000 : ℝ) ≤ (5000203138881617/5000000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (1000194068064634969/1000000000000000000 : ℝ)^1024 ≤ (5000203138881617/5000000000000000 : ℝ)^4891 := by
      have hnat : (1000194068064634969 : ℕ)^1024*5000000000000000^4891 ≤ 5000203138881617^4891*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000194068064634969 1000000000000000000 5000203138881617 5000000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000203138881617/5000000000000000 : ℝ)) (X := (1000194068064634969/1000000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252144640674544679/6250000000000000000 : ℝ) ≤ (2500179589173593/2500000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (6252144640674544679/6250000000000000000 : ℝ)^1024 ≤ (2500179589173593/2500000000000000 : ℝ)^4891 := by
      have hnat : (6252144640674544679 : ℕ)^1024*2500000000000000^4891 ≤ 2500179589173593^4891*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252144640674544679 6250000000000000000 2500179589173593 2500000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500179589173593/2500000000000000 : ℝ)) (X := (6252144640674544679/6250000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(562420266784867/25000000000000000000 : ℝ) ≤ ((14098472716479066769/14100000000000000000 : ℝ)+2*(156039465569/282000000000000 : ℝ)*(10639/100000 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (14098472716479066769/14100000000000000000 : ℝ)+2*(156039465569/282000000000000 : ℝ)*(10639/100000 : ℝ)=(312502943713503/312500000000000 : ℝ) by norm_num, show 1+2*(562420266784867/25000000000000000000 : ℝ)=(12500562420266784867/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2144640674544679/12500000000000000000 : ℝ)+(562420266784867/25000000000000000000 : ℝ) ≤ ((14098472716479066769/14100000000000000000 : ℝ)+(156039465569/282000000000000 : ℝ)*((16279/100000 : ℝ)+(10639/100000 : ℝ)))^(4891/1024 : ℝ) := by
    rw [show (14098472716479066769/14100000000000000000 : ℝ)+(156039465569/282000000000000 : ℝ)*((16279/100000 : ℝ)+(10639/100000 : ℝ))=(5000203138881617/5000000000000000 : ℝ) by norm_num, show 1+(2144640674544679/12500000000000000000 : ℝ)+(562420266784867/25000000000000000000 : ℝ)=(1000194068064634969/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2144640674544679/12500000000000000000 : ℝ) ≤ ((14098472716479066769/14100000000000000000 : ℝ)+2*(156039465569/282000000000000 : ℝ)*(16279/100000 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (14098472716479066769/14100000000000000000 : ℝ)+2*(156039465569/282000000000000 : ℝ)*(16279/100000 : ℝ)=(2500179589173593/2500000000000000 : ℝ) by norm_num, show 1+2*(2144640674544679/12500000000000000000 : ℝ)=(6252144640674544679/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14098472716479066769/14100000000000000000 : ℝ)*(X 1 0+X 2 0)+(156039465569/282000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (10639/100000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (14098472716479066769/14100000000000000000 : ℝ)) (alpha := (156039465569/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14098472716479066769/14100000000000000000 : ℝ)*(X 0 1+X 2 1)+(156039465569/282000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (10639/100000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (14098472716479066769/14100000000000000000 : ℝ)) (alpha := (156039465569/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14098472716479066769/14100000000000000000 : ℝ)*(X 0 2+X 1 2)+(156039465569/282000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (10639/100000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (14098472716479066769/14100000000000000000 : ℝ)) (alpha := (156039465569/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1362164251/10000000000 : ℝ)*X 0 0+(1352386033/2500000000 : ℝ)*X 0 1+(2704771713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251158359/10000000000 : ℝ)*X 1 0+(-792378701/5000000000 : ℝ)*X 1 1+(2704771797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((65639483/125000000 : ℝ)*X 2 0+(5409543571/10000000000 : ℝ)*X 2 1+(-198094631/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4462578751/10000000000 : ℝ)*X 0 0+(1014722629/2500000000 : ℝ)*X 0 1+(811778153/2000000000 : ℝ)*X 0 2+(4462578751/10000000000 : ℝ)*X 1 0+(1014722629/2500000000 : ℝ)*X 1 1+(811778153/2000000000 : ℝ)*X 1 2+(4462578751/10000000000 : ℝ)*X 2 0+(1014722629/2500000000 : ℝ)*X 2 1+(811778153/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-236636339/1250000000 : ℝ)*X 0 0+(1043115171/2000000000 : ℝ)*X 0 1+(5215576361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42065631/78125000 : ℝ)*X 1 0+(-52117637/312500000 : ℝ)*X 1 1+(5215576653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5384401169/10000000000 : ℝ)*X 2 0+(1043115099/2000000000 : ℝ)*X 2 1+(-416941351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3901750013/10000000000 : ℝ)*X 0 0+(4338977941/10000000000 : ℝ)*X 0 1+(33898259/78125000 : ℝ)*X 0 2+(3901750013/10000000000 : ℝ)*X 1 0+(4338977941/10000000000 : ℝ)*X 1 1+(33898259/78125000 : ℝ)*X 1 2+(3901750013/10000000000 : ℝ)*X 2 0+(4338977941/10000000000 : ℝ)*X 2 1+(33898259/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-889944109/5000000000 : ℝ)*X 0 0+(634527097/1250000000 : ℝ)*X 0 1+(679884113/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230872871/10000000000 : ℝ)*X 1 0+(-314337377/2000000000 : ℝ)*X 1 1+(5439074279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615436299/5000000000 : ℝ)*X 2 0+(1359768499/2500000000 : ℝ)*X 2 1+(-1571687653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2272788879/5000000000 : ℝ)*X 0 0+(2008086911/5000000000 : ℝ)*X 0 1+(4016172687/10000000000 : ℝ)*X 0 2+(2272788879/5000000000 : ℝ)*X 1 0+(2008086911/5000000000 : ℝ)*X 1 1+(4016172687/10000000000 : ℝ)*X 1 2+(2272788879/5000000000 : ℝ)*X 2 0+(2008086911/5000000000 : ℝ)*X 2 1+(4016172687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1473675501/10000000000 : ℝ)*X 0 0+(5543530407/10000000000 : ℝ)*X 0 1+(5195744839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2699016987/5000000000 : ℝ)*X 1 0+(-1675964483/10000000000 : ℝ)*X 1 1+(649468067/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2699017029/5000000000 : ℝ)*X 2 0+(1298936057/2500000000 : ℝ)*X 2 1+(-104747799/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((120086931/312500000 : ℝ)*X 0 0+(1091890637/2500000000 : ℝ)*X 0 1+(1091890559/2500000000 : ℝ)*X 0 2+(120086931/312500000 : ℝ)*X 1 0+(1091890637/2500000000 : ℝ)*X 1 1+(1091890559/2500000000 : ℝ)*X 1 2+(120086931/312500000 : ℝ)*X 2 0+(1091890637/2500000000 : ℝ)*X 2 1+(1091890559/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65043/100000 : ℝ) ≤ (-3056897586412618288819829969/4700000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2605401/50000000000000 : ℝ)*(lower0) + (162121413/100000000000000 : ℝ)*(upper1) + (6993087/4000000000000 : ℝ)*(lower4) + (1747528737239399/100000000000000 : ℝ)*(major0) + (1747528737239399/100000000000000 : ℝ)*(major1) + (1747528737239399/100000000000000 : ℝ)*(major2) + (8365120723/100000000000000 : ℝ)*(sp2) + (223101021/100000000000000 : ℝ)*(sp3) + (2537098088760341/100000000000000 : ℝ)*(sp4) + (1268489493345779/50000000000000 : ℝ)*(sp5) + (126854586363899/5000000000000 : ℝ)*(sp6) + (979637283705399/100000000000000 : ℝ)*(sp7) + (2003638363/100000000000000 : ℝ)*(sp12) + (60552853573/50000000000000 : ℝ)*(sp13) + (48981875340321/5000000000000 : ℝ)*(f.failure) + (158568755774919/6250000000000 : ℝ)*(f.sum) + (8156964219269/14100000000000000000000000000 : ℝ)*base66 + (3979004582800018169/1410000000000000000000000000000000 : ℝ)*base68 + (305588107399981831/1410000000000000000000000000000000 : ℝ)*base69 + (13010941634950018169/1410000000000000000000000000000000 : ℝ)*base72 + (17085882232531/14100000000000000000000000000 : ℝ)*base73 + (2188831573120018169/1410000000000000000000000000000000 : ℝ)*base76 + (4123997930329981831/1410000000000000000000000000000000 : ℝ)*base77 + (7355630609029981831/1410000000000000000000000000000000 : ℝ)*base79 + (27324191001869/14100000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (528659/250000000000000000000 : ℝ)*base90 + (528659/250000000000000000000 : ℝ)*base92 + (528659/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58561/100000 : ℝ) ≤ (137624406385965789653480587261593/235000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99241729/50000000000000 : ℝ)*(lower1) + (47738041/25000000000000 : ℝ)*(lower2) + (155205923/100000000000000 : ℝ)*(lower5) + (1837094832878301/100000000000000 : ℝ)*(major0) + (1837094832878301/100000000000000 : ℝ)*(major1) + (1837094832878301/100000000000000 : ℝ)*(major2) + (104992854985647/4000000000000 : ℝ)*(sp0) + (2624769094639023/100000000000000 : ℝ)*(sp1) + (1312410400459847/50000000000000 : ℝ)*(sp2) + (64365188770617/6250000000000 : ℝ)*(sp3) + (160309029/20000000000000 : ℝ)*(sp6) + (3850566713/100000000000000 : ℝ)*(sp7) + (45564733/20000000000000 : ℝ)*(sp8) + (52507825817/100000000000000 : ℝ)*(sp9) + (205969374179317/20000000000000 : ℝ)*(f.failure) + (65620540061621/2500000000000 : ℝ)*(f.sum) + (13436368016777/4700000000000000000000000000 : ℝ)*base66 + (924940803097909823/470000000000000000000000000000000 : ℝ)*base67 + (634903266827909823/470000000000000000000000000000000 : ℝ)*base69 + (800668112497909823/470000000000000000000000000000000 : ℝ)*base71 + (1204196652377/4700000000000000000000000000 : ℝ)*base74 + (847676546177909823/470000000000000000000000000000000 : ℝ)*base75 + (1841353016027909823/470000000000000000000000000000000 : ℝ)*base77 + (2854962945867909823/470000000000000000000000000000000 : ℝ)*base79 + (7716671388623/4700000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2780143/1000000000000000000000 : ℝ)*base90 + (2780143/1000000000000000000000 : ℝ)*base92 + (2780143/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81087/100000 : ℝ) ≤ (47639841364640760563806352357303/58750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1068549/5000000000000 : ℝ)*(upper1) + (101369187/100000000000000 : ℝ)*(upper2) + (121072543/50000000000000 : ℝ)*(upper3) + (13576799/25000000000000 : ℝ)*(lower5) + (966690778448687/50000000000000 : ℝ)*(major0) + (966690778448687/50000000000000 : ℝ)*(major1) + (966690778448687/50000000000000 : ℝ)*(major2) + (29620137/1000000000000 : ℝ)*(sp0) + (28260460349/50000000000000 : ℝ)*(sp1) + (43637193197/100000000000000 : ℝ)*(sp2) + (2755906739529761/100000000000000 : ℝ)*(sp8) + (2755853180622763/100000000000000 : ℝ)*(sp9) + (344483258043783/12500000000000 : ℝ)*(sp10) + (216764743004623/20000000000000 : ℝ)*(sp11) + (216764743004623/20000000000000 : ℝ)*(f.failure) + (1377954850771731/50000000000000 : ℝ)*(f.sum) + (7382470324697/7050000000000000000000000000 : ℝ)*base66 + (5338242611321467697/705000000000000000000000000000000 : ℝ)*base68 + (3029662077836467697/705000000000000000000000000000000 : ℝ)*base70 + (3046413706916467697/705000000000000000000000000000000 : ℝ)*base72 + (31454301279047/7050000000000000000000000000 : ℝ)*base74 + (1926847933938532303/705000000000000000000000000000000 : ℝ)*base75 + (837550568801467697/705000000000000000000000000000000 : ℝ)*base78 + (1105664070296467697/705000000000000000000000000000000 : ℝ)*base80 + (18464341301053/7050000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (486883/1000000000000000000000 : ℝ)*base89 + (486883/1000000000000000000000 : ℝ)*base91 + (486883/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17633/20000 : ℝ) ≤ (-51795428579962767924101026471941/58750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (287472167/100000000000000 : ℝ)*(lower0) + (74284783/50000000000000 : ℝ)*(lower1) + (127388253/100000000000000 : ℝ)*(lower2) + (49007559/50000000000000 : ℝ)*(lower3) + (23665587/10000000000000 : ℝ)*(lower4) + (988576154480589/50000000000000 : ℝ)*(major0) + (988576154480589/50000000000000 : ℝ)*(major1) + (988576154480589/50000000000000 : ℝ)*(major2) + (13884244721/20000000000000 : ℝ)*(sp5) + (167289400449/100000000000000 : ℝ)*(sp6) + (1437665587681531/50000000000000 : ℝ)*(sp12) + (2875261754139457/100000000000000 : ℝ)*(sp13) + (1437581942981307/50000000000000 : ℝ)*(sp14) + (1108360919767779/100000000000000 : ℝ)*(sp15) + (1108360919767779/100000000000000 : ℝ)*(f.failure) + (1437665587681531/50000000000000 : ℝ)*(f.sum) + (6421264599053/2350000000000000000000000000 : ℝ)*base66 + (831762359274165647/235000000000000000000000000000000 : ℝ)*base67 + (1632016381314165647/235000000000000000000000000000000 : ℝ)*base69 + (1361980263274165647/235000000000000000000000000000000 : ℝ)*base71 + (4959129696303/2350000000000000000000000000 : ℝ)*base74 + (1001625591549165647/235000000000000000000000000000000 : ℝ)*base75 + (778820794450834353/235000000000000000000000000000000 : ℝ)*base78 + (9482551219165647/235000000000000000000000000000000 : ℝ)*base79 + (5466430910847/2350000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (20358759/5000000000000000000000 : ℝ)*base89 + (20358759/5000000000000000000000 : ℝ)*base91 + (20358759/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1644_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65043/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58561/100000 : ℝ) else (81087/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17633/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1644_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1644_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65043/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58561/100000 : ℝ) else (81087/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17633/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1644_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65043/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58561/100000 : ℝ) else (81087/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17633/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1644_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
