-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1118_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:08.72797+00:00
-- url     : https://prove2.me/submissions/5db1b519-621e-49b5-a624-cfb95816ce62

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
theorem support_rectangle_w1118_s0_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-949714987/5000000000 : ℝ)*x 0 + (1514973453/2500000000 : ℝ)*x 1 + (4777429531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (949714987/5000000000 : ℝ)^8311 ≤ (11034006035683/100000000000000 : ℝ)^6263 := by
    have hnat : (949714987 : ℕ)^8311*100000000000000^6263 ≤ 11034006035683^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949714987 5000000000 11034006035683 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514973453/2500000000 : ℝ)^8311 ≤ (51443571058779/100000000000000 : ℝ)^6263 := by
    have hnat : (1514973453 : ℕ)^8311*100000000000000^6263 ≤ 51443571058779^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514973453 2500000000 51443571058779 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4777429531/10000000000 : ℝ)^8311 ≤ (9380605721313/25000000000000 : ℝ)^6263 := by
    have hnat : (4777429531 : ℕ)^8311*25000000000000^6263 ≤ 9380605721313^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4777429531 10000000000 9380605721313 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-949714987/5000000000 : ℝ), (1514973453/2500000000 : ℝ), (4777429531/10000000000 : ℝ)] ![(11034006035683/100000000000000 : ℝ), (51443571058779/100000000000000 : ℝ), (9380605721313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-949714987/5000000000 : ℝ)|^8311 ≤ (11034006035683/100000000000000 : ℝ)^6263
        have hw : |(-949714987/5000000000 : ℝ)|=(949714987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1514973453/2500000000 : ℝ)|^8311 ≤ (51443571058779/100000000000000 : ℝ)^6263
        have hw : |(1514973453/2500000000 : ℝ)|=(1514973453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4777429531/10000000000 : ℝ)|^8311 ≤ (9380605721313/25000000000000 : ℝ)^6263
        have hw : |(4777429531/10000000000 : ℝ)|=(4777429531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s0_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518145443/10000000000 : ℝ)*x 0 + (-527221241/2000000000 : ℝ)*x 1 + (477742957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518145443/10000000000 : ℝ)^8311 ≤ (45431757976099/100000000000000 : ℝ)^6263 := by
    have hnat : (5518145443 : ℕ)^8311*100000000000000^6263 ≤ 45431757976099^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518145443 10000000000 45431757976099 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527221241/2000000000 : ℝ)^8311 ≤ (4261454677841/25000000000000 : ℝ)^6263 := by
    have hnat : (527221241 : ℕ)^8311*25000000000000^6263 ≤ 4261454677841^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527221241 2000000000 4261454677841 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477742957/1000000000 : ℝ)^8311 ≤ (1500896931669/4000000000000 : ℝ)^6263 := by
    have hnat : (477742957 : ℕ)^8311*4000000000000^6263 ≤ 1500896931669^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477742957 1000000000 1500896931669 4000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518145443/10000000000 : ℝ), (-527221241/2000000000 : ℝ), (477742957/1000000000 : ℝ)] ![(45431757976099/100000000000000 : ℝ), (4261454677841/25000000000000 : ℝ), (1500896931669/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518145443/10000000000 : ℝ)|^8311 ≤ (45431757976099/100000000000000 : ℝ)^6263
        have hw : |(5518145443/10000000000 : ℝ)|=(5518145443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527221241/2000000000 : ℝ)|^8311 ≤ (4261454677841/25000000000000 : ℝ)^6263
        have hw : |(-527221241/2000000000 : ℝ)|=(527221241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477742957/1000000000 : ℝ)|^8311 ≤ (1500896931669/4000000000000 : ℝ)^6263
        have hw : |(477742957/1000000000 : ℝ)|=(477742957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s0_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103629119/2000000000 : ℝ)*x 0 + (1194357357/2500000000 : ℝ)*x 1 + (-527221237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103629119/2000000000 : ℝ)^8311 ≤ (45431759636759/100000000000000 : ℝ)^6263 := by
    have hnat : (1103629119 : ℕ)^8311*100000000000000^6263 ≤ 45431759636759^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103629119 2000000000 45431759636759 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194357357/2500000000 : ℝ)^8311 ≤ (7504484362349/20000000000000 : ℝ)^6263 := by
    have hnat : (1194357357 : ℕ)^8311*20000000000000^6263 ≤ 7504484362349^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194357357 2500000000 7504484362349 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527221237/2000000000 : ℝ)^8311 ≤ (4261454634937/25000000000000 : ℝ)^6263 := by
    have hnat : (527221237 : ℕ)^8311*25000000000000^6263 ≤ 4261454634937^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527221237 2000000000 4261454634937 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103629119/2000000000 : ℝ), (1194357357/2500000000 : ℝ), (-527221237/2000000000 : ℝ)] ![(45431759636759/100000000000000 : ℝ), (7504484362349/20000000000000 : ℝ), (4261454634937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103629119/2000000000 : ℝ)|^8311 ≤ (45431759636759/100000000000000 : ℝ)^6263
        have hw : |(1103629119/2000000000 : ℝ)|=(1103629119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194357357/2500000000 : ℝ)|^8311 ≤ (7504484362349/20000000000000 : ℝ)^6263
        have hw : |(1194357357/2500000000 : ℝ)|=(1194357357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527221237/2000000000 : ℝ)|^8311 ≤ (4261454634937/25000000000000 : ℝ)^6263
        have hw : |(-527221237/2000000000 : ℝ)|=(527221237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s0_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4202939027/10000000000 : ℝ)*x 0 + (3122216589/10000000000 : ℝ)*x 1 + (566164121/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202939027/10000000000 : ℝ)^8311 ≤ (6331185025407/20000000000000 : ℝ)^6263 := by
    have hnat : (4202939027 : ℕ)^8311*20000000000000^6263 ≤ 6331185025407^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202939027 10000000000 6331185025407 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122216589/10000000000 : ℝ)^8311 ≤ (10668970683033/50000000000000 : ℝ)^6263 := by
    have hnat : (3122216589 : ℕ)^8311*50000000000000^6263 ≤ 10668970683033^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122216589 10000000000 10668970683033 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566164121/1000000000 : ℝ)^8311 ≤ (11751533373433/25000000000000 : ℝ)^6263 := by
    have hnat : (566164121 : ℕ)^8311*25000000000000^6263 ≤ 11751533373433^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566164121 1000000000 11751533373433 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202939027/10000000000 : ℝ), (3122216589/10000000000 : ℝ), (566164121/1000000000 : ℝ)] ![(6331185025407/20000000000000 : ℝ), (10668970683033/50000000000000 : ℝ), (11751533373433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202939027/10000000000 : ℝ)|^8311 ≤ (6331185025407/20000000000000 : ℝ)^6263
        have hw : |(4202939027/10000000000 : ℝ)|=(4202939027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122216589/10000000000 : ℝ)|^8311 ≤ (10668970683033/50000000000000 : ℝ)^6263
        have hw : |(3122216589/10000000000 : ℝ)|=(3122216589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566164121/1000000000 : ℝ)|^8311 ≤ (11751533373433/25000000000000 : ℝ)^6263
        have hw : |(566164121/1000000000 : ℝ)|=(566164121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s0_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1904647791/10000000000 : ℝ)*x 0 + (4810525413/10000000000 : ℝ)*x 1 + (6025635399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1904647791/10000000000 : ℝ)^8311 ≤ (11074246644239/100000000000000 : ℝ)^6263 := by
    have hnat : (1904647791 : ℕ)^8311*100000000000000^6263 ≤ 11074246644239^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904647791 10000000000 11074246644239 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810525413/10000000000 : ℝ)^8311 ≤ (37867751271867/100000000000000 : ℝ)^6263 := by
    have hnat : (4810525413 : ℕ)^8311*100000000000000^6263 ≤ 37867751271867^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810525413 10000000000 37867751271867 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6025635399/10000000000 : ℝ)^8311 ≤ (3191125130037/6250000000000 : ℝ)^6263 := by
    have hnat : (6025635399 : ℕ)^8311*6250000000000^6263 ≤ 3191125130037^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6025635399 10000000000 3191125130037 6250000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1904647791/10000000000 : ℝ), (4810525413/10000000000 : ℝ), (6025635399/10000000000 : ℝ)] ![(11074246644239/100000000000000 : ℝ), (37867751271867/100000000000000 : ℝ), (3191125130037/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1904647791/10000000000 : ℝ)|^8311 ≤ (11074246644239/100000000000000 : ℝ)^6263
        have hw : |(-1904647791/10000000000 : ℝ)|=(1904647791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810525413/10000000000 : ℝ)|^8311 ≤ (37867751271867/100000000000000 : ℝ)^6263
        have hw : |(4810525413/10000000000 : ℝ)|=(4810525413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6025635399/10000000000 : ℝ)|^8311 ≤ (3191125130037/6250000000000 : ℝ)^6263
        have hw : |(6025635399/10000000000 : ℝ)|=(6025635399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s0_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169788459/10000000000 : ℝ)*x 0 + (-1387901111/10000000000 : ℝ)*x 1 + (753204817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169788459/10000000000 : ℝ)^8311 ≤ (41665674343509/100000000000000 : ℝ)^6263 := by
    have hnat : (5169788459 : ℕ)^8311*100000000000000^6263 ≤ 41665674343509^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169788459 10000000000 41665674343509 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387901111/10000000000 : ℝ)^8311 ≤ (7276288286977/100000000000000 : ℝ)^6263 := by
    have hnat : (1387901111 : ℕ)^8311*100000000000000^6263 ≤ 7276288286977^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387901111 10000000000 7276288286977 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753204817/1250000000 : ℝ)^8311 ≤ (51058037353917/100000000000000 : ℝ)^6263 := by
    have hnat : (753204817 : ℕ)^8311*100000000000000^6263 ≤ 51058037353917^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753204817 1250000000 51058037353917 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169788459/10000000000 : ℝ), (-1387901111/10000000000 : ℝ), (753204817/1250000000 : ℝ)] ![(41665674343509/100000000000000 : ℝ), (7276288286977/100000000000000 : ℝ), (51058037353917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169788459/10000000000 : ℝ)|^8311 ≤ (41665674343509/100000000000000 : ℝ)^6263
        have hw : |(5169788459/10000000000 : ℝ)|=(5169788459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1387901111/10000000000 : ℝ)|^8311 ≤ (7276288286977/100000000000000 : ℝ)^6263
        have hw : |(-1387901111/10000000000 : ℝ)|=(1387901111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753204817/1250000000 : ℝ)|^8311 ≤ (51058037353917/100000000000000 : ℝ)^6263
        have hw : |(753204817/1250000000 : ℝ)|=(753204817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s0_6 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292448109/2500000000 : ℝ)*x 0 + (6025635823/10000000000 : ℝ)*x 1 + (-693949691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292448109/2500000000 : ℝ)^8311 ≤ (41665716877111/100000000000000 : ℝ)^6263 := by
    have hnat : (1292448109 : ℕ)^8311*100000000000000^6263 ≤ 41665716877111^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292448109 2500000000 41665716877111 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6025635823/10000000000 : ℝ)^8311 ≤ (51058006848169/100000000000000 : ℝ)^6263 := by
    have hnat : (6025635823 : ℕ)^8311*100000000000000^6263 ≤ 51058006848169^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6025635823 10000000000 51058006848169 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693949691/5000000000 : ℝ)^8311 ≤ (90953453229/1250000000000 : ℝ)^6263 := by
    have hnat : (693949691 : ℕ)^8311*1250000000000^6263 ≤ 90953453229^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693949691 5000000000 90953453229 1250000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292448109/2500000000 : ℝ), (6025635823/10000000000 : ℝ), (-693949691/5000000000 : ℝ)] ![(41665716877111/100000000000000 : ℝ), (51058006848169/100000000000000 : ℝ), (90953453229/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292448109/2500000000 : ℝ)|^8311 ≤ (41665716877111/100000000000000 : ℝ)^6263
        have hw : |(1292448109/2500000000 : ℝ)|=(1292448109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6025635823/10000000000 : ℝ)|^8311 ≤ (51058006848169/100000000000000 : ℝ)^6263
        have hw : |(6025635823/10000000000 : ℝ)|=(6025635823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-693949691/5000000000 : ℝ)|^8311 ≤ (90953453229/1250000000000 : ℝ)^6263
        have hw : |(-693949691/5000000000 : ℝ)|=(693949691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s0_7 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (168530693/400000000 : ℝ)*x 0 + (5596111049/10000000000 : ℝ)*x 1 + (1595023961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168530693/400000000 : ℝ)^8311 ≤ (31759195539777/100000000000000 : ℝ)^6263 := by
    have hnat : (168530693 : ℕ)^8311*100000000000000^6263 ≤ 31759195539777^6263*400000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168530693 400000000 31759195539777 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5596111049/10000000000 : ℝ)^8311 ≤ (23142762398751/50000000000000 : ℝ)^6263 := by
    have hnat : (5596111049 : ℕ)^8311*50000000000000^6263 ≤ 23142762398751^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596111049 10000000000 23142762398751 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595023961/5000000000 : ℝ)^8311 ≤ (21955279651187/100000000000000 : ℝ)^6263 := by
    have hnat : (1595023961 : ℕ)^8311*100000000000000^6263 ≤ 21955279651187^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595023961 5000000000 21955279651187 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168530693/400000000 : ℝ), (5596111049/10000000000 : ℝ), (1595023961/5000000000 : ℝ)] ![(31759195539777/100000000000000 : ℝ), (23142762398751/50000000000000 : ℝ), (21955279651187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168530693/400000000 : ℝ)|^8311 ≤ (31759195539777/100000000000000 : ℝ)^6263
        have hw : |(168530693/400000000 : ℝ)|=(168530693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5596111049/10000000000 : ℝ)|^8311 ≤ (23142762398751/50000000000000 : ℝ)^6263
        have hw : |(5596111049/10000000000 : ℝ)|=(5596111049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595023961/5000000000 : ℝ)|^8311 ≤ (21955279651187/100000000000000 : ℝ)^6263
        have hw : |(1595023961/5000000000 : ℝ)|=(1595023961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (157/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27907/100000 : ℝ)*pair X 0 0 := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
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
  have hpowlo : (0 : ℝ) ^ (4155/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4155 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4155*1^1024 ≤ 0^1024*1^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4155/1024 : ℝ) ≤ (121417639534901937/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4155 ≤ (121417639534901937/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4155*5000000000000000000^1024 ≤ 121417639534901937^1024*5^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 121417639534901937 5000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (121417639534901937/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4155 := by
      have hnat : (1 : ℕ)^1024*1^4155 ≤ 1^4155*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5121417639534901937/5000000000000000000 : ℝ) ≤ (2514826712542213/2500000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (5121417639534901937/5000000000000000000 : ℝ)^1024 ≤ (2514826712542213/2500000000000000 : ℝ)^4155 := by
      have hnat : (5121417639534901937 : ℕ)^1024*2500000000000000^4155 ≤ 2514826712542213^4155*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5121417639534901937 5000000000000000000 2514826712542213 2500000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514826712542213/2500000000000000 : ℝ)) (X := (5121417639534901937/5000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2621417639534901937/2500000000000000000 : ℝ) ≤ (1264826712542213/1250000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (2621417639534901937/2500000000000000000 : ℝ)^1024 ≤ (1264826712542213/1250000000000000 : ℝ)^4155 := by
      have hnat : (2621417639534901937 : ℕ)^1024*1250000000000000^4155 ≤ 1264826712542213^4155*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2621417639534901937 2500000000000000000 1264826712542213 1250000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264826712542213/1250000000000000 : ℝ)) (X := (2621417639534901937/2500000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14826712542213/1000000000000000 : ℝ)*(0 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14826712542213/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(121417639534901937/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14826712542213/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14826712542213/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514826712542213/2500000000000000 : ℝ) by norm_num, show 1+(121417639534901937/5000000000000000000 : ℝ)+(0 : ℝ)=(5121417639534901937/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(121417639534901937/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14826712542213/1000000000000000 : ℝ)*(2/5 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14826712542213/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264826712542213/1250000000000000 : ℝ) by norm_num, show 1+2*(121417639534901937/5000000000000000000 : ℝ)=(2621417639534901937/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14826712542213/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14826712542213/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14826712542213/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14826712542213/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14826712542213/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14826712542213/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-949714987/5000000000 : ℝ)*X 0 0+(1514973453/2500000000 : ℝ)*X 0 1+(4777429531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518145443/10000000000 : ℝ)*X 1 0+(-527221241/2000000000 : ℝ)*X 1 1+(477742957/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103629119/2000000000 : ℝ)*X 2 0+(1194357357/2500000000 : ℝ)*X 2 1+(-527221237/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4202939027/10000000000 : ℝ)*X 0 0+(3122216589/10000000000 : ℝ)*X 0 1+(566164121/1000000000 : ℝ)*X 0 2+(4202939027/10000000000 : ℝ)*X 1 0+(3122216589/10000000000 : ℝ)*X 1 1+(566164121/1000000000 : ℝ)*X 1 2+(4202939027/10000000000 : ℝ)*X 2 0+(3122216589/10000000000 : ℝ)*X 2 1+(566164121/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1904647791/10000000000 : ℝ)*X 0 0+(4810525413/10000000000 : ℝ)*X 0 1+(6025635399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5169788459/10000000000 : ℝ)*X 1 0+(-1387901111/10000000000 : ℝ)*X 1 1+(753204817/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292448109/2500000000 : ℝ)*X 2 0+(6025635823/10000000000 : ℝ)*X 2 1+(-693949691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168530693/400000000 : ℝ)*X 0 0+(5596111049/10000000000 : ℝ)*X 0 1+(1595023961/5000000000 : ℝ)*X 0 2+(168530693/400000000 : ℝ)*X 1 0+(5596111049/10000000000 : ℝ)*X 1 1+(1595023961/5000000000 : ℝ)*X 1 2+(168530693/400000000 : ℝ)*X 2 0+(5596111049/10000000000 : ℝ)*X 2 1+(1595023961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1576927870363681718589/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14090131/20000000000000 : ℝ)*(base1) + (780565789/50000000000000 : ℝ)*(base19) + (735354081/50000000000000 : ℝ)*(base23) + (55951083/50000000000000 : ℝ)*(base24) + (90182457/25000000000000 : ℝ)*(upper3) + (11735519377301/2000000000000 : ℝ)*(major0) + (11735519377301/2000000000000 : ℝ)*(major1) + (11735519377301/2000000000000 : ℝ)*(major2) + (155950794386433/20000000000000 : ℝ)*(sp0) + (779755736952159/100000000000000 : ℝ)*(sp1) + (190370047723/24414062500 : ℝ)*(sp2) + (393791598605917/100000000000000 : ℝ)*(sp3) + (1698301113/50000000000000 : ℝ)*(sp4) + (43130199/1562500000000 : ℝ)*(sp7) + (98448607347327/25000000000000 : ℝ)*(f.failure) + (779757298083737/100000000000000 : ℝ)*(f.sum) + (2084340975887/1000000000000000000000000000 : ℝ)*base66 + (4706742482887/2000000000000000000000000000 : ℝ)*base68 + (67517394887/2000000000000000000000000000 : ℝ)*base70 + (13495434284887/2000000000000000000000000000 : ℝ)*base72 + (383525925113/1000000000000000000000000000 : ℝ)*base73 + (13216275076887/2000000000000000000000000000 : ℝ)*base76 + (7095386930887/2000000000000000000000000000 : ℝ)*base78 + (4582779094887/2000000000000000000000000000 : ℝ)*base80 + (3278149174887/1000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (4426837/500000000000000000000 : ℝ)*base89 + (4426837/500000000000000000000 : ℝ)*base91 + (4426837/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1945316264287766631/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (315414753/100000000000000 : ℝ)*(base13) + (138601977/20000000000000 : ℝ)*(base23) + (97396177/100000000000000 : ℝ)*(base39) + (66403973/50000000000000 : ℝ)*(upper3) + (53860727/100000000000000 : ℝ)*(upper4) + (33625787/25000000000000 : ℝ)*(upper5) + (619292952097317/100000000000000 : ℝ)*(major0) + (619292952097317/100000000000000 : ℝ)*(major1) + (30964642735057/5000000000000 : ℝ)*(major2) + (1031426833/100000000000000 : ℝ)*(sp2) + (822968346706633/100000000000000 : ℝ)*(sp4) + (411484331060693/50000000000000 : ℝ)*(sp5) + (205741758770211/25000000000000 : ℝ)*(sp6) + (41561707983319/10000000000000 : ℝ)*(sp7) + (41561707983319/10000000000000 : ℝ)*(f.failure) + (411484379758781/50000000000000 : ℝ)*(f.sum) + (169143091065341/100000000000000000000000000000 : ℝ)*base65 + (28416516233859/5000000000000000000000000000 : ℝ)*base68 + (469336028157479/100000000000000000000000000000 : ℝ)*base70 + (24113117158859/5000000000000000000000000000 : ℝ)*base72 + (251079349365341/100000000000000000000000000000 : ℝ)*base73 + (881178961057479/100000000000000000000000000000 : ℝ)*base76 + (87529090357479/100000000000000000000000000000 : ℝ)*base78 + (770075998057479/100000000000000000000000000000 : ℝ)*base80 + (88955713192521/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1333789/200000000000000000000 : ℝ)*base89 + (1333789/200000000000000000000 : ℝ)*base91 + (1333789/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1118_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (157/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27907/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1118_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1118_s1_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105831679/10000000000 : ℝ)*x 0 + (5707965359/10000000000 : ℝ)*x 1 + (999441809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105831679/10000000000 : ℝ)^8311 ≤ (3163175633069/25000000000000 : ℝ)^6263 := by
    have hnat : (2105831679 : ℕ)^8311*25000000000000^6263 ≤ 3163175633069^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105831679 10000000000 3163175633069 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5707965359/10000000000 : ℝ)^8311 ≤ (47517191321179/100000000000000 : ℝ)^6263 := by
    have hnat : (5707965359 : ℕ)^8311*100000000000000^6263 ≤ 47517191321179^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707965359 10000000000 47517191321179 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999441809/2000000000 : ℝ)^8311 ≤ (39830106134687/100000000000000 : ℝ)^6263 := by
    have hnat : (999441809 : ℕ)^8311*100000000000000^6263 ≤ 39830106134687^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999441809 2000000000 39830106134687 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105831679/10000000000 : ℝ), (5707965359/10000000000 : ℝ), (999441809/2000000000 : ℝ)] ![(3163175633069/25000000000000 : ℝ), (47517191321179/100000000000000 : ℝ), (39830106134687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105831679/10000000000 : ℝ)|^8311 ≤ (3163175633069/25000000000000 : ℝ)^6263
        have hw : |(-2105831679/10000000000 : ℝ)|=(2105831679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5707965359/10000000000 : ℝ)|^8311 ≤ (47517191321179/100000000000000 : ℝ)^6263
        have hw : |(5707965359/10000000000 : ℝ)|=(5707965359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(999441809/2000000000 : ℝ)|^8311 ≤ (39830106134687/100000000000000 : ℝ)^6263
        have hw : |(999441809/2000000000 : ℝ)|=(999441809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s1_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2710220127/5000000000 : ℝ)*x 0 + (-2489867169/10000000000 : ℝ)*x 1 + (4997208871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710220127/5000000000 : ℝ)^8311 ≤ (44367392532823/100000000000000 : ℝ)^6263 := by
    have hnat : (2710220127 : ℕ)^8311*100000000000000^6263 ≤ 44367392532823^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710220127 5000000000 44367392532823 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2489867169/10000000000 : ℝ)^8311 ≤ (7901251574529/50000000000000 : ℝ)^6263 := by
    have hnat : (2489867169 : ℕ)^8311*50000000000000^6263 ≤ 7901251574529^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489867169 10000000000 7901251574529 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4997208871/10000000000 : ℝ)^8311 ≤ (19915052147161/50000000000000 : ℝ)^6263 := by
    have hnat : (4997208871 : ℕ)^8311*50000000000000^6263 ≤ 19915052147161^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997208871 10000000000 19915052147161 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710220127/5000000000 : ℝ), (-2489867169/10000000000 : ℝ), (4997208871/10000000000 : ℝ)] ![(44367392532823/100000000000000 : ℝ), (7901251574529/50000000000000 : ℝ), (19915052147161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710220127/5000000000 : ℝ)|^8311 ≤ (44367392532823/100000000000000 : ℝ)^6263
        have hw : |(2710220127/5000000000 : ℝ)|=(2710220127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2489867169/10000000000 : ℝ)|^8311 ≤ (7901251574529/50000000000000 : ℝ)^6263
        have hw : |(-2489867169/10000000000 : ℝ)|=(2489867169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4997208871/10000000000 : ℝ)|^8311 ≤ (19915052147161/50000000000000 : ℝ)^6263
        have hw : |(4997208871/10000000000 : ℝ)|=(4997208871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s1_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355110429/2500000000 : ℝ)*x 0 + (31232547/62500000 : ℝ)*x 1 + (-2489866981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355110429/2500000000 : ℝ)^8311 ≤ (44367408412717/100000000000000 : ℝ)^6263 := by
    have hnat : (1355110429 : ℕ)^8311*100000000000000^6263 ≤ 44367408412717^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355110429 2500000000 44367408412717 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31232547/62500000 : ℝ)^8311 ≤ (39830090005049/100000000000000 : ℝ)^6263 := by
    have hnat : (31232547 : ℕ)^8311*100000000000000^6263 ≤ 39830090005049^6263*62500000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31232547 62500000 39830090005049 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2489866981/10000000000 : ℝ)^8311 ≤ (7901250782851/50000000000000 : ℝ)^6263 := by
    have hnat : (2489866981 : ℕ)^8311*50000000000000^6263 ≤ 7901250782851^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489866981 10000000000 7901250782851 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355110429/2500000000 : ℝ), (31232547/62500000 : ℝ), (-2489866981/10000000000 : ℝ)] ![(44367408412717/100000000000000 : ℝ), (39830090005049/100000000000000 : ℝ), (7901250782851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355110429/2500000000 : ℝ)|^8311 ≤ (44367408412717/100000000000000 : ℝ)^6263
        have hw : |(1355110429/2500000000 : ℝ)|=(1355110429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31232547/62500000 : ℝ)|^8311 ≤ (39830090005049/100000000000000 : ℝ)^6263
        have hw : |(31232547/62500000 : ℝ)|=(31232547/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2489866981/10000000000 : ℝ)|^8311 ≤ (7901250782851/50000000000000 : ℝ)^6263
        have hw : |(-2489866981/10000000000 : ℝ)|=(2489866981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s1_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319465341/10000000000 : ℝ)*x 0 + (1836259353/5000000000 : ℝ)*x 1 + (1269973713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319465341/10000000000 : ℝ)^8311 ≤ (32825825745789/100000000000000 : ℝ)^6263 := by
    have hnat : (4319465341 : ℕ)^8311*100000000000000^6263 ≤ 32825825745789^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319465341 10000000000 32825825745789 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1836259353/5000000000 : ℝ)^8311 ≤ (26467158575731/100000000000000 : ℝ)^6263 := by
    have hnat : (1836259353 : ℕ)^8311*100000000000000^6263 ≤ 26467158575731^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836259353 5000000000 26467158575731 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269973713/2500000000 : ℝ)^8311 ≤ (20353507834699/50000000000000 : ℝ)^6263 := by
    have hnat : (1269973713 : ℕ)^8311*50000000000000^6263 ≤ 20353507834699^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269973713 2500000000 20353507834699 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319465341/10000000000 : ℝ), (1836259353/5000000000 : ℝ), (1269973713/2500000000 : ℝ)] ![(32825825745789/100000000000000 : ℝ), (26467158575731/100000000000000 : ℝ), (20353507834699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319465341/10000000000 : ℝ)|^8311 ≤ (32825825745789/100000000000000 : ℝ)^6263
        have hw : |(4319465341/10000000000 : ℝ)|=(4319465341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1836259353/5000000000 : ℝ)|^8311 ≤ (26467158575731/100000000000000 : ℝ)^6263
        have hw : |(1836259353/5000000000 : ℝ)|=(1836259353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269973713/2500000000 : ℝ)|^8311 ≤ (20353507834699/50000000000000 : ℝ)^6263
        have hw : |(1269973713/2500000000 : ℝ)|=(1269973713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s1_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263333989/1250000000 : ℝ)*x 0 + (250350151/500000000 : ℝ)*x 1 + (2848987903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263333989/1250000000 : ℝ)^8311 ≤ (12659402281957/100000000000000 : ℝ)^6263 := by
    have hnat : (263333989 : ℕ)^8311*100000000000000^6263 ≤ 12659402281957^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263333989 1250000000 12659402281957 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250350151/500000000 : ℝ)^8311 ≤ (39933728354279/100000000000000 : ℝ)^6263 := by
    have hnat : (250350151 : ℕ)^8311*100000000000000^6263 ≤ 39933728354279^6263*500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250350151 500000000 39933728354279 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2848987903/5000000000 : ℝ)^8311 ≤ (47406869347539/100000000000000 : ℝ)^6263 := by
    have hnat : (2848987903 : ℕ)^8311*100000000000000^6263 ≤ 47406869347539^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848987903 5000000000 47406869347539 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263333989/1250000000 : ℝ), (250350151/500000000 : ℝ), (2848987903/5000000000 : ℝ)] ![(12659402281957/100000000000000 : ℝ), (39933728354279/100000000000000 : ℝ), (47406869347539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263333989/1250000000 : ℝ)|^8311 ≤ (12659402281957/100000000000000 : ℝ)^6263
        have hw : |(-263333989/1250000000 : ℝ)|=(263333989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250350151/500000000 : ℝ)|^8311 ≤ (39933728354279/100000000000000 : ℝ)^6263
        have hw : |(250350151/500000000 : ℝ)|=(250350151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2848987903/5000000000 : ℝ)|^8311 ≤ (47406869347539/100000000000000 : ℝ)^6263
        have hw : |(2848987903/5000000000 : ℝ)|=(2848987903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s1_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309609027/2500000000 : ℝ)*x 0 + (-89454993/500000000 : ℝ)*x 1 + (5697975589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309609027/2500000000 : ℝ)^8311 ≤ (10600360735399/25000000000000 : ℝ)^6263 := by
    have hnat : (1309609027 : ℕ)^8311*25000000000000^6263 ≤ 10600360735399^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309609027 2500000000 10600360735399 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89454993/500000000 : ℝ)^8311 ≤ (10191690093859/100000000000000 : ℝ)^6263 := by
    have hnat : (89454993 : ℕ)^8311*100000000000000^6263 ≤ 10191690093859^6263*500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89454993 500000000 10191690093859 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5697975589/10000000000 : ℝ)^8311 ≤ (9481373390347/20000000000000 : ℝ)^6263 := by
    have hnat : (5697975589 : ℕ)^8311*20000000000000^6263 ≤ 9481373390347^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697975589 10000000000 9481373390347 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309609027/2500000000 : ℝ), (-89454993/500000000 : ℝ), (5697975589/10000000000 : ℝ)] ![(10600360735399/25000000000000 : ℝ), (10191690093859/100000000000000 : ℝ), (9481373390347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309609027/2500000000 : ℝ)|^8311 ≤ (10600360735399/25000000000000 : ℝ)^6263
        have hw : |(1309609027/2500000000 : ℝ)|=(1309609027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89454993/500000000 : ℝ)|^8311 ≤ (10191690093859/100000000000000 : ℝ)^6263
        have hw : |(-89454993/500000000 : ℝ)|=(89454993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5697975589/10000000000 : ℝ)|^8311 ≤ (9481373390347/20000000000000 : ℝ)^6263
        have hw : |(5697975589/10000000000 : ℝ)|=(5697975589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s1_6 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5238436141/10000000000 : ℝ)*x 0 + (5697975741/10000000000 : ℝ)*x 1 + (-1789099591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238436141/10000000000 : ℝ)^8311 ≤ (42401443296053/100000000000000 : ℝ)^6263 := by
    have hnat : (5238436141 : ℕ)^8311*100000000000000^6263 ≤ 42401443296053^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238436141 10000000000 42401443296053 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5697975741/10000000000 : ℝ)^8311 ≤ (47406868629901/100000000000000 : ℝ)^6263 := by
    have hnat : (5697975741 : ℕ)^8311*100000000000000^6263 ≤ 47406868629901^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697975741 10000000000 47406868629901 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1789099591/10000000000 : ℝ)^8311 ≤ (10191688060403/100000000000000 : ℝ)^6263 := by
    have hnat : (1789099591 : ℕ)^8311*100000000000000^6263 ≤ 10191688060403^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789099591 10000000000 10191688060403 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238436141/10000000000 : ℝ), (5697975741/10000000000 : ℝ), (-1789099591/10000000000 : ℝ)] ![(42401443296053/100000000000000 : ℝ), (47406868629901/100000000000000 : ℝ), (10191688060403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238436141/10000000000 : ℝ)|^8311 ≤ (42401443296053/100000000000000 : ℝ)^6263
        have hw : |(5238436141/10000000000 : ℝ)|=(5238436141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5697975741/10000000000 : ℝ)|^8311 ≤ (47406868629901/100000000000000 : ℝ)^6263
        have hw : |(5697975741/10000000000 : ℝ)|=(5697975741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1789099591/10000000000 : ℝ)|^8311 ≤ (10191688060403/100000000000000 : ℝ)^6263
        have hw : |(-1789099591/10000000000 : ℝ)|=(1789099591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s1_7 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (216056351/500000000 : ℝ)*x 0 + (1265125607/2500000000 : ℝ)*x 1 + (738459643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216056351/500000000 : ℝ)^8311 ≤ (32842584085159/100000000000000 : ℝ)^6263 := by
    have hnat : (216056351 : ℕ)^8311*100000000000000^6263 ≤ 32842584085159^6263*500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216056351 500000000 32842584085159 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265125607/2500000000 : ℝ)^8311 ≤ (20250465396009/50000000000000 : ℝ)^6263 := by
    have hnat : (1265125607 : ℕ)^8311*50000000000000^6263 ≤ 20250465396009^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265125607 2500000000 20250465396009 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738459643/2000000000 : ℝ)^8311 ≤ (5331297021779/20000000000000 : ℝ)^6263 := by
    have hnat : (738459643 : ℕ)^8311*20000000000000^6263 ≤ 5331297021779^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738459643 2000000000 5331297021779 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216056351/500000000 : ℝ), (1265125607/2500000000 : ℝ), (738459643/2000000000 : ℝ)] ![(32842584085159/100000000000000 : ℝ), (20250465396009/50000000000000 : ℝ), (5331297021779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216056351/500000000 : ℝ)|^8311 ≤ (32842584085159/100000000000000 : ℝ)^6263
        have hw : |(216056351/500000000 : ℝ)|=(216056351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1265125607/2500000000 : ℝ)|^8311 ≤ (20250465396009/50000000000000 : ℝ)^6263
        have hw : |(1265125607/2500000000 : ℝ)|=(1265125607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738459643/2000000000 : ℝ)|^8311 ≤ (5331297021779/20000000000000 : ℝ)^6263
        have hw : |(738459643/2000000000 : ℝ)|=(738459643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (157/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2757/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20547/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (157/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (157/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (157/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (157/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (157/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (157/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (157/50000 : ℝ) ^ (4155/1024 : ℝ) ≤ (697426939/10000000000000000000 : ℝ) := by
    have hpowers : (157/50000 : ℝ)^4155 ≤ (697426939/10000000000000000000 : ℝ)^1024 := by
      have hnat : (157 : ℕ)^4155*10000000000000000000^1024 ≤ 697426939^1024*50000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        157 50000 697426939 10000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (157/50000 : ℝ)) (X := (697426939/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27907/100000 : ℝ) ^ (4155/1024 : ℝ) ≤ (563528857170569031/100000000000000000000 : ℝ) := by
    have hpowers : (27907/100000 : ℝ)^4155 ≤ (563528857170569031/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27907 : ℕ)^4155*100000000000000000000^1024 ≤ 563528857170569031^1024*100000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27907 100000 563528857170569031 100000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27907/100000 : ℝ)) (X := (563528857170569031/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000000697426939/5000000000000000000 : ℝ) ≤ (5000000000171881/5000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (5000000000697426939/5000000000000000000 : ℝ)^1024 ≤ (5000000000171881/5000000000000000 : ℝ)^4155 := by
      have hnat : (5000000000697426939 : ℕ)^1024*5000000000000000^4155 ≤ 5000000000171881^4155*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000000697426939 5000000000000000000 5000000000171881 5000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000171881/5000000000000000 : ℝ)) (X := (5000000000697426939/5000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100563528864144838421/100000000000000000000 : ℝ) ≤ (2503464695284933/2500000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (100563528864144838421/100000000000000000000 : ℝ)^1024 ≤ (2503464695284933/2500000000000000 : ℝ)^4155 := by
      have hnat : (100563528864144838421 : ℕ)^1024*2500000000000000^4155 ≤ 2503464695284933^4155*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100563528864144838421 100000000000000000000 2503464695284933 2500000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503464695284933/2500000000000000 : ℝ)) (X := (100563528864144838421/100000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50563528857170569031/50000000000000000000 : ℝ) ≤ (5013858780967851/5000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50563528857170569031/50000000000000000000 : ℝ)^1024 ≤ (5013858780967851/5000000000000000 : ℝ)^4155 := by
      have hnat : (50563528857170569031 : ℕ)^1024*5000000000000000^4155 ≤ 5013858780967851^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50563528857170569031 50000000000000000000 5013858780967851 5000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013858780967851/5000000000000000 : ℝ)) (X := (50563528857170569031/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(697426939/10000000000000000000 : ℝ) ≤ ((137960648347572777853/137965000000000000000 : ℝ)+2*(1385878079597/275930000000000 : ℝ)*(157/50000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (137960648347572777853/137965000000000000000 : ℝ)+2*(1385878079597/275930000000000 : ℝ)*(157/50000 : ℝ)=(5000000000171881/5000000000000000 : ℝ) by norm_num, show 1+2*(697426939/10000000000000000000 : ℝ)=(5000000000697426939/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(563528857170569031/100000000000000000000 : ℝ)+(697426939/10000000000000000000 : ℝ) ≤ ((137960648347572777853/137965000000000000000 : ℝ)+(1385878079597/275930000000000 : ℝ)*((27907/100000 : ℝ)+(157/50000 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (137960648347572777853/137965000000000000000 : ℝ)+(1385878079597/275930000000000 : ℝ)*((27907/100000 : ℝ)+(157/50000 : ℝ))=(2503464695284933/2500000000000000 : ℝ) by norm_num, show 1+(563528857170569031/100000000000000000000 : ℝ)+(697426939/10000000000000000000 : ℝ)=(100563528864144838421/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(563528857170569031/100000000000000000000 : ℝ) ≤ ((137960648347572777853/137965000000000000000 : ℝ)+2*(1385878079597/275930000000000 : ℝ)*(27907/100000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (137960648347572777853/137965000000000000000 : ℝ)+2*(1385878079597/275930000000000 : ℝ)*(27907/100000 : ℝ)=(5013858780967851/5000000000000000 : ℝ) by norm_num, show 1+2*(563528857170569031/100000000000000000000 : ℝ)=(50563528857170569031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137960648347572777853/137965000000000000000 : ℝ)*(X 1 0+X 2 0)+(1385878079597/275930000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (157/50000 : ℝ)) (hi := (27907/100000 : ℝ)) (c := (137960648347572777853/137965000000000000000 : ℝ)) (alpha := (1385878079597/275930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137960648347572777853/137965000000000000000 : ℝ)*(X 0 1+X 2 1)+(1385878079597/275930000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (157/50000 : ℝ)) (hi := (27907/100000 : ℝ)) (c := (137960648347572777853/137965000000000000000 : ℝ)) (alpha := (1385878079597/275930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137960648347572777853/137965000000000000000 : ℝ)*(X 0 2+X 1 2)+(1385878079597/275930000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (157/50000 : ℝ)) (hi := (27907/100000 : ℝ)) (c := (137960648347572777853/137965000000000000000 : ℝ)) (alpha := (1385878079597/275930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105831679/10000000000 : ℝ)*X 0 0+(5707965359/10000000000 : ℝ)*X 0 1+(999441809/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2710220127/5000000000 : ℝ)*X 1 0+(-2489867169/10000000000 : ℝ)*X 1 1+(4997208871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355110429/2500000000 : ℝ)*X 2 0+(31232547/62500000 : ℝ)*X 2 1+(-2489866981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319465341/10000000000 : ℝ)*X 0 0+(1836259353/5000000000 : ℝ)*X 0 1+(1269973713/2500000000 : ℝ)*X 0 2+(4319465341/10000000000 : ℝ)*X 1 0+(1836259353/5000000000 : ℝ)*X 1 1+(1269973713/2500000000 : ℝ)*X 1 2+(4319465341/10000000000 : ℝ)*X 2 0+(1836259353/5000000000 : ℝ)*X 2 1+(1269973713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-263333989/1250000000 : ℝ)*X 0 0+(250350151/500000000 : ℝ)*X 0 1+(2848987903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309609027/2500000000 : ℝ)*X 1 0+(-89454993/500000000 : ℝ)*X 1 1+(5697975589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5238436141/10000000000 : ℝ)*X 2 0+(5697975741/10000000000 : ℝ)*X 2 1+(-1789099591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216056351/500000000 : ℝ)*X 0 0+(1265125607/2500000000 : ℝ)*X 0 1+(738459643/2000000000 : ℝ)*X 0 2+(216056351/500000000 : ℝ)*X 1 0+(1265125607/2500000000 : ℝ)*X 1 1+(738459643/2000000000 : ℝ)*X 1 2+(216056351/500000000 : ℝ)*X 2 0+(1265125607/2500000000 : ℝ)*X 2 1+(738459643/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24027846406471139138167419591/3449125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78204837/25000000000000 : ℝ)*(base1) + (1238129221/100000000000000 : ℝ)*(base19) + (1617613947/100000000000000 : ℝ)*(base23) + (31152039/100000000000000 : ℝ)*(upper3) + (24822803/12500000000000 : ℝ)*(upper5) + (1058753390332151/100000000000000 : ℝ)*(major0) + (1058753390332151/100000000000000 : ℝ)*(major1) + (1058753390332151/100000000000000 : ℝ)*(major2) + (703477634514257/50000000000000 : ℝ)*(sp0) + (703479766245961/50000000000000 : ℝ)*(sp1) + (1406959153007197/100000000000000 : ℝ)*(sp2) + (35527196272507/5000000000000 : ℝ)*(sp3) + (5814411977/100000000000000 : ℝ)*(sp4) + (769780831/50000000000000 : ℝ)*(sp7) + (710545777831151/100000000000000 : ℝ)*(f.failure) + (175870096327643/12500000000000 : ℝ)*(f.sum) + (4496260333243/3449125000000000000000000000 : ℝ)*base65 + (160143779818727151803/13796500000000000000000000000000000 : ℝ)*base67 + (28592787017087151803/13796500000000000000000000000000000 : ℝ)*base69 + (87458548576668151803/13796500000000000000000000000000000 : ℝ)*base71 + (124780763243/27593000000000000000000000 : ℝ)*base73 + (86980920589732151803/13796500000000000000000000000000000 : ℝ)*base75 + (52575452259992151803/13796500000000000000000000000000000 : ℝ)*base77 + (27545246177163848197/13796500000000000000000000000000000 : ℝ)*base80 + (7639596188807/5518600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6831781/2000000000000000000000 : ℝ)*base89 + (6831781/2000000000000000000000 : ℝ)*base91 + (6831781/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13556928303609584663543005773/1724562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93436961/100000000000000 : ℝ)*(base1) + (873236481/50000000000000 : ℝ)*(base19) + (221773527/12500000000000 : ℝ)*(base23) + (173514879/100000000000000 : ℝ)*(upper3) + (44347593/25000000000000 : ℝ)*(upper5) + (544530108763453/50000000000000 : ℝ)*(major0) + (544530108763453/50000000000000 : ℝ)*(major1) + (544530108763453/50000000000000 : ℝ)*(major2) + (7037675813/100000000000000 : ℝ)*(sp1) + (7572911241/100000000000000 : ℝ)*(sp2) + (723617554042373/50000000000000 : ℝ)*(sp4) + (1447226230499011/100000000000000 : ℝ)*(sp5) + (180903208443541/12500000000000 : ℝ)*(sp6) + (182721266233243/25000000000000 : ℝ)*(sp7) + (730885158369933/100000000000000 : ℝ)*(f.failure) + (723617507323893/50000000000000 : ℝ)*(f.sum) + (1049981459429/1379650000000000000000000000 : ℝ)*base65 + (5607142009552706409/6898250000000000000000000000000000 : ℝ)*base67 + (82180398221362706409/6898250000000000000000000000000000 : ℝ)*base69 + (8122308338707793591/6898250000000000000000000000000000 : ℝ)*base72 + (20594424024477/27593000000000000000000000000 : ℝ)*base73 + (25568362139533206409/6898250000000000000000000000000000 : ℝ)*base75 + (39661965200391706409/6898250000000000000000000000000000 : ℝ)*base77 + (32724780511636706409/6898250000000000000000000000000000 : ℝ)*base79 + (139129990994141/27593000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (205777/2000000000000000000000 : ℝ)*base90 + (205777/2000000000000000000000 : ℝ)*base92 + (205777/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1118_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (157/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2757/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20547/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1118_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1118_s2_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160359219/10000000000 : ℝ)*x 0 + (2757720319/5000000000 : ℝ)*x 1 + (257754277/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160359219/10000000000 : ℝ)^8311 ≤ (13089289376593/100000000000000 : ℝ)^6263 := by
    have hnat : (2160359219 : ℕ)^8311*100000000000000^6263 ≤ 13089289376593^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160359219 10000000000 13089289376593 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757720319/5000000000 : ℝ)^8311 ≤ (1418819039791/3125000000000 : ℝ)^6263 := by
    have hnat : (2757720319 : ℕ)^8311*3125000000000^6263 ≤ 1418819039791^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757720319 5000000000 1418819039791 3125000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257754277/500000000 : ℝ)^8311 ≤ (41508501338389/100000000000000 : ℝ)^6263 := by
    have hnat : (257754277 : ℕ)^8311*100000000000000^6263 ≤ 41508501338389^6263*500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257754277 500000000 41508501338389 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160359219/10000000000 : ℝ), (2757720319/5000000000 : ℝ), (257754277/500000000 : ℝ)] ![(13089289376593/100000000000000 : ℝ), (1418819039791/3125000000000 : ℝ), (41508501338389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160359219/10000000000 : ℝ)|^8311 ≤ (13089289376593/100000000000000 : ℝ)^6263
        have hw : |(-2160359219/10000000000 : ℝ)|=(2160359219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757720319/5000000000 : ℝ)|^8311 ≤ (1418819039791/3125000000000 : ℝ)^6263
        have hw : |(2757720319/5000000000 : ℝ)|=(2757720319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257754277/500000000 : ℝ)|^8311 ≤ (41508501338389/100000000000000 : ℝ)^6263
        have hw : |(257754277/500000000 : ℝ)|=(257754277/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s2_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343725861/2500000000 : ℝ)*x 0 + (-469577257/2000000000 : ℝ)*x 1 + (5155086959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343725861/2500000000 : ℝ)^8311 ≤ (43873463275441/100000000000000 : ℝ)^6263 := by
    have hnat : (1343725861 : ℕ)^8311*100000000000000^6263 ≤ 43873463275441^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343725861 2500000000 43873463275441 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469577257/2000000000 : ℝ)^8311 ≤ (14618020200197/100000000000000 : ℝ)^6263 := by
    have hnat : (469577257 : ℕ)^8311*100000000000000^6263 ≤ 14618020200197^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469577257 2000000000 14618020200197 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5155086959/10000000000 : ℝ)^8311 ≤ (20754258250159/50000000000000 : ℝ)^6263 := by
    have hnat : (5155086959 : ℕ)^8311*50000000000000^6263 ≤ 20754258250159^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155086959 10000000000 20754258250159 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343725861/2500000000 : ℝ), (-469577257/2000000000 : ℝ), (5155086959/10000000000 : ℝ)] ![(43873463275441/100000000000000 : ℝ), (14618020200197/100000000000000 : ℝ), (20754258250159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343725861/2500000000 : ℝ)|^8311 ≤ (43873463275441/100000000000000 : ℝ)^6263
        have hw : |(1343725861/2500000000 : ℝ)|=(1343725861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469577257/2000000000 : ℝ)|^8311 ≤ (14618020200197/100000000000000 : ℝ)^6263
        have hw : |(-469577257/2000000000 : ℝ)|=(469577257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5155086959/10000000000 : ℝ)|^8311 ≤ (20754258250159/50000000000000 : ℝ)^6263
        have hw : |(5155086959/10000000000 : ℝ)|=(5155086959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s2_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374903373/10000000000 : ℝ)*x 0 + (5155087017/10000000000 : ℝ)*x 1 + (-73371447/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374903373/10000000000 : ℝ)^8311 ≤ (43873462506381/100000000000000 : ℝ)^6263 := by
    have hnat : (5374903373 : ℕ)^8311*100000000000000^6263 ≤ 43873462506381^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374903373 10000000000 43873462506381 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5155087017/10000000000 : ℝ)^8311 ≤ (10377129280011/25000000000000 : ℝ)^6263 := by
    have hnat : (5155087017 : ℕ)^8311*25000000000000^6263 ≤ 10377129280011^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155087017 10000000000 10377129280011 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73371447/312500000 : ℝ)^8311 ≤ (7309010178587/50000000000000 : ℝ)^6263 := by
    have hnat : (73371447 : ℕ)^8311*50000000000000^6263 ≤ 7309010178587^6263*312500000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73371447 312500000 7309010178587 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374903373/10000000000 : ℝ), (5155087017/10000000000 : ℝ), (-73371447/312500000 : ℝ)] ![(43873462506381/100000000000000 : ℝ), (10377129280011/25000000000000 : ℝ), (7309010178587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374903373/10000000000 : ℝ)|^8311 ≤ (43873462506381/100000000000000 : ℝ)^6263
        have hw : |(5374903373/10000000000 : ℝ)|=(5374903373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5155087017/10000000000 : ℝ)|^8311 ≤ (10377129280011/25000000000000 : ℝ)^6263
        have hw : |(5155087017/10000000000 : ℝ)|=(5155087017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73371447/312500000 : ℝ)|^8311 ≤ (7309010178587/50000000000000 : ℝ)^6263
        have hw : |(-73371447/312500000 : ℝ)|=(73371447/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s2_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871362553/2000000000 : ℝ)*x 0 + (2007299423/5000000000 : ℝ)*x 1 + (147754353/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871362553/2000000000 : ℝ)^8311 ≤ (6640597825279/20000000000000 : ℝ)^6263 := by
    have hnat : (871362553 : ℕ)^8311*20000000000000^6263 ≤ 6640597825279^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871362553 2000000000 6640597825279 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007299423/5000000000 : ℝ)^8311 ≤ (5957488315039/20000000000000 : ℝ)^6263 := by
    have hnat : (2007299423 : ℕ)^8311*20000000000000^6263 ≤ 5957488315039^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007299423 5000000000 5957488315039 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147754353/312500000 : ℝ)^8311 ≤ (3700956927599/10000000000000 : ℝ)^6263 := by
    have hnat : (147754353 : ℕ)^8311*10000000000000^6263 ≤ 3700956927599^6263*312500000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147754353 312500000 3700956927599 10000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871362553/2000000000 : ℝ), (2007299423/5000000000 : ℝ), (147754353/312500000 : ℝ)] ![(6640597825279/20000000000000 : ℝ), (5957488315039/20000000000000 : ℝ), (3700956927599/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871362553/2000000000 : ℝ)|^8311 ≤ (6640597825279/20000000000000 : ℝ)^6263
        have hw : |(871362553/2000000000 : ℝ)|=(871362553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007299423/5000000000 : ℝ)|^8311 ≤ (5957488315039/20000000000000 : ℝ)^6263
        have hw : |(2007299423/5000000000 : ℝ)|=(2007299423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147754353/312500000 : ℝ)|^8311 ≤ (3700956927599/10000000000000 : ℝ)^6263
        have hw : |(147754353/312500000 : ℝ)|=(147754353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s2_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-540117089/2500000000 : ℝ)*x 0 + (5157613/10000000 : ℝ)*x 1 + (5512887689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540117089/2500000000 : ℝ)^8311 ≤ (6545083427631/50000000000000 : ℝ)^6263 := by
    have hnat : (540117089 : ℕ)^8311*50000000000000^6263 ≤ 6545083427631^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540117089 2500000000 6545083427631 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5157613/10000000 : ℝ)^8311 ≤ (20767754629477/50000000000000 : ℝ)^6263 := by
    have hnat : (5157613 : ℕ)^8311*50000000000000^6263 ≤ 20767754629477^6263*10000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157613 10000000 20767754629477 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5512887689/10000000000 : ℝ)^8311 ≤ (45374323871347/100000000000000 : ℝ)^6263 := by
    have hnat : (5512887689 : ℕ)^8311*100000000000000^6263 ≤ 45374323871347^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512887689 10000000000 45374323871347 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540117089/2500000000 : ℝ), (5157613/10000000 : ℝ), (5512887689/10000000000 : ℝ)] ![(6545083427631/50000000000000 : ℝ), (20767754629477/50000000000000 : ℝ), (45374323871347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540117089/2500000000 : ℝ)|^8311 ≤ (6545083427631/50000000000000 : ℝ)^6263
        have hw : |(-540117089/2500000000 : ℝ)|=(540117089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5157613/10000000 : ℝ)|^8311 ≤ (20767754629477/50000000000000 : ℝ)^6263
        have hw : |(5157613/10000000 : ℝ)|=(5157613/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5512887689/10000000000 : ℝ)|^8311 ≤ (45374323871347/100000000000000 : ℝ)^6263
        have hw : |(5512887689/10000000000 : ℝ)|=(5512887689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s2_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641809551/5000000000 : ℝ)*x 0 + (-248760609/1250000000 : ℝ)*x 1 + (551288777/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641809551/5000000000 : ℝ)^8311 ≤ (42887442312209/100000000000000 : ℝ)^6263 := by
    have hnat : (2641809551 : ℕ)^8311*100000000000000^6263 ≤ 42887442312209^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641809551 5000000000 42887442312209 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248760609/1250000000 : ℝ)^8311 ≤ (11738232921371/100000000000000 : ℝ)^6263 := by
    have hnat : (248760609 : ℕ)^8311*100000000000000^6263 ≤ 11738232921371^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248760609 1250000000 11738232921371 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551288777/1000000000 : ℝ)^8311 ≤ (45374324756029/100000000000000 : ℝ)^6263 := by
    have hnat : (551288777 : ℕ)^8311*100000000000000^6263 ≤ 45374324756029^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551288777 1000000000 45374324756029 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641809551/5000000000 : ℝ), (-248760609/1250000000 : ℝ), (551288777/1000000000 : ℝ)] ![(42887442312209/100000000000000 : ℝ), (11738232921371/100000000000000 : ℝ), (45374324756029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641809551/5000000000 : ℝ)|^8311 ≤ (42887442312209/100000000000000 : ℝ)^6263
        have hw : |(2641809551/5000000000 : ℝ)|=(2641809551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248760609/1250000000 : ℝ)|^8311 ≤ (11738232921371/100000000000000 : ℝ)^6263
        have hw : |(-248760609/1250000000 : ℝ)|=(248760609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551288777/1000000000 : ℝ)|^8311 ≤ (45374324756029/100000000000000 : ℝ)^6263
        have hw : |(551288777/1000000000 : ℝ)|=(551288777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s2_6 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283619219/10000000000 : ℝ)*x 0 + (2756443863/5000000000 : ℝ)*x 1 + (-1990084771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283619219/10000000000 : ℝ)^8311 ≤ (5360930446557/12500000000000 : ℝ)^6263 := by
    have hnat : (5283619219 : ℕ)^8311*12500000000000^6263 ≤ 5360930446557^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283619219 10000000000 5360930446557 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756443863/5000000000 : ℝ)^8311 ≤ (45374324275461/100000000000000 : ℝ)^6263 := by
    have hnat : (2756443863 : ℕ)^8311*100000000000000^6263 ≤ 45374324275461^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756443863 5000000000 45374324275461 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1990084771/10000000000 : ℝ)^8311 ≤ (733639508177/6250000000000 : ℝ)^6263 := by
    have hnat : (1990084771 : ℕ)^8311*6250000000000^6263 ≤ 733639508177^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990084771 10000000000 733639508177 6250000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283619219/10000000000 : ℝ), (2756443863/5000000000 : ℝ), (-1990084771/10000000000 : ℝ)] ![(5360930446557/12500000000000 : ℝ), (45374324275461/100000000000000 : ℝ), (733639508177/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283619219/10000000000 : ℝ)|^8311 ≤ (5360930446557/12500000000000 : ℝ)^6263
        have hw : |(5283619219/10000000000 : ℝ)|=(5283619219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756443863/5000000000 : ℝ)|^8311 ≤ (45374324275461/100000000000000 : ℝ)^6263
        have hw : |(2756443863/5000000000 : ℝ)|=(2756443863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1990084771/10000000000 : ℝ)|^8311 ≤ (733639508177/6250000000000 : ℝ)^6263
        have hw : |(-1990084771/10000000000 : ℝ)|=(1990084771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s2_7 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435703031/1000000000 : ℝ)*x 0 + (4723136097/10000000000 : ℝ)*x 1 + (3925441/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435703031/1000000000 : ℝ)^8311 ≤ (8301297293159/25000000000000 : ℝ)^6263 := by
    have hnat : (435703031 : ℕ)^8311*25000000000000^6263 ≤ 8301297293159^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435703031 1000000000 8301297293159 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4723136097/10000000000 : ℝ)^8311 ≤ (36957609502007/100000000000000 : ℝ)^6263 := by
    have hnat : (4723136097 : ℕ)^8311*100000000000000^6263 ≤ 36957609502007^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4723136097 10000000000 36957609502007 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3925441/9765625 : ℝ)^8311 ≤ (5967440261437/20000000000000 : ℝ)^6263 := by
    have hnat : (3925441 : ℕ)^8311*20000000000000^6263 ≤ 5967440261437^6263*9765625^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3925441 9765625 5967440261437 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435703031/1000000000 : ℝ), (4723136097/10000000000 : ℝ), (3925441/9765625 : ℝ)] ![(8301297293159/25000000000000 : ℝ), (36957609502007/100000000000000 : ℝ), (5967440261437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435703031/1000000000 : ℝ)|^8311 ≤ (8301297293159/25000000000000 : ℝ)^6263
        have hw : |(435703031/1000000000 : ℝ)|=(435703031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4723136097/10000000000 : ℝ)|^8311 ≤ (36957609502007/100000000000000 : ℝ)^6263
        have hw : |(4723136097/10000000000 : ℝ)|=(4723136097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3925441/9765625 : ℝ)|^8311 ≤ (5967440261437/20000000000000 : ℝ)^6263
        have hw : |(3925441/9765625 : ℝ)|=(3925441/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20547/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (56/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (663/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20547/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2757/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20547/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2757/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20547/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2757/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20547/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2757/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20547/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2757/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20547/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2757/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2757/50000 : ℝ) ^ (4155/1024 : ℝ) ≤ (782265003573757/100000000000000000000 : ℝ) := by
    have hpowers : (2757/50000 : ℝ)^4155 ≤ (782265003573757/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2757 : ℕ)^4155*100000000000000000000^1024 ≤ 782265003573757^1024*50000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2757 50000 782265003573757 100000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2757/50000 : ℝ)) (X := (782265003573757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20547/100000 : ℝ) ^ (4155/1024 : ℝ) ≤ (162703232228893877/100000000000000000000 : ℝ) := by
    have hpowers : (20547/100000 : ℝ)^4155 ≤ (162703232228893877/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20547 : ℕ)^4155*100000000000000000000^1024 ≤ 162703232228893877^1024*100000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20547 100000 162703232228893877 100000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20547/100000 : ℝ)) (X := (162703232228893877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000782265003573757/50000000000000000000 : ℝ) ≤ (10000038557624153/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50000782265003573757/50000000000000000000 : ℝ)^1024 ≤ (10000038557624153/10000000000000000 : ℝ)^4155 := by
      have hnat : (50000782265003573757 : ℕ)^1024*10000000000000000^4155 ≤ 10000038557624153^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000782265003573757 50000000000000000000 10000038557624153 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000038557624153/10000000000000000 : ℝ)) (X := (50000782265003573757/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50081742748616233817/50000000000000000000 : ℝ) ≤ (5002013310808367/5000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50081742748616233817/50000000000000000000 : ℝ)^1024 ≤ (5002013310808367/5000000000000000 : ℝ)^4155 := by
      have hnat : (50081742748616233817 : ℕ)^1024*5000000000000000^4155 ≤ 5002013310808367^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50081742748616233817 50000000000000000000 5002013310808367 5000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002013310808367/5000000000000000 : ℝ)) (X := (50081742748616233817/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50162703232228893877/50000000000000000000 : ℝ) ≤ (2001602937121863/2000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50162703232228893877/50000000000000000000 : ℝ)^1024 ≤ (2001602937121863/2000000000000000 : ℝ)^4155 := by
      have hnat : (50162703232228893877 : ℕ)^1024*2000000000000000^4155 ≤ 2001602937121863^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50162703232228893877 50000000000000000000 2001602937121863 2000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001602937121863/2000000000000000 : ℝ)) (X := (50162703232228893877/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(782265003573757/100000000000000000000 : ℝ) ≤ ((50095533089017902927/50110000000000000000 : ℝ)+2*(3988063992581/1503300000000000 : ℝ)*(2757/50000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (50095533089017902927/50110000000000000000 : ℝ)+2*(3988063992581/1503300000000000 : ℝ)*(2757/50000 : ℝ)=(10000038557624153/10000000000000000 : ℝ) by norm_num, show 1+2*(782265003573757/100000000000000000000 : ℝ)=(50000782265003573757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(162703232228893877/100000000000000000000 : ℝ)+(782265003573757/100000000000000000000 : ℝ) ≤ ((50095533089017902927/50110000000000000000 : ℝ)+(3988063992581/1503300000000000 : ℝ)*((20547/100000 : ℝ)+(2757/50000 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (50095533089017902927/50110000000000000000 : ℝ)+(3988063992581/1503300000000000 : ℝ)*((20547/100000 : ℝ)+(2757/50000 : ℝ))=(5002013310808367/5000000000000000 : ℝ) by norm_num, show 1+(162703232228893877/100000000000000000000 : ℝ)+(782265003573757/100000000000000000000 : ℝ)=(50081742748616233817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(162703232228893877/100000000000000000000 : ℝ) ≤ ((50095533089017902927/50110000000000000000 : ℝ)+2*(3988063992581/1503300000000000 : ℝ)*(20547/100000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (50095533089017902927/50110000000000000000 : ℝ)+2*(3988063992581/1503300000000000 : ℝ)*(20547/100000 : ℝ)=(2001602937121863/2000000000000000 : ℝ) by norm_num, show 1+2*(162703232228893877/100000000000000000000 : ℝ)=(50162703232228893877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50095533089017902927/50110000000000000000 : ℝ)*(X 1 0+X 2 0)+(3988063992581/1503300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (2757/50000 : ℝ)) (hi := (20547/100000 : ℝ)) (c := (50095533089017902927/50110000000000000000 : ℝ)) (alpha := (3988063992581/1503300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50095533089017902927/50110000000000000000 : ℝ)*(X 0 1+X 2 1)+(3988063992581/1503300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (2757/50000 : ℝ)) (hi := (20547/100000 : ℝ)) (c := (50095533089017902927/50110000000000000000 : ℝ)) (alpha := (3988063992581/1503300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50095533089017902927/50110000000000000000 : ℝ)*(X 0 2+X 1 2)+(3988063992581/1503300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (2757/50000 : ℝ)) (hi := (20547/100000 : ℝ)) (c := (50095533089017902927/50110000000000000000 : ℝ)) (alpha := (3988063992581/1503300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2160359219/10000000000 : ℝ)*X 0 0+(2757720319/5000000000 : ℝ)*X 0 1+(257754277/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343725861/2500000000 : ℝ)*X 1 0+(-469577257/2000000000 : ℝ)*X 1 1+(5155086959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374903373/10000000000 : ℝ)*X 2 0+(5155087017/10000000000 : ℝ)*X 2 1+(-73371447/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871362553/2000000000 : ℝ)*X 0 0+(2007299423/5000000000 : ℝ)*X 0 1+(147754353/312500000 : ℝ)*X 0 2+(871362553/2000000000 : ℝ)*X 1 0+(2007299423/5000000000 : ℝ)*X 1 1+(147754353/312500000 : ℝ)*X 1 2+(871362553/2000000000 : ℝ)*X 2 0+(2007299423/5000000000 : ℝ)*X 2 1+(147754353/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-540117089/2500000000 : ℝ)*X 0 0+(5157613/10000000 : ℝ)*X 0 1+(5512887689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641809551/5000000000 : ℝ)*X 1 0+(-248760609/1250000000 : ℝ)*X 1 1+(551288777/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5283619219/10000000000 : ℝ)*X 2 0+(2756443863/5000000000 : ℝ)*X 2 1+(-1990084771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435703031/1000000000 : ℝ)*X 0 0+(4723136097/10000000000 : ℝ)*X 0 1+(3925441/9765625 : ℝ)*X 0 2+(435703031/1000000000 : ℝ)*X 1 0+(4723136097/10000000000 : ℝ)*X 1 1+(3925441/9765625 : ℝ)*X 1 2+(435703031/1000000000 : ℝ)*X 2 0+(4723136097/10000000000 : ℝ)*X 2 1+(3925441/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84693571688785660361311161/9787109375000000000000000000000 : ℝ) := by norm_num
    linear_combination (30473283/3125000000000 : ℝ)*(base19) + (678558131/100000000000000 : ℝ)*(base23) + (122071741/50000000000000 : ℝ)*(upper3) + (139709563/100000000000000 : ℝ)*(upper4) + (12698841/50000000000000 : ℝ)*(upper5) + (65258629613223/3125000000000 : ℝ)*(major0) + (65258629613223/3125000000000 : ℝ)*(major1) + (65258629613223/3125000000000 : ℝ)*(major2) + (1387530097360271/50000000000000 : ℝ)*(sp0) + (21680285984227/781250000000 : ℝ)*(sp1) + (1387538451283991/50000000000000 : ℝ)*(sp2) + (1401467276369639/100000000000000 : ℝ)*(sp3) + (1738640557/10000000000000 : ℝ)*(sp4) + (178732443/2500000000000 : ℝ)*(sp7) + (1401474425667359/100000000000000 : ℝ)*(f.failure) + (86721174410191/3125000000000 : ℝ)*(f.sum) + (99752500288263/25055000000000000000000000000 : ℝ)*base66 + (385056223348891221/156593750000000000000000000000000 : ℝ)*base67 + (1119916480396233779/156593750000000000000000000000000 : ℝ)*base70 + (1467582614537327529/156593750000000000000000000000000 : ℝ)*base72 + (21826110559301/12527500000000000000000000000 : ℝ)*base73 + (451116847377703721/156593750000000000000000000000000 : ℝ)*base75 + (1455125021432390029/156593750000000000000000000000000 : ℝ)*base78 + (627086524241046279/156593750000000000000000000000000 : ℝ)*base80 + (1164834252197/391484375000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7983029/2000000000000000000000 : ℝ)*base89 + (7983029/2000000000000000000000 : ℝ)*base91 + (7983029/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50122271425281679113459/12527500000000000000000000000 : ℝ) := by norm_num
    linear_combination (817977249/100000000000000 : ℝ)*(base19) + (973260689/100000000000000 : ℝ)*(base23) + (121513947/100000000000000 : ℝ)*(upper3) + (7207519/25000000000000 : ℝ)*(lower4) + (33083301/50000000000000 : ℝ)*(upper5) + (529527319569441/25000000000000 : ℝ)*(major0) + (529527319569441/25000000000000 : ℝ)*(major1) + (529527319569441/25000000000000 : ℝ)*(major2) + (234349033/3125000000000 : ℝ)*(sp1) + (4860603121/50000000000000 : ℝ)*(sp2) + (703680630514741/25000000000000 : ℝ)*(sp4) + (140735710245633/5000000000000 : ℝ)*(sp5) + (87959744612251/3125000000000 : ℝ)*(sp6) + (710747950565287/50000000000000 : ℝ)*(sp7) + (710747950565287/50000000000000 : ℝ)*(f.failure) + (703680630514741/25000000000000 : ℝ)*(f.sum) + (4019006771189/782968750000000000000000000 : ℝ)*base65 + (215755658500146193/1252750000000000000000000000000000 : ℝ)*base68 + (93846804231353807/1252750000000000000000000000000000 : ℝ)*base69 + (4317505256226646193/1252750000000000000000000000000000 : ℝ)*base72 + (83770610106869/12527500000000000000000000000 : ℝ)*base73 + (9410034221215646193/1252750000000000000000000000000000 : ℝ)*base76 + (1106079074275853807/1252750000000000000000000000000000 : ℝ)*base77 + (324395883798353807/1252750000000000000000000000000000 : ℝ)*base79 + (5611792391487/6263750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (1939597/1000000000000000000000 : ℝ)*base89 + (1939597/1000000000000000000000 : ℝ)*base91 + (1939597/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1118_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20547/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (56/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (663/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1118_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1118_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (56/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (663/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1118_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1118_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1118_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (56/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (663/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1118_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
