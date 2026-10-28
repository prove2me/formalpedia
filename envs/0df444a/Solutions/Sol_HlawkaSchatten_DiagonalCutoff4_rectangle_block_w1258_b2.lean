-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:58.709978+00:00
-- url     : https://prove2.me/submissions/616f6b6b-7c85-490a-a30b-e6280261edb8

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
theorem support_rectangle_w1258_s6_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056300373/5000000000 : ℝ)*x 0 + (2695536977/5000000000 : ℝ)*x 1 + (1316815253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056300373/5000000000 : ℝ)^8451 ≤ (12848730973623/100000000000000 : ℝ)^6403 := by
    have hnat : (1056300373 : ℕ)^8451*100000000000000^6403 ≤ 12848730973623^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056300373 5000000000 12848730973623 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695536977/5000000000 : ℝ)^8451 ≤ (22121858815323/50000000000000 : ℝ)^6403 := by
    have hnat : (2695536977 : ℕ)^8451*50000000000000^6403 ≤ 22121858815323^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695536977 5000000000 22121858815323 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316815253/2500000000 : ℝ)^8451 ≤ (42907551379219/100000000000000 : ℝ)^6403 := by
    have hnat : (1316815253 : ℕ)^8451*100000000000000^6403 ≤ 42907551379219^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316815253 2500000000 42907551379219 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056300373/5000000000 : ℝ), (2695536977/5000000000 : ℝ), (1316815253/2500000000 : ℝ)] ![(12848730973623/100000000000000 : ℝ), (22121858815323/50000000000000 : ℝ), (42907551379219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056300373/5000000000 : ℝ)|^8451 ≤ (12848730973623/100000000000000 : ℝ)^6403
        have hw : |(-1056300373/5000000000 : ℝ)|=(1056300373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695536977/5000000000 : ℝ)|^8451 ≤ (22121858815323/50000000000000 : ℝ)^6403
        have hw : |(2695536977/5000000000 : ℝ)|=(2695536977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316815253/2500000000 : ℝ)|^8451 ≤ (42907551379219/100000000000000 : ℝ)^6403
        have hw : |(1316815253/2500000000 : ℝ)|=(1316815253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s6_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344267747/10000000000 : ℝ)*x 0 + (-1087687901/5000000000 : ℝ)*x 1 + (5267261009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344267747/10000000000 : ℝ)^8451 ≤ (437374271717/1000000000000 : ℝ)^6403 := by
    have hnat : (5344267747 : ℕ)^8451*1000000000000^6403 ≤ 437374271717^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344267747 10000000000 437374271717 1000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087687901/5000000000 : ℝ)^8451 ≤ (2671004293503/20000000000000 : ℝ)^6403 := by
    have hnat : (1087687901 : ℕ)^8451*20000000000000^6403 ≤ 2671004293503^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087687901 5000000000 2671004293503 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267261009/10000000000 : ℝ)^8451 ≤ (10726887836741/25000000000000 : ℝ)^6403 := by
    have hnat : (5267261009 : ℕ)^8451*25000000000000^6403 ≤ 10726887836741^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267261009 10000000000 10726887836741 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344267747/10000000000 : ℝ), (-1087687901/5000000000 : ℝ), (5267261009/10000000000 : ℝ)] ![(437374271717/1000000000000 : ℝ), (2671004293503/20000000000000 : ℝ), (10726887836741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344267747/10000000000 : ℝ)|^8451 ≤ (437374271717/1000000000000 : ℝ)^6403
        have hw : |(5344267747/10000000000 : ℝ)|=(5344267747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087687901/5000000000 : ℝ)|^8451 ≤ (2671004293503/20000000000000 : ℝ)^6403
        have hw : |(-1087687901/5000000000 : ℝ)|=(1087687901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267261009/10000000000 : ℝ)|^8451 ≤ (10726887836741/25000000000000 : ℝ)^6403
        have hw : |(5267261009/10000000000 : ℝ)|=(5267261009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s6_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668033469/1250000000 : ℝ)*x 0 + (329203813/625000000 : ℝ)*x 1 + (-543843949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668033469/1250000000 : ℝ)^8451 ≤ (10934356806427/25000000000000 : ℝ)^6403 := by
    have hnat : (668033469 : ℕ)^8451*25000000000000^6403 ≤ 10934356806427^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668033469 1250000000 10934356806427 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329203813/625000000 : ℝ)^8451 ≤ (10726887834053/25000000000000 : ℝ)^6403 := by
    have hnat : (329203813 : ℕ)^8451*25000000000000^6403 ≤ 10726887834053^6403*625000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329203813 625000000 10726887834053 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543843949/2500000000 : ℝ)^8451 ≤ (13355021418899/100000000000000 : ℝ)^6403 := by
    have hnat : (543843949 : ℕ)^8451*100000000000000^6403 ≤ 13355021418899^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543843949 2500000000 13355021418899 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668033469/1250000000 : ℝ), (329203813/625000000 : ℝ), (-543843949/2500000000 : ℝ)] ![(10934356806427/25000000000000 : ℝ), (10726887834053/25000000000000 : ℝ), (13355021418899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668033469/1250000000 : ℝ)|^8451 ≤ (10934356806427/25000000000000 : ℝ)^6403
        have hw : |(668033469/1250000000 : ℝ)|=(668033469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329203813/625000000 : ℝ)|^8451 ≤ (10726887834053/25000000000000 : ℝ)^6403
        have hw : |(329203813/625000000 : ℝ)|=(329203813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-543843949/2500000000 : ℝ)|^8451 ≤ (13355021418899/100000000000000 : ℝ)^6403
        have hw : |(-543843949/2500000000 : ℝ)|=(543843949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s6_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087143717/2500000000 : ℝ)*x 0 + (211218627/500000000 : ℝ)*x 1 + (447631201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087143717/2500000000 : ℝ)^8451 ≤ (33317484061147/100000000000000 : ℝ)^6403 := by
    have hnat : (1087143717 : ℕ)^8451*100000000000000^6403 ≤ 33317484061147^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087143717 2500000000 33317484061147 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211218627/500000000 : ℝ)^8451 ≤ (16033643832973/50000000000000 : ℝ)^6403 := by
    have hnat : (211218627 : ℕ)^8451*50000000000000^6403 ≤ 16033643832973^6403*500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211218627 500000000 16033643832973 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447631201/1000000000 : ℝ)^8451 ≤ (17307614131493/50000000000000 : ℝ)^6403 := by
    have hnat : (447631201 : ℕ)^8451*50000000000000^6403 ≤ 17307614131493^6403*1000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447631201 1000000000 17307614131493 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087143717/2500000000 : ℝ), (211218627/500000000 : ℝ), (447631201/1000000000 : ℝ)] ![(33317484061147/100000000000000 : ℝ), (16033643832973/50000000000000 : ℝ), (17307614131493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087143717/2500000000 : ℝ)|^8451 ≤ (33317484061147/100000000000000 : ℝ)^6403
        have hw : |(1087143717/2500000000 : ℝ)|=(1087143717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211218627/500000000 : ℝ)|^8451 ≤ (16033643832973/50000000000000 : ℝ)^6403
        have hw : |(211218627/500000000 : ℝ)|=(211218627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447631201/1000000000 : ℝ)|^8451 ≤ (17307614131493/50000000000000 : ℝ)^6403
        have hw : |(447631201/1000000000 : ℝ)|=(447631201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s6_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528151351/2500000000 : ℝ)*x 0 + (5267574287/10000000000 : ℝ)*x 1 + (5390759541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528151351/2500000000 : ℝ)^8451 ≤ (642438418231/5000000000000 : ℝ)^6403 := by
    have hnat : (528151351 : ℕ)^8451*5000000000000^6403 ≤ 642438418231^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528151351 2500000000 642438418231 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267574287/10000000000 : ℝ)^8451 ≤ (42910919621791/100000000000000 : ℝ)^6403 := by
    have hnat : (5267574287 : ℕ)^8451*100000000000000^6403 ≤ 42910919621791^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267574287 10000000000 42910919621791 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390759541/10000000000 : ℝ)^8451 ≤ (11060078000351/25000000000000 : ℝ)^6403 := by
    have hnat : (5390759541 : ℕ)^8451*25000000000000^6403 ≤ 11060078000351^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390759541 10000000000 11060078000351 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528151351/2500000000 : ℝ), (5267574287/10000000000 : ℝ), (5390759541/10000000000 : ℝ)] ![(642438418231/5000000000000 : ℝ), (42910919621791/100000000000000 : ℝ), (11060078000351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528151351/2500000000 : ℝ)|^8451 ≤ (642438418231/5000000000000 : ℝ)^6403
        have hw : |(-528151351/2500000000 : ℝ)|=(528151351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267574287/10000000000 : ℝ)|^8451 ≤ (42910919621791/100000000000000 : ℝ)^6403
        have hw : |(5267574287/10000000000 : ℝ)|=(5267574287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390759541/10000000000 : ℝ)|^8451 ≤ (11060078000351/25000000000000 : ℝ)^6403
        have hw : |(5390759541/10000000000 : ℝ)|=(5390759541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s6_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312642349/10000000000 : ℝ)*x 0 + (-128242329/625000000 : ℝ)*x 1 + (5390759543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312642349/10000000000 : ℝ)^8451 ≤ (5424518098687/12500000000000 : ℝ)^6403 := by
    have hnat : (5312642349 : ℕ)^8451*12500000000000^6403 ≤ 5424518098687^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312642349 10000000000 5424518098687 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128242329/625000000 : ℝ)^8451 ≤ (12363543169221/100000000000000 : ℝ)^6403 := by
    have hnat : (128242329 : ℕ)^8451*100000000000000^6403 ≤ 12363543169221^6403*625000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128242329 625000000 12363543169221 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390759543/10000000000 : ℝ)^8451 ≤ (11060078005767/25000000000000 : ℝ)^6403 := by
    have hnat : (5390759543 : ℕ)^8451*25000000000000^6403 ≤ 11060078005767^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390759543 10000000000 11060078005767 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312642349/10000000000 : ℝ), (-128242329/625000000 : ℝ), (5390759543/10000000000 : ℝ)] ![(5424518098687/12500000000000 : ℝ), (12363543169221/100000000000000 : ℝ), (11060078005767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312642349/10000000000 : ℝ)|^8451 ≤ (5424518098687/12500000000000 : ℝ)^6403
        have hw : |(5312642349/10000000000 : ℝ)|=(5312642349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128242329/625000000 : ℝ)|^8451 ≤ (12363543169221/100000000000000 : ℝ)^6403
        have hw : |(-128242329/625000000 : ℝ)|=(128242329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390759543/10000000000 : ℝ)|^8451 ≤ (11060078005767/25000000000000 : ℝ)^6403
        have hw : |(5390759543/10000000000 : ℝ)|=(5390759543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s6_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328160587/2500000000 : ℝ)*x 0 + (5390759543/10000000000 : ℝ)*x 1 + (-410375453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328160587/2500000000 : ℝ)^8451 ≤ (8679228955743/20000000000000 : ℝ)^6403 := by
    have hnat : (1328160587 : ℕ)^8451*20000000000000^6403 ≤ 8679228955743^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328160587 2500000000 8679228955743 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390759543/10000000000 : ℝ)^8451 ≤ (11060078005767/25000000000000 : ℝ)^6403 := by
    have hnat : (5390759543 : ℕ)^8451*25000000000000^6403 ≤ 11060078005767^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390759543 10000000000 11060078005767 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410375453/2000000000 : ℝ)^8451 ≤ (6181771588587/50000000000000 : ℝ)^6403 := by
    have hnat : (410375453 : ℕ)^8451*50000000000000^6403 ≤ 6181771588587^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410375453 2000000000 6181771588587 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328160587/2500000000 : ℝ), (5390759543/10000000000 : ℝ), (-410375453/2000000000 : ℝ)] ![(8679228955743/20000000000000 : ℝ), (11060078005767/25000000000000 : ℝ), (6181771588587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328160587/2500000000 : ℝ)|^8451 ≤ (8679228955743/20000000000000 : ℝ)^6403
        have hw : |(1328160587/2500000000 : ℝ)|=(1328160587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390759543/10000000000 : ℝ)|^8451 ≤ (11060078005767/25000000000000 : ℝ)^6403
        have hw : |(5390759543/10000000000 : ℝ)|=(5390759543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410375453/2000000000 : ℝ)|^8451 ≤ (6181771588587/50000000000000 : ℝ)^6403
        have hw : |(-410375453/2000000000 : ℝ)|=(410375453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s6_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543573043/1250000000 : ℝ)*x 0 + (4475674547/10000000000 : ℝ)*x 1 + (4225012329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543573043/1250000000 : ℝ)^8451 ≤ (16658789942657/50000000000000 : ℝ)^6403 := by
    have hnat : (543573043 : ℕ)^8451*50000000000000^6403 ≤ 16658789942657^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543573043 1250000000 16658789942657 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475674547/10000000000 : ℝ)^8451 ≤ (34608722225813/100000000000000 : ℝ)^6403 := by
    have hnat : (4475674547 : ℕ)^8451*100000000000000^6403 ≤ 34608722225813^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475674547 10000000000 34608722225813 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225012329/10000000000 : ℝ)^8451 ≤ (32073697870733/100000000000000 : ℝ)^6403 := by
    have hnat : (4225012329 : ℕ)^8451*100000000000000^6403 ≤ 32073697870733^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225012329 10000000000 32073697870733 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543573043/1250000000 : ℝ), (4475674547/10000000000 : ℝ), (4225012329/10000000000 : ℝ)] ![(16658789942657/50000000000000 : ℝ), (34608722225813/100000000000000 : ℝ), (32073697870733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543573043/1250000000 : ℝ)|^8451 ≤ (16658789942657/50000000000000 : ℝ)^6403
        have hw : |(543573043/1250000000 : ℝ)|=(543573043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475674547/10000000000 : ℝ)|^8451 ≤ (34608722225813/100000000000000 : ℝ)^6403
        have hw : |(4475674547/10000000000 : ℝ)|=(4475674547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225012329/10000000000 : ℝ)|^8451 ≤ (32073697870733/100000000000000 : ℝ)^6403
        have hw : |(4225012329/10000000000 : ℝ)|=(4225012329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5747/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14137/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14137/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14137/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14137/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14137/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14137/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (459/4000 : ℝ) ^ (4225/1024 : ℝ) ≤ (3299906707681661/25000000000000000000 : ℝ) := by
    have hpowers : (459/4000 : ℝ)^4225 ≤ (3299906707681661/25000000000000000000 : ℝ)^1024 := by
      have hnat : (459 : ℕ)^4225*25000000000000000000^1024 ≤ 3299906707681661^1024*4000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 4000 3299906707681661 25000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/4000 : ℝ)) (X := (3299906707681661/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14137/100000 : ℝ) ^ (4225/1024 : ℝ) ≤ (31217200948945597/100000000000000000000 : ℝ) := by
    have hpowers : (14137/100000 : ℝ)^4225 ≤ (31217200948945597/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14137 : ℕ)^4225*100000000000000000000^1024 ≤ 31217200948945597^1024*100000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14137 100000 31217200948945597 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14137/100000 : ℝ)) (X := (31217200948945597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503299906707681661/12500000000000000000 : ℝ) ≤ (1250079970806969/1250000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (12503299906707681661/12500000000000000000 : ℝ)^1024 ≤ (1250079970806969/1250000000000000 : ℝ)^4225 := by
      have hnat : (12503299906707681661 : ℕ)^1024*1250000000000000^4225 ≤ 1250079970806969^4225*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503299906707681661 12500000000000000000 1250079970806969 1250000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250079970806969/1250000000000000 : ℝ)) (X := (12503299906707681661/12500000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044416827779672241/100000000000000000000 : ℝ) ≤ (10001076335639603/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (100044416827779672241/100000000000000000000 : ℝ)^1024 ≤ (10001076335639603/10000000000000000 : ℝ)^4225 := by
      have hnat : (100044416827779672241 : ℕ)^1024*10000000000000000^4225 ≤ 10001076335639603^4225*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044416827779672241 100000000000000000000 10001076335639603 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001076335639603/10000000000000000 : ℝ)) (X := (100044416827779672241/100000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031217200948945597/50000000000000000000 : ℝ) ≤ (5000756452411727/5000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50031217200948945597/50000000000000000000 : ℝ)^1024 ≤ (5000756452411727/5000000000000000 : ℝ)^4225 := by
      have hnat : (50031217200948945597 : ℕ)^1024*5000000000000000^4225 ≤ 5000756452411727^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031217200948945597 50000000000000000000 5000756452411727 5000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000756452411727/5000000000000000 : ℝ)) (X := (50031217200948945597/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3299906707681661/25000000000000000000 : ℝ) ≤ ((13305841897767915687/13310000000000000000 : ℝ)+2*(436569183851/266200000000000 : ℝ)*(459/4000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (13305841897767915687/13310000000000000000 : ℝ)+2*(436569183851/266200000000000 : ℝ)*(459/4000 : ℝ)=(1250079970806969/1250000000000000 : ℝ) by norm_num, show 1+2*(3299906707681661/25000000000000000000 : ℝ)=(12503299906707681661/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31217200948945597/100000000000000000000 : ℝ)+(3299906707681661/25000000000000000000 : ℝ) ≤ ((13305841897767915687/13310000000000000000 : ℝ)+(436569183851/266200000000000 : ℝ)*((14137/100000 : ℝ)+(459/4000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (13305841897767915687/13310000000000000000 : ℝ)+(436569183851/266200000000000 : ℝ)*((14137/100000 : ℝ)+(459/4000 : ℝ))=(10001076335639603/10000000000000000 : ℝ) by norm_num, show 1+(31217200948945597/100000000000000000000 : ℝ)+(3299906707681661/25000000000000000000 : ℝ)=(100044416827779672241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31217200948945597/100000000000000000000 : ℝ) ≤ ((13305841897767915687/13310000000000000000 : ℝ)+2*(436569183851/266200000000000 : ℝ)*(14137/100000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (13305841897767915687/13310000000000000000 : ℝ)+2*(436569183851/266200000000000 : ℝ)*(14137/100000 : ℝ)=(5000756452411727/5000000000000000 : ℝ) by norm_num, show 1+2*(31217200948945597/100000000000000000000 : ℝ)=(50031217200948945597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13305841897767915687/13310000000000000000 : ℝ)*(X 1 0+X 2 0)+(436569183851/266200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14137/100000 : ℝ)) (c := (13305841897767915687/13310000000000000000 : ℝ)) (alpha := (436569183851/266200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13305841897767915687/13310000000000000000 : ℝ)*(X 0 1+X 2 1)+(436569183851/266200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14137/100000 : ℝ)) (c := (13305841897767915687/13310000000000000000 : ℝ)) (alpha := (436569183851/266200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13305841897767915687/13310000000000000000 : ℝ)*(X 0 2+X 1 2)+(436569183851/266200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14137/100000 : ℝ)) (c := (13305841897767915687/13310000000000000000 : ℝ)) (alpha := (436569183851/266200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056300373/5000000000 : ℝ)*X 0 0+(2695536977/5000000000 : ℝ)*X 0 1+(1316815253/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344267747/10000000000 : ℝ)*X 1 0+(-1087687901/5000000000 : ℝ)*X 1 1+(5267261009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668033469/1250000000 : ℝ)*X 2 0+(329203813/625000000 : ℝ)*X 2 1+(-543843949/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087143717/2500000000 : ℝ)*X 0 0+(211218627/500000000 : ℝ)*X 0 1+(447631201/1000000000 : ℝ)*X 0 2+(1087143717/2500000000 : ℝ)*X 1 0+(211218627/500000000 : ℝ)*X 1 1+(447631201/1000000000 : ℝ)*X 1 2+(1087143717/2500000000 : ℝ)*X 2 0+(211218627/500000000 : ℝ)*X 2 1+(447631201/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528151351/2500000000 : ℝ)*X 0 0+(5267574287/10000000000 : ℝ)*X 0 1+(5390759541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312642349/10000000000 : ℝ)*X 1 0+(-128242329/625000000 : ℝ)*X 1 1+(5390759543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328160587/2500000000 : ℝ)*X 2 0+(5390759543/10000000000 : ℝ)*X 2 1+(-410375453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543573043/1250000000 : ℝ)*X 0 0+(4475674547/10000000000 : ℝ)*X 0 1+(4225012329/10000000000 : ℝ)*X 0 2+(543573043/1250000000 : ℝ)*X 1 0+(4475674547/10000000000 : ℝ)*X 1 1+(4225012329/10000000000 : ℝ)*X 1 2+(543573043/1250000000 : ℝ)*X 2 0+(4475674547/10000000000 : ℝ)*X 2 1+(4225012329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99136338333697343756139/20796875000000000000000000000 : ℝ) := by norm_num
    linear_combination (929538859/100000000000000 : ℝ)*(base19) + (870788269/100000000000000 : ℝ)*(base23) + (7087253/20000000000000 : ℝ)*(lower2) + (29609131/25000000000000 : ℝ)*(upper3) + (4030389/5000000000000 : ℝ)*(upper5) + (1505748228829/25000000000 : ℝ)*(major0) + (1505748228829/25000000000 : ℝ)*(major1) + (1505748228829/25000000000 : ℝ)*(major2) + (4038363270356403/50000000000000 : ℝ)*(sp0) + (8076751446860763/100000000000000 : ℝ)*(sp1) + (4038375752805677/50000000000000 : ℝ)*(sp2) + (992304925677583/25000000000000 : ℝ)*(sp3) + (25835686817/100000000000000 : ℝ)*(sp4) + (13592625823/100000000000000 : ℝ)*(sp7) + (992308323834039/25000000000000 : ℝ)*(f.failure) + (4038376188199811/50000000000000 : ℝ)*(f.sum) + (388490216071/83187500000000000000000000 : ℝ)*base65 + (2201054411055477/332750000000000000000000000000 : ℝ)*base68 + (1058461472381523/332750000000000000000000000000 : ℝ)*base69 + (3537877390335773/332750000000000000000000000000 : ℝ)*base71 + (1167643867303/266200000000000000000000000 : ℝ)*base73 + (7168317414247023/332750000000000000000000000000 : ℝ)*base75 + (4826769459396523/332750000000000000000000000000 : ℝ)*base77 + (6153847069944773/332750000000000000000000000000 : ℝ)*base79 + (10643904287307/1331000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (2418947/2500000000000000000000 : ℝ)*base89 + (2418947/2500000000000000000000 : ℝ)*base91 + (2418947/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5264121986543967029363983731/665500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (706116011/50000000000000 : ℝ)*(base19) + (1534871069/100000000000000 : ℝ)*(base23) + (31942677/20000000000000 : ℝ)*(upper3) + (56668567/100000000000000 : ℝ)*(lower4) + (161771309/100000000000000 : ℝ)*(upper5) + (6053642744838471/100000000000000 : ℝ)*(major0) + (6053642744838471/100000000000000 : ℝ)*(major1) + (6053642744838471/100000000000000 : ℝ)*(major2) + (2494168697/6250000000000 : ℝ)*(sp1) + (21423201803/50000000000000 : ℝ)*(sp2) + (8117853281007307/100000000000000 : ℝ)*(sp4) + (2029452990519033/25000000000000 : ℝ)*(sp5) + (8117808899732633/100000000000000 : ℝ)*(sp6) + (1994715972501053/50000000000000 : ℝ)*(sp7) + (1994715972501053/50000000000000 : ℝ)*(f.failure) + (8117853281007307/100000000000000 : ℝ)*(f.sum) + (65598306218661/13310000000000000000000000000 : ℝ)*base65 + (21044420638367955423/1331000000000000000000000000000000 : ℝ)*base68 + (7811245785337955423/1331000000000000000000000000000000 : ℝ)*base70 + (2692124939597044577/1331000000000000000000000000000000 : ℝ)*base71 + (85817209359479/13310000000000000000000000000 : ℝ)*base74 + (19349771165895044577/1331000000000000000000000000000000 : ℝ)*base75 + (16719833092506955423/1331000000000000000000000000000000 : ℝ)*base78 + (11188826773965955423/1331000000000000000000000000000000 : ℝ)*base80 + (18438123659391/13310000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (23202431/5000000000000000000000 : ℝ)*base90 + (23202431/5000000000000000000000 : ℝ)*base92 + (23202431/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1258_s7_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-422523299/2000000000 : ℝ)*x 0 + (5390892731/10000000000 : ℝ)*x 1 + (5267431827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422523299/2000000000 : ℝ)^8451 ≤ (6424428697557/50000000000000 : ℝ)^6403 := by
    have hnat : (422523299 : ℕ)^8451*50000000000000^6403 ≤ 6424428697557^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422523299 2000000000 6424428697557 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390892731/10000000000 : ℝ)^8451 ≤ (44241754668597/100000000000000 : ℝ)^6403 := by
    have hnat : (5390892731 : ℕ)^8451*100000000000000^6403 ≤ 44241754668597^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390892731 10000000000 44241754668597 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267431827/10000000000 : ℝ)^8451 ≤ (21454693962479/50000000000000 : ℝ)^6403 := by
    have hnat : (5267431827 : ℕ)^8451*50000000000000^6403 ≤ 21454693962479^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267431827 10000000000 21454693962479 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422523299/2000000000 : ℝ), (5390892731/10000000000 : ℝ), (5267431827/10000000000 : ℝ)] ![(6424428697557/50000000000000 : ℝ), (44241754668597/100000000000000 : ℝ), (21454693962479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422523299/2000000000 : ℝ)|^8451 ≤ (6424428697557/50000000000000 : ℝ)^6403
        have hw : |(-422523299/2000000000 : ℝ)|=(422523299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390892731/10000000000 : ℝ)|^8451 ≤ (44241754668597/100000000000000 : ℝ)^6403
        have hw : |(5390892731/10000000000 : ℝ)|=(5390892731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267431827/10000000000 : ℝ)|^8451 ≤ (21454693962479/50000000000000 : ℝ)^6403
        have hw : |(5267431827/10000000000 : ℝ)|=(5267431827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s7_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344221723/10000000000 : ℝ)*x 0 + (-108760531/500000000 : ℝ)*x 1 + (5267431731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344221723/10000000000 : ℝ)^8451 ≤ (43736930037791/100000000000000 : ℝ)^6403 := by
    have hnat : (5344221723 : ℕ)^8451*100000000000000^6403 ≤ 43736930037791^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344221723 10000000000 43736930037791 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108760531/500000000 : ℝ)^8451 ≤ (2670736609549/20000000000000 : ℝ)^6403 := by
    have hnat : (108760531 : ℕ)^8451*20000000000000^6403 ≤ 2670736609549^6403*500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108760531 500000000 2670736609549 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267431731/10000000000 : ℝ)^8451 ≤ (42909386892793/100000000000000 : ℝ)^6403 := by
    have hnat : (5267431731 : ℕ)^8451*100000000000000^6403 ≤ 42909386892793^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267431731 10000000000 42909386892793 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344221723/10000000000 : ℝ), (-108760531/500000000 : ℝ), (5267431731/10000000000 : ℝ)] ![(43736930037791/100000000000000 : ℝ), (2670736609549/20000000000000 : ℝ), (42909386892793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344221723/10000000000 : ℝ)|^8451 ≤ (43736930037791/100000000000000 : ℝ)^6403
        have hw : |(5344221723/10000000000 : ℝ)|=(5344221723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108760531/500000000 : ℝ)|^8451 ≤ (2670736609549/20000000000000 : ℝ)^6403
        have hw : |(-108760531/500000000 : ℝ)|=(108760531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267431731/10000000000 : ℝ)|^8451 ≤ (42909386892793/100000000000000 : ℝ)^6403
        have hw : |(5267431731/10000000000 : ℝ)|=(5267431731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s7_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068844327/2000000000 : ℝ)*x 0 + (5267431821/10000000000 : ℝ)*x 1 + (-2175210619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068844327/2000000000 : ℝ)^8451 ≤ (174947716349/400000000000 : ℝ)^6403 := by
    have hnat : (1068844327 : ℕ)^8451*400000000000^6403 ≤ 174947716349^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068844327 2000000000 174947716349 400000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267431821/10000000000 : ℝ)^8451 ≤ (1340918370639/3125000000000 : ℝ)^6403 := by
    have hnat : (5267431821 : ℕ)^8451*3125000000000^6403 ≤ 1340918370639^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267431821 10000000000 1340918370639 3125000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175210619/10000000000 : ℝ)^8451 ≤ (6676841519821/50000000000000 : ℝ)^6403 := by
    have hnat : (2175210619 : ℕ)^8451*50000000000000^6403 ≤ 6676841519821^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175210619 10000000000 6676841519821 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068844327/2000000000 : ℝ), (5267431821/10000000000 : ℝ), (-2175210619/10000000000 : ℝ)] ![(174947716349/400000000000 : ℝ), (1340918370639/3125000000000 : ℝ), (6676841519821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068844327/2000000000 : ℝ)|^8451 ≤ (174947716349/400000000000 : ℝ)^6403
        have hw : |(1068844327/2000000000 : ℝ)|=(1068844327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267431821/10000000000 : ℝ)|^8451 ≤ (1340918370639/3125000000000 : ℝ)^6403
        have hw : |(5267431821/10000000000 : ℝ)|=(5267431821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175210619/10000000000 : ℝ)|^8451 ≤ (6676841519821/50000000000000 : ℝ)^6403
        have hw : |(-2175210619/10000000000 : ℝ)|=(2175210619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s7_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174291817/5000000000 : ℝ)*x 0 + (4224729607/10000000000 : ℝ)*x 1 + (4475952803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174291817/5000000000 : ℝ)^8451 ≤ (16658786352789/50000000000000 : ℝ)^6403 := by
    have hnat : (2174291817 : ℕ)^8451*50000000000000^6403 ≤ 16658786352789^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174291817 5000000000 16658786352789 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224729607/10000000000 : ℝ)^8451 ≤ (6414173034111/20000000000000 : ℝ)^6403 := by
    have hnat : (4224729607 : ℕ)^8451*20000000000000^6403 ≤ 6414173034111^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224729607 10000000000 6414173034111 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475952803/10000000000 : ℝ)^8451 ≤ (2163222631831/6250000000000 : ℝ)^6403 := by
    have hnat : (4475952803 : ℕ)^8451*6250000000000^6403 ≤ 2163222631831^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475952803 10000000000 2163222631831 6250000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174291817/5000000000 : ℝ), (4224729607/10000000000 : ℝ), (4475952803/10000000000 : ℝ)] ![(16658786352789/50000000000000 : ℝ), (6414173034111/20000000000000 : ℝ), (2163222631831/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174291817/5000000000 : ℝ)|^8451 ≤ (16658786352789/50000000000000 : ℝ)^6403
        have hw : |(2174291817/5000000000 : ℝ)|=(2174291817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224729607/10000000000 : ℝ)|^8451 ≤ (6414173034111/20000000000000 : ℝ)^6403
        have hw : |(4224729607/10000000000 : ℝ)|=(4224729607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475952803/10000000000 : ℝ)|^8451 ≤ (2163222631831/6250000000000 : ℝ)^6403
        have hw : |(4475952803/10000000000 : ℝ)|=(4475952803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s7_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211262111/1000000000 : ℝ)*x 0 + (1053548673/2000000000 : ℝ)*x 1 + (5390580067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211262111/1000000000 : ℝ)^8451 ≤ (12848894441027/100000000000000 : ℝ)^6403 := by
    have hnat : (211262111 : ℕ)^8451*100000000000000^6403 ≤ 12848894441027^6403*1000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211262111 1000000000 12848894441027 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053548673/2000000000 : ℝ)^8451 ≤ (10728184381593/25000000000000 : ℝ)^6403 := by
    have hnat : (1053548673 : ℕ)^8451*25000000000000^6403 ≤ 10728184381593^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053548673 2000000000 10728184381593 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390580067/10000000000 : ℝ)^8451 ≤ (44238368020249/100000000000000 : ℝ)^6403 := by
    have hnat : (5390580067 : ℕ)^8451*100000000000000^6403 ≤ 44238368020249^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390580067 10000000000 44238368020249 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211262111/1000000000 : ℝ), (1053548673/2000000000 : ℝ), (5390580067/10000000000 : ℝ)] ![(12848894441027/100000000000000 : ℝ), (10728184381593/25000000000000 : ℝ), (44238368020249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211262111/1000000000 : ℝ)|^8451 ≤ (12848894441027/100000000000000 : ℝ)^6403
        have hw : |(-211262111/1000000000 : ℝ)|=(211262111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053548673/2000000000 : ℝ)|^8451 ≤ (10728184381593/25000000000000 : ℝ)^6403
        have hw : |(1053548673/2000000000 : ℝ)|=(1053548673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390580067/10000000000 : ℝ)|^8451 ≤ (44238368020249/100000000000000 : ℝ)^6403
        have hw : |(5390580067/10000000000 : ℝ)|=(5390580067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s7_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312686119/10000000000 : ℝ)*x 0 + (-1026031167/5000000000 : ℝ)*x 1 + (5390580093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312686119/10000000000 : ℝ)^8451 ≤ (21698308340571/50000000000000 : ℝ)^6403 := by
    have hnat : (5312686119 : ℕ)^8451*50000000000000^6403 ≤ 21698308340571^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312686119 10000000000 21698308340571 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026031167/5000000000 : ℝ)^8451 ≤ (6182507500981/50000000000000 : ℝ)^6403 := by
    have hnat : (1026031167 : ℕ)^8451*50000000000000^6403 ≤ 6182507500981^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026031167 5000000000 6182507500981 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390580093/10000000000 : ℝ)^8451 ≤ (11059592075467/25000000000000 : ℝ)^6403 := by
    have hnat : (5390580093 : ℕ)^8451*25000000000000^6403 ≤ 11059592075467^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390580093 10000000000 11059592075467 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312686119/10000000000 : ℝ), (-1026031167/5000000000 : ℝ), (5390580093/10000000000 : ℝ)] ![(21698308340571/50000000000000 : ℝ), (6182507500981/50000000000000 : ℝ), (11059592075467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312686119/10000000000 : ℝ)|^8451 ≤ (21698308340571/50000000000000 : ℝ)^6403
        have hw : |(5312686119/10000000000 : ℝ)|=(5312686119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026031167/5000000000 : ℝ)|^8451 ≤ (6182507500981/50000000000000 : ℝ)^6403
        have hw : |(-1026031167/5000000000 : ℝ)|=(1026031167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390580093/10000000000 : ℝ)|^8451 ≤ (11059592075467/25000000000000 : ℝ)^6403
        have hw : |(5390580093/10000000000 : ℝ)|=(5390580093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s7_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312686103/10000000000 : ℝ)*x 0 + (2695290061/5000000000 : ℝ)*x 1 + (-513015579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312686103/10000000000 : ℝ)^8451 ≤ (43396616508643/100000000000000 : ℝ)^6403 := by
    have hnat : (5312686103 : ℕ)^8451*100000000000000^6403 ≤ 43396616508643^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312686103 10000000000 43396616508643 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695290061/5000000000 : ℝ)^8451 ≤ (44238368615981/100000000000000 : ℝ)^6403 := by
    have hnat : (2695290061 : ℕ)^8451*100000000000000^6403 ≤ 44238368615981^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695290061 5000000000 44238368615981 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513015579/2500000000 : ℝ)^8451 ≤ (1545626857351/12500000000000 : ℝ)^6403 := by
    have hnat : (513015579 : ℕ)^8451*12500000000000^6403 ≤ 1545626857351^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513015579 2500000000 1545626857351 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312686103/10000000000 : ℝ), (2695290061/5000000000 : ℝ), (-513015579/2500000000 : ℝ)] ![(43396616508643/100000000000000 : ℝ), (44238368615981/100000000000000 : ℝ), (1545626857351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312686103/10000000000 : ℝ)|^8451 ≤ (43396616508643/100000000000000 : ℝ)^6403
        have hw : |(5312686103/10000000000 : ℝ)|=(5312686103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695290061/5000000000 : ℝ)|^8451 ≤ (44238368615981/100000000000000 : ℝ)^6403
        have hw : |(2695290061/5000000000 : ℝ)|=(2695290061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513015579/2500000000 : ℝ)|^8451 ≤ (1545626857351/12500000000000 : ℝ)^6403
        have hw : |(-513015579/2500000000 : ℝ)|=(513015579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s7_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174296577/5000000000 : ℝ)*x 0 + (895063773/2000000000 : ℝ)*x 1 + (132042679/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174296577/5000000000 : ℝ)^8451 ≤ (8329417243687/25000000000000 : ℝ)^6403 := by
    have hnat : (2174296577 : ℕ)^8451*25000000000000^6403 ≤ 8329417243687^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174296577 5000000000 8329417243687 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895063773/2000000000 : ℝ)^8451 ≤ (34605092214037/100000000000000 : ℝ)^6403 := by
    have hnat : (895063773 : ℕ)^8451*100000000000000^6403 ≤ 34605092214037^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895063773 2000000000 34605092214037 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132042679/312500000 : ℝ)^8451 ≤ (32077238796147/100000000000000 : ℝ)^6403 := by
    have hnat : (132042679 : ℕ)^8451*100000000000000^6403 ≤ 32077238796147^6403*312500000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132042679 312500000 32077238796147 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174296577/5000000000 : ℝ), (895063773/2000000000 : ℝ), (132042679/312500000 : ℝ)] ![(8329417243687/25000000000000 : ℝ), (34605092214037/100000000000000 : ℝ), (32077238796147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174296577/5000000000 : ℝ)|^8451 ≤ (8329417243687/25000000000000 : ℝ)^6403
        have hw : |(2174296577/5000000000 : ℝ)|=(2174296577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895063773/2000000000 : ℝ)|^8451 ≤ (34605092214037/100000000000000 : ℝ)^6403
        have hw : |(895063773/2000000000 : ℝ)|=(895063773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132042679/312500000 : ℝ)|^8451 ≤ (32077238796147/100000000000000 : ℝ)^6403
        have hw : |(132042679/312500000 : ℝ)|=(132042679/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14113/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5747/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5747/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5747/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5747/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5747/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5747/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5747/50000 : ℝ) ^ (4225/1024 : ℝ) ≤ (3322509033126377/25000000000000000000 : ℝ) := by
    have hpowers : (5747/50000 : ℝ)^4225 ≤ (3322509033126377/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5747 : ℕ)^4225*25000000000000000000^1024 ≤ 3322509033126377^1024*50000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5747 50000 3322509033126377 25000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5747/50000 : ℝ)) (X := (3322509033126377/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14117/100000 : ℝ) ^ (4225/1024 : ℝ) ≤ (6207076910774923/20000000000000000000 : ℝ) := by
    have hpowers : (14117/100000 : ℝ)^4225 ≤ (6207076910774923/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14117 : ℕ)^4225*20000000000000000000^1024 ≤ 6207076910774923^1024*100000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14117 100000 6207076910774923 20000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14117/100000 : ℝ)) (X := (6207076910774923/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503322509033126377/12500000000000000000 : ℝ) ≤ (2500161037005053/2500000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (12503322509033126377/12500000000000000000 : ℝ)^1024 ≤ (2500161037005053/2500000000000000 : ℝ)^4225 := by
      have hnat : (12503322509033126377 : ℕ)^1024*2500000000000000^4225 ≤ 2500161037005053^4225*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503322509033126377 12500000000000000000 2500161037005053 2500000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500161037005053/2500000000000000 : ℝ)) (X := (12503322509033126377/12500000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044325420686380123/100000000000000000000 : ℝ) ≤ (2500268530244753/2500000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (100044325420686380123/100000000000000000000 : ℝ)^1024 ≤ (2500268530244753/2500000000000000 : ℝ)^4225 := by
      have hnat : (100044325420686380123 : ℕ)^1024*2500000000000000^4225 ≤ 2500268530244753^4225*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044325420686380123 100000000000000000000 2500268530244753 2500000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500268530244753/2500000000000000 : ℝ)) (X := (100044325420686380123/100000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006207076910774923/10000000000000000000 : ℝ) ≤ (2500376023484453/2500000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (10006207076910774923/10000000000000000000 : ℝ)^1024 ≤ (2500376023484453/2500000000000000 : ℝ)^4225 := by
      have hnat : (10006207076910774923 : ℕ)^1024*2500000000000000^4225 ≤ 2500376023484453^4225*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006207076910774923 10000000000000000000 2500376023484453 2500000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500376023484453/2500000000000000 : ℝ)) (X := (10006207076910774923/10000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3322509033126377/25000000000000000000 : ℝ) ≤ ((6555451345470030419/6557500000000000000 : ℝ)+2*(1074932397/655750000000 : ℝ)*(5747/50000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (6555451345470030419/6557500000000000000 : ℝ)+2*(1074932397/655750000000 : ℝ)*(5747/50000 : ℝ)=(2500161037005053/2500000000000000 : ℝ) by norm_num, show 1+2*(3322509033126377/25000000000000000000 : ℝ)=(12503322509033126377/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6207076910774923/20000000000000000000 : ℝ)+(3322509033126377/25000000000000000000 : ℝ) ≤ ((6555451345470030419/6557500000000000000 : ℝ)+(1074932397/655750000000 : ℝ)*((14117/100000 : ℝ)+(5747/50000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (6555451345470030419/6557500000000000000 : ℝ)+(1074932397/655750000000 : ℝ)*((14117/100000 : ℝ)+(5747/50000 : ℝ))=(2500268530244753/2500000000000000 : ℝ) by norm_num, show 1+(6207076910774923/20000000000000000000 : ℝ)+(3322509033126377/25000000000000000000 : ℝ)=(100044325420686380123/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6207076910774923/20000000000000000000 : ℝ) ≤ ((6555451345470030419/6557500000000000000 : ℝ)+2*(1074932397/655750000000 : ℝ)*(14117/100000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (6555451345470030419/6557500000000000000 : ℝ)+2*(1074932397/655750000000 : ℝ)*(14117/100000 : ℝ)=(2500376023484453/2500000000000000 : ℝ) by norm_num, show 1+2*(6207076910774923/20000000000000000000 : ℝ)=(10006207076910774923/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6555451345470030419/6557500000000000000 : ℝ)*(X 1 0+X 2 0)+(1074932397/655750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (6555451345470030419/6557500000000000000 : ℝ)) (alpha := (1074932397/655750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6555451345470030419/6557500000000000000 : ℝ)*(X 0 1+X 2 1)+(1074932397/655750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (6555451345470030419/6557500000000000000 : ℝ)) (alpha := (1074932397/655750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6555451345470030419/6557500000000000000 : ℝ)*(X 0 2+X 1 2)+(1074932397/655750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (6555451345470030419/6557500000000000000 : ℝ)) (alpha := (1074932397/655750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-422523299/2000000000 : ℝ)*X 0 0+(5390892731/10000000000 : ℝ)*X 0 1+(5267431827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344221723/10000000000 : ℝ)*X 1 0+(-108760531/500000000 : ℝ)*X 1 1+(5267431731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068844327/2000000000 : ℝ)*X 2 0+(5267431821/10000000000 : ℝ)*X 2 1+(-2175210619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174291817/5000000000 : ℝ)*X 0 0+(4224729607/10000000000 : ℝ)*X 0 1+(4475952803/10000000000 : ℝ)*X 0 2+(2174291817/5000000000 : ℝ)*X 1 0+(4224729607/10000000000 : ℝ)*X 1 1+(4475952803/10000000000 : ℝ)*X 1 2+(2174291817/5000000000 : ℝ)*X 2 0+(4224729607/10000000000 : ℝ)*X 2 1+(4475952803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-211262111/1000000000 : ℝ)*X 0 0+(1053548673/2000000000 : ℝ)*X 0 1+(5390580067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312686119/10000000000 : ℝ)*X 1 0+(-1026031167/5000000000 : ℝ)*X 1 1+(5390580093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312686103/10000000000 : ℝ)*X 2 0+(2695290061/5000000000 : ℝ)*X 2 1+(-513015579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174296577/5000000000 : ℝ)*X 0 0+(895063773/2000000000 : ℝ)*X 0 1+(132042679/312500000 : ℝ)*X 0 2+(2174296577/5000000000 : ℝ)*X 1 0+(895063773/2000000000 : ℝ)*X 1 1+(132042679/312500000 : ℝ)*X 1 2+(2174296577/5000000000 : ℝ)*X 2 0+(895063773/2000000000 : ℝ)*X 2 1+(132042679/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357587550998686601631458037/32787500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265303283/12500000000000 : ℝ)*(base19) + (241069981/12500000000000 : ℝ)*(base23) + (32327873/100000000000000 : ℝ)*(lower2) + (28495189/12500000000000 : ℝ)*(upper3) + (32436201/20000000000000 : ℝ)*(upper5) + (1208043049877959/20000000000000 : ℝ)*(major0) + (1208043049877959/20000000000000 : ℝ)*(major1) + (1208043049877959/20000000000000 : ℝ)*(major2) + (4049895175542443/50000000000000 : ℝ)*(sp0) + (8099844967810601/100000000000000 : ℝ)*(sp1) + (8099845161677017/100000000000000 : ℝ)*(sp2) + (1990276519085631/50000000000000 : ℝ)*(sp3) + (56739151979/100000000000000 : ℝ)*(sp4) + (7501707731/25000000000000 : ℝ)*(sp7) + (1990291522501093/50000000000000 : ℝ)*(f.failure) + (1619969418047373/20000000000000 : ℝ)*(f.sum) + (95951614439/327875000000000000000000000 : ℝ)*base66 + (2774893225308384821/131150000000000000000000000000000 : ℝ)*base67 + (934973995928684821/131150000000000000000000000000000 : ℝ)*base69 + (3078303814871584821/131150000000000000000000000000000 : ℝ)*base71 + (4357261412649/1311500000000000000000000000 : ℝ)*base73 + (4878841373819715179/131150000000000000000000000000000 : ℝ)*base76 + (2092085025648784821/131150000000000000000000000000000 : ℝ)*base77 + (667978317328984821/131150000000000000000000000000000 : ℝ)*base79 + (814507427579/524600000000000000000000000 : ℝ)*base81 + (3523511/5000000000000000000000 : ℝ)*base90 + (3523511/5000000000000000000000 : ℝ)*base92 + (3523511/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (497329111454006402681694609/81968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20843867/2000000000000 : ℝ)*(base19) + (286924151/25000000000000 : ℝ)*(base23) + (147029989/100000000000000 : ℝ)*(upper3) + (49720399/100000000000000 : ℝ)*(lower4) + (45370309/50000000000000 : ℝ)*(upper5) + (3035408969624163/50000000000000 : ℝ)*(major0) + (3035408969624163/50000000000000 : ℝ)*(major1) + (3035408969624163/50000000000000 : ℝ)*(major2) + (3598575967/12500000000000 : ℝ)*(sp1) + (6985275827/20000000000000 : ℝ)*(sp2) + (8140885047257333/100000000000000 : ℝ)*(sp4) + (1017606902057031/12500000000000 : ℝ)*(sp5) + (1628169794636319/20000000000000 : ℝ)*(sp6) + (1000187657248981/25000000000000 : ℝ)*(sp7) + (1000187657248981/25000000000000 : ℝ)*(f.failure) + (8140885047257333/100000000000000 : ℝ)*(f.sum) + (5906624722579/1311500000000000000000000000 : ℝ)*base66 + (5217495277653039297/327875000000000000000000000000000 : ℝ)*base67 + (7768912893541289297/327875000000000000000000000000000 : ℝ)*base69 + (1079482831423585703/327875000000000000000000000000000 : ℝ)*base72 + (2390667347631/655750000000000000000000000 : ℝ)*base74 + (3144773481405414297/327875000000000000000000000000000 : ℝ)*base75 + (2804527903887664297/327875000000000000000000000000000 : ℝ)*base77 + (5953783220498039297/327875000000000000000000000000000 : ℝ)*base79 + (4528599866441/2623000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20820487/2500000000000000000000 : ℝ)*base90 + (20820487/2500000000000000000000 : ℝ)*base92 + (20820487/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1258_s8_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056310871/5000000000 : ℝ)*x 0 + (2695429651/5000000000 : ℝ)*x 1 + (5267461587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056310871/5000000000 : ℝ)^8451 ≤ (401528109821/3125000000000 : ℝ)^6403 := by
    have hnat : (1056310871 : ℕ)^8451*3125000000000^6403 ≤ 401528109821^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056310871 5000000000 401528109821 3125000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695429651/5000000000 : ℝ)^8451 ≤ (22120696288183/50000000000000 : ℝ)^6403 := by
    have hnat : (2695429651 : ℕ)^8451*50000000000000^6403 ≤ 22120696288183^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695429651 5000000000 22120696288183 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267461587/10000000000 : ℝ)^8451 ≤ (42909707896471/100000000000000 : ℝ)^6403 := by
    have hnat : (5267461587 : ℕ)^8451*100000000000000^6403 ≤ 42909707896471^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267461587 10000000000 42909707896471 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056310871/5000000000 : ℝ), (2695429651/5000000000 : ℝ), (5267461587/10000000000 : ℝ)] ![(401528109821/3125000000000 : ℝ), (22120696288183/50000000000000 : ℝ), (42909707896471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056310871/5000000000 : ℝ)|^8451 ≤ (401528109821/3125000000000 : ℝ)^6403
        have hw : |(-1056310871/5000000000 : ℝ)|=(1056310871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695429651/5000000000 : ℝ)|^8451 ≤ (22120696288183/50000000000000 : ℝ)^6403
        have hw : |(2695429651/5000000000 : ℝ)|=(2695429651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267461587/10000000000 : ℝ)|^8451 ≤ (42909707896471/100000000000000 : ℝ)^6403
        have hw : |(5267461587/10000000000 : ℝ)|=(5267461587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s8_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167006639/312500000 : ℝ)*x 0 + (-435036673/2000000000 : ℝ)*x 1 + (5267461589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167006639/312500000 : ℝ)^8451 ≤ (43736829852901/100000000000000 : ℝ)^6403 := by
    have hnat : (167006639 : ℕ)^8451*100000000000000^6403 ≤ 43736829852901^6403*312500000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167006639 312500000 43736829852901 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435036673/2000000000 : ℝ)^8451 ≤ (267069244237/2000000000000 : ℝ)^6403 := by
    have hnat : (435036673 : ℕ)^8451*2000000000000^6403 ≤ 267069244237^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435036673 2000000000 267069244237 2000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267461589/10000000000 : ℝ)^8451 ≤ (1716388316719/4000000000000 : ℝ)^6403 := by
    have hnat : (5267461589 : ℕ)^8451*4000000000000^6403 ≤ 1716388316719^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267461589 10000000000 1716388316719 4000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167006639/312500000 : ℝ), (-435036673/2000000000 : ℝ), (5267461589/10000000000 : ℝ)] ![(43736829852901/100000000000000 : ℝ), (267069244237/2000000000000 : ℝ), (1716388316719/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167006639/312500000 : ℝ)|^8451 ≤ (43736829852901/100000000000000 : ℝ)^6403
        have hw : |(167006639/312500000 : ℝ)|=(167006639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435036673/2000000000 : ℝ)|^8451 ≤ (267069244237/2000000000000 : ℝ)^6403
        have hw : |(-435036673/2000000000 : ℝ)|=(435036673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267461589/10000000000 : ℝ)|^8451 ≤ (1716388316719/4000000000000 : ℝ)^6403
        have hw : |(5267461589/10000000000 : ℝ)|=(5267461589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s8_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344212447/10000000000 : ℝ)*x 0 + (5267461591/10000000000 : ℝ)*x 1 + (-2175183363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344212447/10000000000 : ℝ)^8451 ≤ (43736829842099/100000000000000 : ℝ)^6403 := by
    have hnat : (5344212447 : ℕ)^8451*100000000000000^6403 ≤ 43736829842099^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344212447 10000000000 43736829842099 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267461591/10000000000 : ℝ)^8451 ≤ (21454853969739/50000000000000 : ℝ)^6403 := by
    have hnat : (5267461591 : ℕ)^8451*50000000000000^6403 ≤ 21454853969739^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267461591 10000000000 21454853969739 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175183363/10000000000 : ℝ)^8451 ≤ (2670692439129/20000000000000 : ℝ)^6403 := by
    have hnat : (2175183363 : ℕ)^8451*20000000000000^6403 ≤ 2670692439129^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175183363 10000000000 2670692439129 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344212447/10000000000 : ℝ), (5267461591/10000000000 : ℝ), (-2175183363/10000000000 : ℝ)] ![(43736829842099/100000000000000 : ℝ), (21454853969739/50000000000000 : ℝ), (2670692439129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344212447/10000000000 : ℝ)|^8451 ≤ (43736829842099/100000000000000 : ℝ)^6403
        have hw : |(5344212447/10000000000 : ℝ)|=(5344212447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267461591/10000000000 : ℝ)|^8451 ≤ (21454853969739/50000000000000 : ℝ)^6403
        have hw : |(5267461591/10000000000 : ℝ)|=(5267461591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175183363/10000000000 : ℝ)|^8451 ≤ (2670692439129/20000000000000 : ℝ)^6403
        have hw : |(-2175183363/10000000000 : ℝ)|=(2175183363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s8_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348585351/10000000000 : ℝ)*x 0 + (528099209/1250000000 : ℝ)*x 1 + (4475888209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348585351/10000000000 : ℝ)^8451 ≤ (6663518013681/20000000000000 : ℝ)^6403 := by
    have hnat : (4348585351 : ℕ)^8451*20000000000000^6403 ≤ 6663518013681^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348585351 10000000000 6663518013681 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528099209/1250000000 : ℝ)^8451 ≤ (16035753528527/50000000000000 : ℝ)^6403 := by
    have hnat : (528099209 : ℕ)^8451*50000000000000^6403 ≤ 16035753528527^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528099209 1250000000 16035753528527 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475888209/10000000000 : ℝ)^8451 ≤ (17305451428631/50000000000000 : ℝ)^6403 := by
    have hnat : (4475888209 : ℕ)^8451*50000000000000^6403 ≤ 17305451428631^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475888209 10000000000 17305451428631 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348585351/10000000000 : ℝ), (528099209/1250000000 : ℝ), (4475888209/10000000000 : ℝ)] ![(6663518013681/20000000000000 : ℝ), (16035753528527/50000000000000 : ℝ), (17305451428631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348585351/10000000000 : ℝ)|^8451 ≤ (6663518013681/20000000000000 : ℝ)^6403
        have hw : |(4348585351/10000000000 : ℝ)|=(4348585351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528099209/1250000000 : ℝ)|^8451 ≤ (16035753528527/50000000000000 : ℝ)^6403
        have hw : |(528099209/1250000000 : ℝ)|=(528099209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475888209/10000000000 : ℝ)|^8451 ≤ (17305451428631/50000000000000 : ℝ)^6403
        have hw : |(4475888209/10000000000 : ℝ)|=(4475888209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s8_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112626249/10000000000 : ℝ)*x 0 + (5267772773/10000000000 : ℝ)*x 1 + (2695273533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112626249/10000000000 : ℝ)^8451 ≤ (12848935693267/100000000000000 : ℝ)^6403 := by
    have hnat : (2112626249 : ℕ)^8451*100000000000000^6403 ≤ 12848935693267^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112626249 10000000000 12848935693267 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267772773/10000000000 : ℝ)^8451 ≤ (21456526859627/50000000000000 : ℝ)^6403 := by
    have hnat : (5267772773 : ℕ)^8451*50000000000000^6403 ≤ 21456526859627^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267772773 10000000000 21456526859627 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695273533/5000000000 : ℝ)^8451 ≤ (44238010570603/100000000000000 : ℝ)^6403 := by
    have hnat : (2695273533 : ℕ)^8451*100000000000000^6403 ≤ 44238010570603^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695273533 5000000000 44238010570603 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112626249/10000000000 : ℝ), (5267772773/10000000000 : ℝ), (2695273533/5000000000 : ℝ)] ![(12848935693267/100000000000000 : ℝ), (21456526859627/50000000000000 : ℝ), (44238010570603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112626249/10000000000 : ℝ)|^8451 ≤ (12848935693267/100000000000000 : ℝ)^6403
        have hw : |(-2112626249/10000000000 : ℝ)|=(2112626249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267772773/10000000000 : ℝ)|^8451 ≤ (21456526859627/50000000000000 : ℝ)^6403
        have hw : |(5267772773/10000000000 : ℝ)|=(5267772773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695273533/5000000000 : ℝ)|^8451 ≤ (44238010570603/100000000000000 : ℝ)^6403
        have hw : |(2695273533/5000000000 : ℝ)|=(2695273533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s8_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312693049/10000000000 : ℝ)*x 0 + (-410419617/2000000000 : ℝ)*x 1 + (1078109389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312693049/10000000000 : ℝ)^8451 ≤ (43396691394737/100000000000000 : ℝ)^6403 := by
    have hnat : (5312693049 : ℕ)^8451*100000000000000^6403 ≤ 43396691394737^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312693049 10000000000 43396691394737 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410419617/2000000000 : ℝ)^8451 ≤ (12365299328961/100000000000000 : ℝ)^6403 := by
    have hnat : (410419617 : ℕ)^8451*100000000000000^6403 ≤ 12365299328961^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410419617 2000000000 12365299328961 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078109389/2000000000 : ℝ)^8451 ≤ (11059502314999/25000000000000 : ℝ)^6403 := by
    have hnat : (1078109389 : ℕ)^8451*25000000000000^6403 ≤ 11059502314999^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078109389 2000000000 11059502314999 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312693049/10000000000 : ℝ), (-410419617/2000000000 : ℝ), (1078109389/2000000000 : ℝ)] ![(43396691394737/100000000000000 : ℝ), (12365299328961/100000000000000 : ℝ), (11059502314999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312693049/10000000000 : ℝ)|^8451 ≤ (43396691394737/100000000000000 : ℝ)^6403
        have hw : |(5312693049/10000000000 : ℝ)|=(5312693049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410419617/2000000000 : ℝ)|^8451 ≤ (12365299328961/100000000000000 : ℝ)^6403
        have hw : |(-410419617/2000000000 : ℝ)|=(410419617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078109389/2000000000 : ℝ)|^8451 ≤ (11059502314999/25000000000000 : ℝ)^6403
        have hw : |(1078109389/2000000000 : ℝ)|=(1078109389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s8_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062538577/2000000000 : ℝ)*x 0 + (2695273591/5000000000 : ℝ)*x 1 + (-410419597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062538577/2000000000 : ℝ)^8451 ≤ (43396689626623/100000000000000 : ℝ)^6403 := by
    have hnat : (1062538577 : ℕ)^8451*100000000000000^6403 ≤ 43396689626623^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062538577 2000000000 43396689626623 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695273591/5000000000 : ℝ)^8451 ≤ (22119005913527/50000000000000 : ℝ)^6403 := by
    have hnat : (2695273591 : ℕ)^8451*50000000000000^6403 ≤ 22119005913527^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695273591 5000000000 22119005913527 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410419597/2000000000 : ℝ)^8451 ≤ (12365298533661/100000000000000 : ℝ)^6403 := by
    have hnat : (410419597 : ℕ)^8451*100000000000000^6403 ≤ 12365298533661^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410419597 2000000000 12365298533661 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062538577/2000000000 : ℝ), (2695273591/5000000000 : ℝ), (-410419597/2000000000 : ℝ)] ![(43396689626623/100000000000000 : ℝ), (22119005913527/50000000000000 : ℝ), (12365298533661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062538577/2000000000 : ℝ)|^8451 ≤ (43396689626623/100000000000000 : ℝ)^6403
        have hw : |(1062538577/2000000000 : ℝ)|=(1062538577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695273591/5000000000 : ℝ)|^8451 ≤ (22119005913527/50000000000000 : ℝ)^6403
        have hw : |(2695273591/5000000000 : ℝ)|=(2695273591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410419597/2000000000 : ℝ)|^8451 ≤ (12365298533661/100000000000000 : ℝ)^6403
        have hw : |(-410419597/2000000000 : ℝ)|=(410419597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s8_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543574341/1250000000 : ℝ)*x 0 + (2237627457/5000000000 : ℝ)*x 1 + (1056357319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543574341/1250000000 : ℝ)^8451 ≤ (33317684891527/100000000000000 : ℝ)^6403 := by
    have hnat : (543574341 : ℕ)^8451*100000000000000^6403 ≤ 33317684891527^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543574341 1250000000 33317684891527 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237627457/5000000000 : ℝ)^8451 ≤ (34604439554071/100000000000000 : ℝ)^6403 := by
    have hnat : (2237627457 : ℕ)^8451*100000000000000^6403 ≤ 34604439554071^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237627457 5000000000 34604439554071 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056357319/2500000000 : ℝ)^8451 ≤ (32077875533317/100000000000000 : ℝ)^6403 := by
    have hnat : (1056357319 : ℕ)^8451*100000000000000^6403 ≤ 32077875533317^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056357319 2500000000 32077875533317 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543574341/1250000000 : ℝ), (2237627457/5000000000 : ℝ), (1056357319/2500000000 : ℝ)] ![(33317684891527/100000000000000 : ℝ), (34604439554071/100000000000000 : ℝ), (32077875533317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543574341/1250000000 : ℝ)|^8451 ≤ (33317684891527/100000000000000 : ℝ)^6403
        have hw : |(543574341/1250000000 : ℝ)|=(543574341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237627457/5000000000 : ℝ)|^8451 ≤ (34604439554071/100000000000000 : ℝ)^6403
        have hw : |(2237627457/5000000000 : ℝ)|=(2237627457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056357319/2500000000 : ℝ)|^8451 ≤ (32077875533317/100000000000000 : ℝ)^6403
        have hw : |(1056357319/2500000000 : ℝ)|=(1056357319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5749/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11497/100000 : ℝ) ^ (4225/1024 : ℝ) ≤ (665217702980247/5000000000000000000 : ℝ) := by
    have hpowers : (11497/100000 : ℝ)^4225 ≤ (665217702980247/5000000000000000000 : ℝ)^1024 := by
      have hnat : (11497 : ℕ)^4225*5000000000000000000^1024 ≤ 665217702980247^1024*100000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11497 100000 665217702980247 5000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11497/100000 : ℝ)) (X := (665217702980247/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14113/100000 : ℝ) ^ (4225/1024 : ℝ) ≤ (30999117763200959/100000000000000000000 : ℝ) := by
    have hpowers : (14113/100000 : ℝ)^4225 ≤ (30999117763200959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14113 : ℕ)^4225*100000000000000000000^1024 ≤ 30999117763200959^1024*100000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14113 100000 30999117763200959 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14113/100000 : ℝ)) (X := (30999117763200959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500665217702980247/2500000000000000000 : ℝ) ≤ (5000322420959311/5000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (2500665217702980247/2500000000000000000 : ℝ)^1024 ≤ (5000322420959311/5000000000000000 : ℝ)^4225 := by
      have hnat : (2500665217702980247 : ℕ)^1024*5000000000000000^4225 ≤ 5000322420959311^4225*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500665217702980247 2500000000000000000 5000322420959311 5000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000322420959311/5000000000000000 : ℝ)) (X := (2500665217702980247/2500000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044303471822805899/100000000000000000000 : ℝ) ≤ (10001073589189823/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (100044303471822805899/100000000000000000000 : ℝ)^1024 ≤ (10001073589189823/10000000000000000 : ℝ)^4225 := by
      have hnat : (100044303471822805899 : ℕ)^1024*10000000000000000^4225 ≤ 10001073589189823^4225*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044303471822805899 100000000000000000000 10001073589189823 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001073589189823/10000000000000000 : ℝ)) (X := (100044303471822805899/100000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030999117763200959/50000000000000000000 : ℝ) ≤ (312546948014407/312500000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50030999117763200959/50000000000000000000 : ℝ)^1024 ≤ (312546948014407/312500000000000 : ℝ)^4225 := by
      have hnat : (50030999117763200959 : ℕ)^1024*312500000000000^4225 ≤ 312546948014407^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030999117763200959 50000000000000000000 312546948014407 312500000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312546948014407/312500000000000 : ℝ)) (X := (50030999117763200959/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(665217702980247/5000000000000000000 : ℝ) ≤ ((4358638048617519893/4360000000000000000 : ℝ)+2*(142915757067/87200000000000 : ℝ)*(11497/100000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (4358638048617519893/4360000000000000000 : ℝ)+2*(142915757067/87200000000000 : ℝ)*(11497/100000 : ℝ)=(5000322420959311/5000000000000000 : ℝ) by norm_num, show 1+2*(665217702980247/5000000000000000000 : ℝ)=(2500665217702980247/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30999117763200959/100000000000000000000 : ℝ)+(665217702980247/5000000000000000000 : ℝ) ≤ ((4358638048617519893/4360000000000000000 : ℝ)+(142915757067/87200000000000 : ℝ)*((14113/100000 : ℝ)+(11497/100000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (4358638048617519893/4360000000000000000 : ℝ)+(142915757067/87200000000000 : ℝ)*((14113/100000 : ℝ)+(11497/100000 : ℝ))=(10001073589189823/10000000000000000 : ℝ) by norm_num, show 1+(30999117763200959/100000000000000000000 : ℝ)+(665217702980247/5000000000000000000 : ℝ)=(100044303471822805899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30999117763200959/100000000000000000000 : ℝ) ≤ ((4358638048617519893/4360000000000000000 : ℝ)+2*(142915757067/87200000000000 : ℝ)*(14113/100000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (4358638048617519893/4360000000000000000 : ℝ)+2*(142915757067/87200000000000 : ℝ)*(14113/100000 : ℝ)=(312546948014407/312500000000000 : ℝ) by norm_num, show 1+2*(30999117763200959/100000000000000000000 : ℝ)=(50030999117763200959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4358638048617519893/4360000000000000000 : ℝ)*(X 1 0+X 2 0)+(142915757067/87200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (11497/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (4358638048617519893/4360000000000000000 : ℝ)) (alpha := (142915757067/87200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4358638048617519893/4360000000000000000 : ℝ)*(X 0 1+X 2 1)+(142915757067/87200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (11497/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (4358638048617519893/4360000000000000000 : ℝ)) (alpha := (142915757067/87200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4358638048617519893/4360000000000000000 : ℝ)*(X 0 2+X 1 2)+(142915757067/87200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (11497/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (4358638048617519893/4360000000000000000 : ℝ)) (alpha := (142915757067/87200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056310871/5000000000 : ℝ)*X 0 0+(2695429651/5000000000 : ℝ)*X 0 1+(5267461587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167006639/312500000 : ℝ)*X 1 0+(-435036673/2000000000 : ℝ)*X 1 1+(5267461589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344212447/10000000000 : ℝ)*X 2 0+(5267461591/10000000000 : ℝ)*X 2 1+(-2175183363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348585351/10000000000 : ℝ)*X 0 0+(528099209/1250000000 : ℝ)*X 0 1+(4475888209/10000000000 : ℝ)*X 0 2+(4348585351/10000000000 : ℝ)*X 1 0+(528099209/1250000000 : ℝ)*X 1 1+(4475888209/10000000000 : ℝ)*X 1 2+(4348585351/10000000000 : ℝ)*X 2 0+(528099209/1250000000 : ℝ)*X 2 1+(4475888209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2112626249/10000000000 : ℝ)*X 0 0+(5267772773/10000000000 : ℝ)*X 0 1+(2695273533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312693049/10000000000 : ℝ)*X 1 0+(-410419617/2000000000 : ℝ)*X 1 1+(1078109389/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062538577/2000000000 : ℝ)*X 2 0+(2695273591/5000000000 : ℝ)*X 2 1+(-410419597/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543574341/1250000000 : ℝ)*X 0 0+(2237627457/5000000000 : ℝ)*X 0 1+(1056357319/2500000000 : ℝ)*X 0 2+(543574341/1250000000 : ℝ)*X 1 0+(2237627457/5000000000 : ℝ)*X 1 1+(1056357319/2500000000 : ℝ)*X 1 2+(543574341/1250000000 : ℝ)*X 2 0+(2237627457/5000000000 : ℝ)*X 2 1+(1056357319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161990732369129821341351471/21800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (359515433/25000000000000 : ℝ)*(base19) + (668315699/50000000000000 : ℝ)*(base23) + (5339613/10000000000000 : ℝ)*(lower2) + (93392261/50000000000000 : ℝ)*(upper3) + (5806403/5000000000000 : ℝ)*(upper5) + (604328226732283/10000000000000 : ℝ)*(major0) + (604328226732283/10000000000000 : ℝ)*(major1) + (604328226732283/10000000000000 : ℝ)*(major2) + (8103919787086723/100000000000000 : ℝ)*(sp0) + (4051979298921597/50000000000000 : ℝ)*(sp1) + (1012994837409191/12500000000000 : ℝ)*(sp2) + (497822868128823/12500000000000 : ℝ)*(sp3) + (40248818203/100000000000000 : ℝ)*(sp4) + (21306017891/100000000000000 : ℝ)*(sp7) + (995651062762119/25000000000000 : ℝ)*(f.failure) + (4051980017952463/50000000000000 : ℝ)*(f.sum) + (1827832771923/436000000000000000000000000 : ℝ)*base66 + (27432499957344281/43600000000000000000000000000000 : ℝ)*base68 + (161513298979744281/43600000000000000000000000000000 : ℝ)*base70 + (241742521082544281/43600000000000000000000000000000 : ℝ)*base72 + (329105179271/436000000000000000000000000 : ℝ)*base74 + (878769202140944281/43600000000000000000000000000000 : ℝ)*base76 + (18001452016944281/43600000000000000000000000000000 : ℝ)*base78 + (593693114896144281/43600000000000000000000000000000 : ℝ)*base80 + (441237096327/436000000000000000000000000 : ℝ)*base82 + (16720787/2500000000000000000000 : ℝ)*base89 + (16720787/2500000000000000000000 : ℝ)*base91 + (16720787/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4954327981351089384783/1090000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338233/195312500000 : ℝ)*(base19) + (165100727/100000000000000 : ℝ)*(base23) + (2172273/50000000000000 : ℝ)*(lower2) + (55592379/50000000000000 : ℝ)*(lower4) + (18978437/20000000000000 : ℝ)*(upper5) + (1518477229585803/25000000000000 : ℝ)*(major0) + (1518477229585803/25000000000000 : ℝ)*(major1) + (1518477229585803/25000000000000 : ℝ)*(major2) + (152174931/10000000000000 : ℝ)*(sp0) + (1424417519/20000000000000 : ℝ)*(sp2) + (1629005707531727/20000000000000 : ℝ)*(sp4) + (8145029886232649/100000000000000 : ℝ)*(sp5) + (8145022772219623/100000000000000 : ℝ)*(sp6) + (1000696906442493/25000000000000 : ℝ)*(sp7) + (1000696906442493/25000000000000 : ℝ)*(f.failure) + (1629006011881589/20000000000000 : ℝ)*(f.sum) + (18955869685511/1090000000000000000000000000 : ℝ)*base65 + (512466496754070921/109000000000000000000000000000000 : ℝ)*base68 + (830369764924929079/109000000000000000000000000000000 : ℝ)*base69 + (380320290039929079/109000000000000000000000000000000 : ℝ)*base71 + (4644118995069/1090000000000000000000000000 : ℝ)*base74 + (530768285599929079/109000000000000000000000000000000 : ℝ)*base75 + (214124346531070921/109000000000000000000000000000000 : ℝ)*base78 + (1090263458358070921/109000000000000000000000000000000 : ℝ)*base80 + (4178463789079/1090000000000000000000000000 : ℝ)*base82 + (1141311/2500000000000000000000 : ℝ)*base90 + (1141311/2500000000000000000000 : ℝ)*base92 + (1141311/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1258_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1258_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1258_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1258_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
