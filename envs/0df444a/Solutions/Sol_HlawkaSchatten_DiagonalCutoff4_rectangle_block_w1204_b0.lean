-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:04.566378+00:00
-- url     : https://prove2.me/submissions/19eee5b3-7836-4aa5-bc78-a125fdf15e9a

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
theorem support_rectangle_w1204_s0_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-936170991/5000000000 : ℝ)*x 0 + (3020055541/5000000000 : ℝ)*x 1 + (2394131577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936170991/5000000000 : ℝ)^8397 ≤ (10906316818429/100000000000000 : ℝ)^6349 := by
    have hnat : (936170991 : ℕ)^8397*100000000000000^6349 ≤ 10906316818429^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936170991 5000000000 10906316818429 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3020055541/5000000000 : ℝ)^8397 ≤ (10267068915757/20000000000000 : ℝ)^6349 := by
    have hnat : (3020055541 : ℕ)^8397*20000000000000^6349 ≤ 10267068915757^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020055541 5000000000 10267068915757 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394131577/5000000000 : ℝ)^8397 ≤ (37758338588211/100000000000000 : ℝ)^6349 := by
    have hnat : (2394131577 : ℕ)^8397*100000000000000^6349 ≤ 37758338588211^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394131577 5000000000 37758338588211 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936170991/5000000000 : ℝ), (3020055541/5000000000 : ℝ), (2394131577/5000000000 : ℝ)] ![(10906316818429/100000000000000 : ℝ), (10267068915757/20000000000000 : ℝ), (37758338588211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936170991/5000000000 : ℝ)|^8397 ≤ (10906316818429/100000000000000 : ℝ)^6349
        have hw : |(-936170991/5000000000 : ℝ)|=(936170991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3020055541/5000000000 : ℝ)|^8397 ≤ (10267068915757/20000000000000 : ℝ)^6349
        have hw : |(3020055541/5000000000 : ℝ)|=(3020055541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2394131577/5000000000 : ℝ)|^8397 ≤ (37758338588211/100000000000000 : ℝ)^6349
        have hw : |(2394131577/5000000000 : ℝ)|=(2394131577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s0_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513300443/10000000000 : ℝ)*x 0 + (-1294516469/5000000000 : ℝ)*x 1 + (239413157/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513300443/10000000000 : ℝ)^8397 ≤ (45498669158971/100000000000000 : ℝ)^6349 := by
    have hnat : (5513300443 : ℕ)^8397*100000000000000^6349 ≤ 45498669158971^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513300443 10000000000 45498669158971 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294516469/5000000000 : ℝ)^8397 ≤ (16742992381231/100000000000000 : ℝ)^6349 := by
    have hnat : (1294516469 : ℕ)^8397*100000000000000^6349 ≤ 16742992381231^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294516469 5000000000 16742992381231 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239413157/500000000 : ℝ)^8397 ≤ (37758338442201/100000000000000 : ℝ)^6349 := by
    have hnat : (239413157 : ℕ)^8397*100000000000000^6349 ≤ 37758338442201^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239413157 500000000 37758338442201 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513300443/10000000000 : ℝ), (-1294516469/5000000000 : ℝ), (239413157/500000000 : ℝ)] ![(45498669158971/100000000000000 : ℝ), (16742992381231/100000000000000 : ℝ), (37758338442201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513300443/10000000000 : ℝ)|^8397 ≤ (45498669158971/100000000000000 : ℝ)^6349
        have hw : |(5513300443/10000000000 : ℝ)|=(5513300443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1294516469/5000000000 : ℝ)|^8397 ≤ (16742992381231/100000000000000 : ℝ)^6349
        have hw : |(-1294516469/5000000000 : ℝ)|=(1294516469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239413157/500000000 : ℝ)|^8397 ≤ (37758338442201/100000000000000 : ℝ)^6349
        have hw : |(239413157/500000000 : ℝ)|=(239413157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s0_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513300431/10000000000 : ℝ)*x 0 + (299266447/625000000 : ℝ)*x 1 + (-1294516469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513300431/10000000000 : ℝ)^8397 ≤ (11374667256999/25000000000000 : ℝ)^6349 := by
    have hnat : (5513300431 : ℕ)^8397*25000000000000^6349 ≤ 11374667256999^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513300431 10000000000 11374667256999 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299266447/625000000 : ℝ)^8397 ≤ (4719792320919/12500000000000 : ℝ)^6349 := by
    have hnat : (299266447 : ℕ)^8397*12500000000000^6349 ≤ 4719792320919^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299266447 625000000 4719792320919 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294516469/5000000000 : ℝ)^8397 ≤ (16742992381231/100000000000000 : ℝ)^6349 := by
    have hnat : (1294516469 : ℕ)^8397*100000000000000^6349 ≤ 16742992381231^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294516469 5000000000 16742992381231 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513300431/10000000000 : ℝ), (299266447/625000000 : ℝ), (-1294516469/5000000000 : ℝ)] ![(11374667256999/25000000000000 : ℝ), (4719792320919/12500000000000 : ℝ), (16742992381231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513300431/10000000000 : ℝ)|^8397 ≤ (11374667256999/25000000000000 : ℝ)^6349
        have hw : |(5513300431/10000000000 : ℝ)|=(5513300431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299266447/625000000 : ℝ)|^8397 ≤ (4719792320919/12500000000000 : ℝ)^6349
        have hw : |(299266447/625000000 : ℝ)|=(299266447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1294516469/5000000000 : ℝ)|^8397 ≤ (16742992381231/100000000000000 : ℝ)^6349
        have hw : |(-1294516469/5000000000 : ℝ)|=(1294516469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s0_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167840897/400000000 : ℝ)*x 0 + (3118378657/10000000000 : ℝ)*x 1 + (2819610291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167840897/400000000 : ℝ)^8397 ≤ (7927137953859/25000000000000 : ℝ)^6349 := by
    have hnat : (167840897 : ℕ)^8397*25000000000000^6349 ≤ 7927137953859^6349*400000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167840897 400000000 7927137953859 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118378657/10000000000 : ℝ)^8397 ≤ (5353345117969/25000000000000 : ℝ)^6349 := by
    have hnat : (3118378657 : ℕ)^8397*25000000000000^6349 ≤ 5353345117969^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118378657 10000000000 5353345117969 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2819610291/5000000000 : ℝ)^8397 ≤ (46878067694949/100000000000000 : ℝ)^6349 := by
    have hnat : (2819610291 : ℕ)^8397*100000000000000^6349 ≤ 46878067694949^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819610291 5000000000 46878067694949 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167840897/400000000 : ℝ), (3118378657/10000000000 : ℝ), (2819610291/5000000000 : ℝ)] ![(7927137953859/25000000000000 : ℝ), (5353345117969/25000000000000 : ℝ), (46878067694949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167840897/400000000 : ℝ)|^8397 ≤ (7927137953859/25000000000000 : ℝ)^6349
        have hw : |(167840897/400000000 : ℝ)|=(167840897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118378657/10000000000 : ℝ)|^8397 ≤ (5353345117969/25000000000000 : ℝ)^6349
        have hw : |(3118378657/10000000000 : ℝ)|=(3118378657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2819610291/5000000000 : ℝ)|^8397 ≤ (46878067694949/100000000000000 : ℝ)^6349
        have hw : |(2819610291/5000000000 : ℝ)|=(2819610291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s0_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1877308097/10000000000 : ℝ)*x 0 + (4820524551/10000000000 : ℝ)*x 1 + (3003355493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1877308097/10000000000 : ℝ)^8397 ≤ (10944591727413/100000000000000 : ℝ)^6349 := by
    have hnat : (1877308097 : ℕ)^8397*100000000000000^6349 ≤ 10944591727413^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877308097 10000000000 10944591727413 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4820524551/10000000000 : ℝ)^8397 ≤ (19047583154831/50000000000000 : ℝ)^6349 := by
    have hnat : (4820524551 : ℕ)^8397*50000000000000^6349 ≤ 19047583154831^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820524551 10000000000 19047583154831 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3003355493/5000000000 : ℝ)^8397 ≤ (25480120974713/50000000000000 : ℝ)^6349 := by
    have hnat : (3003355493 : ℕ)^8397*50000000000000^6349 ≤ 25480120974713^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003355493 5000000000 25480120974713 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1877308097/10000000000 : ℝ), (4820524551/10000000000 : ℝ), (3003355493/5000000000 : ℝ)] ![(10944591727413/100000000000000 : ℝ), (19047583154831/50000000000000 : ℝ), (25480120974713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1877308097/10000000000 : ℝ)|^8397 ≤ (10944591727413/100000000000000 : ℝ)^6349
        have hw : |(-1877308097/10000000000 : ℝ)|=(1877308097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4820524551/10000000000 : ℝ)|^8397 ≤ (19047583154831/50000000000000 : ℝ)^6349
        have hw : |(4820524551/10000000000 : ℝ)|=(4820524551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3003355493/5000000000 : ℝ)|^8397 ≤ (25480120974713/50000000000000 : ℝ)^6349
        have hw : |(3003355493/5000000000 : ℝ)|=(3003355493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s0_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586428231/5000000000 : ℝ)*x 0 + (-342645921/2500000000 : ℝ)*x 1 + (6006712551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586428231/5000000000 : ℝ)^8397 ≤ (10455103150271/25000000000000 : ℝ)^6349 := by
    have hnat : (2586428231 : ℕ)^8397*25000000000000^6349 ≤ 10455103150271^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586428231 5000000000 10455103150271 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342645921/2500000000 : ℝ)^8397 ≤ (1443865573429/20000000000000 : ℝ)^6349 := by
    have hnat : (342645921 : ℕ)^8397*20000000000000^6349 ≤ 1443865573429^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342645921 2500000000 1443865573429 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6006712551/10000000000 : ℝ)^8397 ≤ (12740064877391/25000000000000 : ℝ)^6349 := by
    have hnat : (6006712551 : ℕ)^8397*25000000000000^6349 ≤ 12740064877391^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006712551 10000000000 12740064877391 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586428231/5000000000 : ℝ), (-342645921/2500000000 : ℝ), (6006712551/10000000000 : ℝ)] ![(10455103150271/25000000000000 : ℝ), (1443865573429/20000000000000 : ℝ), (12740064877391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586428231/5000000000 : ℝ)|^8397 ≤ (10455103150271/25000000000000 : ℝ)^6349
        have hw : |(2586428231/5000000000 : ℝ)|=(2586428231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-342645921/2500000000 : ℝ)|^8397 ≤ (1443865573429/20000000000000 : ℝ)^6349
        have hw : |(-342645921/2500000000 : ℝ)|=(342645921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6006712551/10000000000 : ℝ)|^8397 ≤ (12740064877391/25000000000000 : ℝ)^6349
        have hw : |(6006712551/10000000000 : ℝ)|=(6006712551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s0_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (206914289/400000000 : ℝ)*x 0 + (1501677873/2500000000 : ℝ)*x 1 + (-68529211/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206914289/400000000 : ℝ)^8397 ≤ (41820420759413/100000000000000 : ℝ)^6349 := by
    have hnat : (206914289 : ℕ)^8397*100000000000000^6349 ≤ 41820420759413^6349*400000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206914289 400000000 41820420759413 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1501677873/2500000000 : ℝ)^8397 ≤ (50960247627017/100000000000000 : ℝ)^6349 := by
    have hnat : (1501677873 : ℕ)^8397*100000000000000^6349 ≤ 50960247627017^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501677873 2500000000 50960247627017 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68529211/500000000 : ℝ)^8397 ≤ (144386632023/2000000000000 : ℝ)^6349 := by
    have hnat : (68529211 : ℕ)^8397*2000000000000^6349 ≤ 144386632023^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68529211 500000000 144386632023 2000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206914289/400000000 : ℝ), (1501677873/2500000000 : ℝ), (-68529211/500000000 : ℝ)] ![(41820420759413/100000000000000 : ℝ), (50960247627017/100000000000000 : ℝ), (144386632023/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206914289/400000000 : ℝ)|^8397 ≤ (41820420759413/100000000000000 : ℝ)^6349
        have hw : |(206914289/400000000 : ℝ)|=(206914289/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1501677873/2500000000 : ℝ)|^8397 ≤ (50960247627017/100000000000000 : ℝ)^6349
        have hw : |(1501677873/2500000000 : ℝ)|=(1501677873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68529211/500000000 : ℝ)|^8397 ≤ (144386632023/2000000000000 : ℝ)^6349
        have hw : |(-68529211/500000000 : ℝ)|=(68529211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s0_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2103010801/5000000000 : ℝ)*x 0 + (5574259327/10000000000 : ℝ)*x 1 + (3185632167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103010801/5000000000 : ℝ)^8397 ≤ (31808526141741/100000000000000 : ℝ)^6349 := by
    have hnat : (2103010801 : ℕ)^8397*100000000000000^6349 ≤ 31808526141741^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103010801 5000000000 31808526141741 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5574259327/10000000000 : ℝ)^8397 ≤ (46165191523213/100000000000000 : ℝ)^6349 := by
    have hnat : (5574259327 : ℕ)^8397*100000000000000^6349 ≤ 46165191523213^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574259327 10000000000 46165191523213 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185632167/10000000000 : ℝ)^8397 ≤ (8810512929/40000000000 : ℝ)^6349 := by
    have hnat : (3185632167 : ℕ)^8397*40000000000^6349 ≤ 8810512929^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185632167 10000000000 8810512929 40000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103010801/5000000000 : ℝ), (5574259327/10000000000 : ℝ), (3185632167/10000000000 : ℝ)] ![(31808526141741/100000000000000 : ℝ), (46165191523213/100000000000000 : ℝ), (8810512929/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103010801/5000000000 : ℝ)|^8397 ≤ (31808526141741/100000000000000 : ℝ)^6349
        have hw : |(2103010801/5000000000 : ℝ)|=(2103010801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5574259327/10000000000 : ℝ)|^8397 ≤ (46165191523213/100000000000000 : ℝ)^6349
        have hw : |(5574259327/10000000000 : ℝ)|=(5574259327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185632167/10000000000 : ℝ)|^8397 ≤ (8810512929/40000000000 : ℝ)^6349
        have hw : |(3185632167/10000000000 : ℝ)|=(3185632167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (333/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27579/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2099/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2099 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2099*1^512 ≤ 0^512*1^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2099/512 : ℝ) ≤ (233669166678025859/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2099 ≤ (233669166678025859/10000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2099*10000000000000000000^512 ≤ 233669166678025859^512*5^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 233669166678025859 10000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (233669166678025859/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2099 := by
      have hnat : (1 : ℕ)^512*1^2099 ≤ 1^2099*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10233669166678025859/10000000000000000000 : ℝ) ≤ (251412529833421/250000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (10233669166678025859/10000000000000000000 : ℝ)^512 ≤ (251412529833421/250000000000000 : ℝ)^2099 := by
      have hnat : (10233669166678025859 : ℕ)^512*250000000000000^2099 ≤ 251412529833421^2099*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10233669166678025859 10000000000000000000 251412529833421 250000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251412529833421/250000000000000 : ℝ)) (X := (10233669166678025859/10000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5233669166678025859/5000000000000000000 : ℝ) ≤ (126412529833421/125000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (5233669166678025859/5000000000000000000 : ℝ)^512 ≤ (126412529833421/125000000000000 : ℝ)^2099 := by
      have hnat : (5233669166678025859 : ℕ)^512*125000000000000^2099 ≤ 126412529833421^2099*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5233669166678025859 5000000000000000000 126412529833421 125000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (126412529833421/125000000000000 : ℝ)) (X := (5233669166678025859/5000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1412529833421/100000000000000 : ℝ)*(0 : ℝ))^(2099/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(1412529833421/100000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(233669166678025859/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1412529833421/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (1 : ℝ)+(1412529833421/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(251412529833421/250000000000000 : ℝ) by norm_num, show 1+(233669166678025859/10000000000000000000 : ℝ)+(0 : ℝ)=(10233669166678025859/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(233669166678025859/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1412529833421/100000000000000 : ℝ)*(2/5 : ℝ))^(2099/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(1412529833421/100000000000000 : ℝ)*(2/5 : ℝ)=(126412529833421/125000000000000 : ℝ) by norm_num, show 1+2*(233669166678025859/10000000000000000000 : ℝ)=(5233669166678025859/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1412529833421/100000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1412529833421/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1412529833421/100000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1412529833421/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1412529833421/100000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1412529833421/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-936170991/5000000000 : ℝ)*X 0 0+(3020055541/5000000000 : ℝ)*X 0 1+(2394131577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513300443/10000000000 : ℝ)*X 1 0+(-1294516469/5000000000 : ℝ)*X 1 1+(239413157/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5513300431/10000000000 : ℝ)*X 2 0+(299266447/625000000 : ℝ)*X 2 1+(-1294516469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((167840897/400000000 : ℝ)*X 0 0+(3118378657/10000000000 : ℝ)*X 0 1+(2819610291/5000000000 : ℝ)*X 0 2+(167840897/400000000 : ℝ)*X 1 0+(3118378657/10000000000 : ℝ)*X 1 1+(2819610291/5000000000 : ℝ)*X 1 2+(167840897/400000000 : ℝ)*X 2 0+(3118378657/10000000000 : ℝ)*X 2 1+(2819610291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1877308097/10000000000 : ℝ)*X 0 0+(4820524551/10000000000 : ℝ)*X 0 1+(3003355493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586428231/5000000000 : ℝ)*X 1 0+(-342645921/2500000000 : ℝ)*X 1 1+(6006712551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((206914289/400000000 : ℝ)*X 2 0+(1501677873/2500000000 : ℝ)*X 2 1+(-68529211/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103010801/5000000000 : ℝ)*X 0 0+(5574259327/10000000000 : ℝ)*X 0 1+(3185632167/10000000000 : ℝ)*X 0 2+(2103010801/5000000000 : ℝ)*X 1 0+(5574259327/10000000000 : ℝ)*X 1 1+(3185632167/10000000000 : ℝ)*X 1 2+(2103010801/5000000000 : ℝ)*X 2 0+(5574259327/10000000000 : ℝ)*X 2 1+(3185632167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5756909753569115616327/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25125923/50000000000000 : ℝ)*(base1) + (1129217601/100000000000000 : ℝ)*(base19) + (1050113559/100000000000000 : ℝ)*(base23) + (38682679/50000000000000 : ℝ)*(base24) + (25854739/10000000000000 : ℝ)*(upper3) + (298880385119143/50000000000000 : ℝ)*(major0) + (298880385119143/50000000000000 : ℝ)*(major1) + (298880385119143/50000000000000 : ℝ)*(major2) + (798822889893591/100000000000000 : ℝ)*(sp0) + (399412105946159/50000000000000 : ℝ)*(sp1) + (399412106815501/50000000000000 : ℝ)*(sp2) + (396694018906917/100000000000000 : ℝ)*(sp3) + (1250734087/50000000000000 : ℝ)*(sp4) + (1976690289/100000000000000 : ℝ)*(sp7) + (99174011462263/25000000000000 : ℝ)*(f.failure) + (399412670554959/50000000000000 : ℝ)*(f.sum) + (8453957879297/2500000000000000000000000000 : ℝ)*base66 + (30626278261797/5000000000000000000000000000 : ℝ)*base68 + (27534459396797/5000000000000000000000000000 : ℝ)*base70 + (34685639606797/5000000000000000000000000000 : ℝ)*base72 + (7310660941797/2500000000000000000000000000 : ℝ)*base74 + (43871224106797/5000000000000000000000000000 : ℝ)*base76 + (18204964546797/5000000000000000000000000000 : ℝ)*base78 + (40073393101797/5000000000000000000000000000 : ℝ)*base80 + (1529841924297/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (765463/78125000000000000000 : ℝ)*base89 + (765463/78125000000000000000 : ℝ)*base91 + (765463/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10061934655165643417997/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (536330699/50000000000000 : ℝ)*(base19) + (1298459281/100000000000000 : ℝ)*(base23) + (5766617/6250000000000 : ℝ)*(base39) + (30151641/12500000000000 : ℝ)*(upper3) + (62083861/100000000000000 : ℝ)*(upper5) + (63084364658813/10000000000000 : ℝ)*(major0) + (63084364658813/10000000000000 : ℝ)*(major1) + (630843554322259/100000000000000 : ℝ)*(major2) + (2618627687/100000000000000 : ℝ)*(sp1) + (1398229167/50000000000000 : ℝ)*(sp2) + (84303600664447/10000000000000 : ℝ)*(sp4) + (105379039419423/12500000000000 : ℝ)*(sp5) + (421516001996363/50000000000000 : ℝ)*(sp6) + (418651060106787/100000000000000 : ℝ)*(sp7) + (418651060106787/100000000000000 : ℝ)*(f.failure) + (843036098910341/100000000000000 : ℝ)*(f.sum) + (12641673529231/10000000000000000000000000000 : ℝ)*base66 + (66071530771961/10000000000000000000000000000 : ℝ)*base68 + (1320975259727/1000000000000000000000000000 : ℝ)*base70 + (818872811961/10000000000000000000000000000 : ℝ)*base72 + (31236714559231/10000000000000000000000000000 : ℝ)*base74 + (519609603727/1000000000000000000000000000 : ℝ)*base76 + (3454710488727/1000000000000000000000000000 : ℝ)*base78 + (4248478719727/1000000000000000000000000000 : ℝ)*base80 + (954224619227/500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3161087/312500000000000000000 : ℝ)*base89 + (3161087/312500000000000000000 : ℝ)*base91 + (36087/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1204_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (333/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27579/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1204_s1_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072516251/10000000000 : ℝ)*x 0 + (1137050577/2000000000 : ℝ)*x 1 + (5014985319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072516251/10000000000 : ℝ)^8397 ≤ (3118604956481/25000000000000 : ℝ)^6349 := by
    have hnat : (2072516251 : ℕ)^8397*25000000000000^6349 ≤ 3118604956481^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072516251 10000000000 3118604956481 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137050577/2000000000 : ℝ)^8397 ≤ (947696557811/2000000000000 : ℝ)^6349 := by
    have hnat : (1137050577 : ℕ)^8397*2000000000000^6349 ≤ 947696557811^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137050577 2000000000 947696557811 2000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5014985319/10000000000 : ℝ)^8397 ≤ (8028150453353/20000000000000 : ℝ)^6349 := by
    have hnat : (5014985319 : ℕ)^8397*20000000000000^6349 ≤ 8028150453353^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014985319 10000000000 8028150453353 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072516251/10000000000 : ℝ), (1137050577/2000000000 : ℝ), (5014985319/10000000000 : ℝ)] ![(3118604956481/25000000000000 : ℝ), (947696557811/2000000000000 : ℝ), (8028150453353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072516251/10000000000 : ℝ)|^8397 ≤ (3118604956481/25000000000000 : ℝ)^6349
        have hw : |(-2072516251/10000000000 : ℝ)|=(2072516251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1137050577/2000000000 : ℝ)|^8397 ≤ (947696557811/2000000000000 : ℝ)^6349
        have hw : |(1137050577/2000000000 : ℝ)|=(1137050577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5014985319/10000000000 : ℝ)|^8397 ≤ (8028150453353/20000000000000 : ℝ)^6349
        have hw : |(5014985319/10000000000 : ℝ)|=(5014985319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s1_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5415726933/10000000000 : ℝ)*x 0 + (-4866211/20000000 : ℝ)*x 1 + (1002997151/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415726933/10000000000 : ℝ)^8397 ≤ (11109187559041/25000000000000 : ℝ)^6349 := by
    have hnat : (5415726933 : ℕ)^8397*25000000000000^6349 ≤ 11109187559041^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415726933 10000000000 11109187559041 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866211/20000000 : ℝ)^8397 ≤ (15422492871841/100000000000000 : ℝ)^6349 := by
    have hnat : (4866211 : ℕ)^8397*100000000000000^6349 ≤ 15422492871841^6349*20000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866211 20000000 15422492871841 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002997151/2000000000 : ℝ)^8397 ≤ (40140756882291/100000000000000 : ℝ)^6349 := by
    have hnat : (1002997151 : ℕ)^8397*100000000000000^6349 ≤ 40140756882291^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002997151 2000000000 40140756882291 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415726933/10000000000 : ℝ), (-4866211/20000000 : ℝ), (1002997151/2000000000 : ℝ)] ![(11109187559041/25000000000000 : ℝ), (15422492871841/100000000000000 : ℝ), (40140756882291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415726933/10000000000 : ℝ)|^8397 ≤ (11109187559041/25000000000000 : ℝ)^6349
        have hw : |(5415726933/10000000000 : ℝ)|=(5415726933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4866211/20000000 : ℝ)|^8397 ≤ (15422492871841/100000000000000 : ℝ)^6349
        have hw : |(-4866211/20000000 : ℝ)|=(4866211/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002997151/2000000000 : ℝ)|^8397 ≤ (40140756882291/100000000000000 : ℝ)^6349
        have hw : |(1002997151/2000000000 : ℝ)|=(1002997151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s1_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083145149/2000000000 : ℝ)*x 0 + (2507493257/5000000000 : ℝ)*x 1 + (-1216553039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083145149/2000000000 : ℝ)^8397 ≤ (888734746883/2000000000000 : ℝ)^6349 := by
    have hnat : (1083145149 : ℕ)^8397*2000000000000^6349 ≤ 888734746883^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083145149 2000000000 888734746883 2000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507493257/5000000000 : ℝ)^8397 ≤ (40140764917117/100000000000000 : ℝ)^6349 := by
    have hnat : (2507493257 : ℕ)^8397*100000000000000^6349 ≤ 40140764917117^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507493257 5000000000 40140764917117 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216553039/5000000000 : ℝ)^8397 ≤ (192781221467/1250000000000 : ℝ)^6349 := by
    have hnat : (1216553039 : ℕ)^8397*1250000000000^6349 ≤ 192781221467^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216553039 5000000000 192781221467 1250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083145149/2000000000 : ℝ), (2507493257/5000000000 : ℝ), (-1216553039/5000000000 : ℝ)] ![(888734746883/2000000000000 : ℝ), (40140764917117/100000000000000 : ℝ), (192781221467/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083145149/2000000000 : ℝ)|^8397 ≤ (888734746883/2000000000000 : ℝ)^6349
        have hw : |(1083145149/2000000000 : ℝ)|=(1083145149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507493257/5000000000 : ℝ)|^8397 ≤ (40140764917117/100000000000000 : ℝ)^6349
        have hw : |(2507493257/5000000000 : ℝ)|=(2507493257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1216553039/5000000000 : ℝ)|^8397 ≤ (192781221467/1250000000000 : ℝ)^6349
        have hw : |(-1216553039/5000000000 : ℝ)|=(1216553039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s1_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312141861/10000000000 : ℝ)*x 0 + (922136537/2500000000 : ℝ)*x 1 + (5038262377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312141861/10000000000 : ℝ)^8397 ≤ (16437122863371/50000000000000 : ℝ)^6349 := by
    have hnat : (4312141861 : ℕ)^8397*50000000000000^6349 ≤ 16437122863371^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312141861 10000000000 16437122863371 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922136537/2500000000 : ℝ)^8397 ≤ (1336920260817/5000000000000 : ℝ)^6349 := by
    have hnat : (922136537 : ℕ)^8397*5000000000000^6349 ≤ 1336920260817^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922136537 2500000000 1336920260817 5000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5038262377/10000000000 : ℝ)^8397 ≤ (20193674525791/50000000000000 : ℝ)^6349 := by
    have hnat : (5038262377 : ℕ)^8397*50000000000000^6349 ≤ 20193674525791^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038262377 10000000000 20193674525791 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312141861/10000000000 : ℝ), (922136537/2500000000 : ℝ), (5038262377/10000000000 : ℝ)] ![(16437122863371/50000000000000 : ℝ), (1336920260817/5000000000000 : ℝ), (20193674525791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312141861/10000000000 : ℝ)|^8397 ≤ (16437122863371/50000000000000 : ℝ)^6349
        have hw : |(4312141861/10000000000 : ℝ)|=(4312141861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922136537/2500000000 : ℝ)|^8397 ≤ (1336920260817/5000000000000 : ℝ)^6349
        have hw : |(922136537/2500000000 : ℝ)|=(922136537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5038262377/10000000000 : ℝ)|^8397 ≤ (20193674525791/50000000000000 : ℝ)^6349
        have hw : |(5038262377/10000000000 : ℝ)|=(5038262377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s1_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073237723/10000000000 : ℝ)*x 0 + (2511960437/5000000000 : ℝ)*x 1 + (5676145823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073237723/10000000000 : ℝ)^8397 ≤ (6240081718999/50000000000000 : ℝ)^6349 := by
    have hnat : (2073237723 : ℕ)^8397*50000000000000^6349 ≤ 6240081718999^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073237723 10000000000 6240081718999 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2511960437/5000000000 : ℝ)^8397 ≤ (10058842957349/25000000000000 : ℝ)^6349 := by
    have hnat : (2511960437 : ℕ)^8397*25000000000000^6349 ≤ 10058842957349^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511960437 5000000000 10058842957349 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5676145823/10000000000 : ℝ)^8397 ≤ (1477639522441/3125000000000 : ℝ)^6349 := by
    have hnat : (5676145823 : ℕ)^8397*3125000000000^6349 ≤ 1477639522441^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676145823 10000000000 1477639522441 3125000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073237723/10000000000 : ℝ), (2511960437/5000000000 : ℝ), (5676145823/10000000000 : ℝ)] ![(6240081718999/50000000000000 : ℝ), (10058842957349/25000000000000 : ℝ), (1477639522441/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073237723/10000000000 : ℝ)|^8397 ≤ (6240081718999/50000000000000 : ℝ)^6349
        have hw : |(-2073237723/10000000000 : ℝ)|=(2073237723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2511960437/5000000000 : ℝ)|^8397 ≤ (10058842957349/25000000000000 : ℝ)^6349
        have hw : |(2511960437/5000000000 : ℝ)|=(2511960437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5676145823/10000000000 : ℝ)|^8397 ≤ (1477639522441/3125000000000 : ℝ)^6349
        have hw : |(5676145823/10000000000 : ℝ)|=(5676145823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s1_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621679091/5000000000 : ℝ)*x 0 + (-13843339/78125000 : ℝ)*x 1 + (709517989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621679091/5000000000 : ℝ)^8397 ≤ (42575899817999/100000000000000 : ℝ)^6349 := by
    have hnat : (2621679091 : ℕ)^8397*100000000000000^6349 ≤ 42575899817999^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621679091 5000000000 42575899817999 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13843339/78125000 : ℝ)^8397 ≤ (1267457062339/12500000000000 : ℝ)^6349 := by
    have hnat : (13843339 : ℕ)^8397*12500000000000^6349 ≤ 1267457062339^6349*78125000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13843339 78125000 1267457062339 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709517989/1250000000 : ℝ)^8397 ≤ (47284443663637/100000000000000 : ℝ)^6349 := by
    have hnat : (709517989 : ℕ)^8397*100000000000000^6349 ≤ 47284443663637^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709517989 1250000000 47284443663637 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621679091/5000000000 : ℝ), (-13843339/78125000 : ℝ), (709517989/1250000000 : ℝ)] ![(42575899817999/100000000000000 : ℝ), (1267457062339/12500000000000 : ℝ), (47284443663637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621679091/5000000000 : ℝ)|^8397 ≤ (42575899817999/100000000000000 : ℝ)^6349
        have hw : |(2621679091/5000000000 : ℝ)|=(2621679091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13843339/78125000 : ℝ)|^8397 ≤ (1267457062339/12500000000000 : ℝ)^6349
        have hw : |(-13843339/78125000 : ℝ)|=(13843339/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709517989/1250000000 : ℝ)|^8397 ≤ (47284443663637/100000000000000 : ℝ)^6349
        have hw : |(709517989/1250000000 : ℝ)|=(709517989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s1_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243358289/10000000000 : ℝ)*x 0 + (1135228881/2000000000 : ℝ)*x 1 + (-1771946523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243358289/10000000000 : ℝ)^8397 ≤ (5321987620887/12500000000000 : ℝ)^6349 := by
    have hnat : (5243358289 : ℕ)^8397*12500000000000^6349 ≤ 5321987620887^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243358289 10000000000 5321987620887 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135228881/2000000000 : ℝ)^8397 ≤ (5910556136909/12500000000000 : ℝ)^6349 := by
    have hnat : (1135228881 : ℕ)^8397*12500000000000^6349 ≤ 5910556136909^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135228881 2000000000 5910556136909 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1771946523/10000000000 : ℝ)^8397 ≤ (10139649921967/100000000000000 : ℝ)^6349 := by
    have hnat : (1771946523 : ℕ)^8397*100000000000000^6349 ≤ 10139649921967^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771946523 10000000000 10139649921967 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243358289/10000000000 : ℝ), (1135228881/2000000000 : ℝ), (-1771946523/10000000000 : ℝ)] ![(5321987620887/12500000000000 : ℝ), (5910556136909/12500000000000 : ℝ), (10139649921967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243358289/10000000000 : ℝ)|^8397 ≤ (5321987620887/12500000000000 : ℝ)^6349
        have hw : |(5243358289/10000000000 : ℝ)|=(5243358289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135228881/2000000000 : ℝ)|^8397 ≤ (5910556136909/12500000000000 : ℝ)^6349
        have hw : |(1135228881/2000000000 : ℝ)|=(1135228881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1771946523/10000000000 : ℝ)|^8397 ≤ (10139649921967/100000000000000 : ℝ)^6349
        have hw : |(-1771946523/10000000000 : ℝ)|=(1771946523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s1_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4313597089/10000000000 : ℝ)*x 0 + (502026737/1000000000 : ℝ)*x 1 + (1853444349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313597089/10000000000 : ℝ)^8397 ≤ (16444459656369/50000000000000 : ℝ)^6349 := by
    have hnat : (4313597089 : ℕ)^8397*50000000000000^6349 ≤ 16444459656369^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313597089 10000000000 16444459656369 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502026737/1000000000 : ℝ)^8397 ≤ (40196677912737/100000000000000 : ℝ)^6349 := by
    have hnat : (502026737 : ℕ)^8397*100000000000000^6349 ≤ 40196677912737^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502026737 1000000000 40196677912737 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1853444349/5000000000 : ℝ)^8397 ≤ (6728600690493/25000000000000 : ℝ)^6349 := by
    have hnat : (1853444349 : ℕ)^8397*25000000000000^6349 ≤ 6728600690493^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853444349 5000000000 6728600690493 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313597089/10000000000 : ℝ), (502026737/1000000000 : ℝ), (1853444349/5000000000 : ℝ)] ![(16444459656369/50000000000000 : ℝ), (40196677912737/100000000000000 : ℝ), (6728600690493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313597089/10000000000 : ℝ)|^8397 ≤ (16444459656369/50000000000000 : ℝ)^6349
        have hw : |(4313597089/10000000000 : ℝ)|=(4313597089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502026737/1000000000 : ℝ)|^8397 ≤ (40196677912737/100000000000000 : ℝ)^6349
        have hw : |(502026737/1000000000 : ℝ)|=(502026737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1853444349/5000000000 : ℝ)|^8397 ≤ (6728600690493/25000000000000 : ℝ)^6349
        have hw : |(1853444349/5000000000 : ℝ)|=(1853444349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (599/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10081/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (333/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (333/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (333/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (333/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (333/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (333/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (333/50000 : ℝ) ^ (2099/512 : ℝ) ≤ (119424806141/100000000000000000000 : ℝ) := by
    have hpowers : (333/50000 : ℝ)^2099 ≤ (119424806141/100000000000000000000 : ℝ)^512 := by
      have hnat : (333 : ℕ)^2099*100000000000000000000^512 ≤ 119424806141^512*50000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        333 50000 119424806141 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (333/50000 : ℝ)) (X := (119424806141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27579/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (254425384304286071/50000000000000000000 : ℝ) := by
    have hpowers : (27579/100000 : ℝ)^2099 ≤ (254425384304286071/50000000000000000000 : ℝ)^512 := by
      have hnat : (27579 : ℕ)^2099*50000000000000000000^512 ≤ 254425384304286071^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27579 100000 254425384304286071 50000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27579/100000 : ℝ)) (X := (254425384304286071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000119424806141/50000000000000000000 : ℝ) ≤ (2500000001456539/2500000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50000000119424806141/50000000000000000000 : ℝ)^512 ≤ (2500000001456539/2500000000000000 : ℝ)^2099 := by
      have hnat : (50000000119424806141 : ℕ)^512*2500000000000000^2099 ≤ 2500000001456539^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000119424806141 50000000000000000000 2500000001456539 2500000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000001456539/2500000000000000 : ℝ)) (X := (50000000119424806141/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100508850888033378283/100000000000000000000 : ℝ) ≤ (10012388374069271/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (100508850888033378283/100000000000000000000 : ℝ)^512 ≤ (10012388374069271/10000000000000000 : ℝ)^2099 := by
      have hnat : (100508850888033378283 : ℕ)^512*10000000000000000^2099 ≤ 10012388374069271^2099*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100508850888033378283 100000000000000000000 10012388374069271 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012388374069271/10000000000000000 : ℝ)) (X := (100508850888033378283/100000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25254425384304286071/25000000000000000000 : ℝ) ≤ (5012388371156193/5000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (25254425384304286071/25000000000000000000 : ℝ)^512 ≤ (5012388371156193/5000000000000000 : ℝ)^2099 := by
      have hnat : (25254425384304286071 : ℕ)^512*5000000000000000^2099 ≤ 5012388371156193^2099*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25254425384304286071 25000000000000000000 5012388371156193 5000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012388371156193/5000000000000000 : ℝ)) (X := (25254425384304286071/25000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(119424806141/100000000000000000000 : ℝ) ≤ ((5606531226047906401/5606875000000000000 : ℝ)+2*(2477673648623/538260000000000 : ℝ)*(333/50000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (5606531226047906401/5606875000000000000 : ℝ)+2*(2477673648623/538260000000000 : ℝ)*(333/50000 : ℝ)=(2500000001456539/2500000000000000 : ℝ) by norm_num, show 1+2*(119424806141/100000000000000000000 : ℝ)=(50000000119424806141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(254425384304286071/50000000000000000000 : ℝ)+(119424806141/100000000000000000000 : ℝ) ≤ ((5606531226047906401/5606875000000000000 : ℝ)+(2477673648623/538260000000000 : ℝ)*((27579/100000 : ℝ)+(333/50000 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (5606531226047906401/5606875000000000000 : ℝ)+(2477673648623/538260000000000 : ℝ)*((27579/100000 : ℝ)+(333/50000 : ℝ))=(10012388374069271/10000000000000000 : ℝ) by norm_num, show 1+(254425384304286071/50000000000000000000 : ℝ)+(119424806141/100000000000000000000 : ℝ)=(100508850888033378283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(254425384304286071/50000000000000000000 : ℝ) ≤ ((5606531226047906401/5606875000000000000 : ℝ)+2*(2477673648623/538260000000000 : ℝ)*(27579/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (5606531226047906401/5606875000000000000 : ℝ)+2*(2477673648623/538260000000000 : ℝ)*(27579/100000 : ℝ)=(5012388371156193/5000000000000000 : ℝ) by norm_num, show 1+2*(254425384304286071/50000000000000000000 : ℝ)=(25254425384304286071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5606531226047906401/5606875000000000000 : ℝ)*(X 1 0+X 2 0)+(2477673648623/538260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (333/50000 : ℝ)) (hi := (27579/100000 : ℝ)) (c := (5606531226047906401/5606875000000000000 : ℝ)) (alpha := (2477673648623/538260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5606531226047906401/5606875000000000000 : ℝ)*(X 0 1+X 2 1)+(2477673648623/538260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (333/50000 : ℝ)) (hi := (27579/100000 : ℝ)) (c := (5606531226047906401/5606875000000000000 : ℝ)) (alpha := (2477673648623/538260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5606531226047906401/5606875000000000000 : ℝ)*(X 0 2+X 1 2)+(2477673648623/538260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (333/50000 : ℝ)) (hi := (27579/100000 : ℝ)) (c := (5606531226047906401/5606875000000000000 : ℝ)) (alpha := (2477673648623/538260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2072516251/10000000000 : ℝ)*X 0 0+(1137050577/2000000000 : ℝ)*X 0 1+(5014985319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415726933/10000000000 : ℝ)*X 1 0+(-4866211/20000000 : ℝ)*X 1 1+(1002997151/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083145149/2000000000 : ℝ)*X 2 0+(2507493257/5000000000 : ℝ)*X 2 1+(-1216553039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312141861/10000000000 : ℝ)*X 0 0+(922136537/2500000000 : ℝ)*X 0 1+(5038262377/10000000000 : ℝ)*X 0 2+(4312141861/10000000000 : ℝ)*X 1 0+(922136537/2500000000 : ℝ)*X 1 1+(5038262377/10000000000 : ℝ)*X 1 2+(4312141861/10000000000 : ℝ)*X 2 0+(922136537/2500000000 : ℝ)*X 2 1+(5038262377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2073237723/10000000000 : ℝ)*X 0 0+(2511960437/5000000000 : ℝ)*X 0 1+(5676145823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2621679091/5000000000 : ℝ)*X 1 0+(-13843339/78125000 : ℝ)*X 1 1+(709517989/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5243358289/10000000000 : ℝ)*X 2 0+(1135228881/2000000000 : ℝ)*X 2 1+(-1771946523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313597089/10000000000 : ℝ)*X 0 0+(502026737/1000000000 : ℝ)*X 0 1+(1853444349/5000000000 : ℝ)*X 0 2+(4313597089/10000000000 : ℝ)*X 1 0+(502026737/1000000000 : ℝ)*X 1 1+(1853444349/5000000000 : ℝ)*X 1 2+(4313597089/10000000000 : ℝ)*X 2 0+(502026737/1000000000 : ℝ)*X 2 1+(1853444349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209457621803408387494082099/140171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9206961/50000000000000 : ℝ)*(base16) + (499651011/100000000000000 : ℝ)*(base19) + (40695267/12500000000000 : ℝ)*(base23) + (14597851/20000000000000 : ℝ)*(upper2) + (136836649/100000000000000 : ℝ)*(upper3) + (558212447168417/50000000000000 : ℝ)*(major0) + (558212447168417/50000000000000 : ℝ)*(major1) + (558212447168417/50000000000000 : ℝ)*(major2) + (1491946550638119/100000000000000 : ℝ)*(sp0) + (745974287192183/50000000000000 : ℝ)*(sp1) + (372987191721791/25000000000000 : ℝ)*(sp2) + (74089845035241/10000000000000 : ℝ)*(sp3) + (127090559/5000000000000 : ℝ)*(sp4) + (2196062243/100000000000000 : ℝ)*(sp7) + (740900646414653/100000000000000 : ℝ)*(f.failure) + (1491949092449299/100000000000000 : ℝ)*(f.sum) + (3336187344109/13456500000000000000000000000 : ℝ)*base65 + (1407826300446949151/841031250000000000000000000000000 : ℝ)*base67 + (4501675765422574151/841031250000000000000000000000000 : ℝ)*base69 + (1627711490179136651/841031250000000000000000000000000 : ℝ)*base71 + (2114882457517/420515625000000000000000000 : ℝ)*base74 + (880001573138917901/841031250000000000000000000000000 : ℝ)*base75 + (680505253068550849/841031250000000000000000000000000 : ℝ)*base78 + (4996972888068457099/841031250000000000000000000000000 : ℝ)*base80 + (35055919602343/13456500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (323647/312500000000000000000 : ℝ)*base90 + (323647/312500000000000000000 : ℝ)*base92 + (323647/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2218616138192178724371052219/280343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101160147/100000000000000 : ℝ)*(base1) + (289423869/20000000000000 : ℝ)*(base19) + (758379401/50000000000000 : ℝ)*(base23) + (202224931/100000000000000 : ℝ)*(base32) + (133943223/100000000000000 : ℝ)*(upper5) + (1147304214909377/100000000000000 : ℝ)*(major0) + (1147304214909377/100000000000000 : ℝ)*(major1) + (1147304214909377/100000000000000 : ℝ)*(major2) + (2081924281/50000000000000 : ℝ)*(sp1) + (5330519919/100000000000000 : ℝ)*(sp2) + (766607483609103/50000000000000 : ℝ)*(sp4) + (191651156886269/12500000000000 : ℝ)*(sp5) + (766604009389669/50000000000000 : ℝ)*(sp6) + (380696498289251/50000000000000 : ℝ)*(sp7) + (38069664998179/5000000000000 : ℝ)*(f.failure) + (1533214866058059/100000000000000 : ℝ)*(f.sum) + (47717597687251/26913000000000000000000000000 : ℝ)*base65 + (3723430289638635281/1682062500000000000000000000000000 : ℝ)*base67 + (1100745397420739719/1682062500000000000000000000000000 : ℝ)*base70 + (1172066115695864719/1682062500000000000000000000000000 : ℝ)*base72 + (43198651574443/26913000000000000000000000000 : ℝ)*base73 + (9367174620545010281/1682062500000000000000000000000000 : ℝ)*base75 + (10040052294332197781/1682062500000000000000000000000000 : ℝ)*base77 + (3932940909791385281/1682062500000000000000000000000000 : ℝ)*base79 + (17960830159651/26913000000000000000000000000 : ℝ)*base81 + (64971/15625000000000000000 : ℝ)*base90 + (64971/15625000000000000000 : ℝ)*base92 + (64971/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1204_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (599/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10081/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1204_s2_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122485043/10000000000 : ℝ)*x 0 + (137485069/250000000 : ℝ)*x 1 + (2584501769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122485043/10000000000 : ℝ)^8397 ≤ (804608479913/6250000000000 : ℝ)^6349 := by
    have hnat : (2122485043 : ℕ)^8397*6250000000000^6349 ≤ 804608479913^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122485043 10000000000 804608479913 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137485069/250000000 : ℝ)^8397 ≤ (22673521949603/50000000000000 : ℝ)^6349 := by
    have hnat : (137485069 : ℕ)^8397*50000000000000^6349 ≤ 22673521949603^6349*250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137485069 250000000 22673521949603 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584501769/5000000000 : ℝ)^8397 ≤ (41779220402723/100000000000000 : ℝ)^6349 := by
    have hnat : (2584501769 : ℕ)^8397*100000000000000^6349 ≤ 41779220402723^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584501769 5000000000 41779220402723 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122485043/10000000000 : ℝ), (137485069/250000000 : ℝ), (2584501769/5000000000 : ℝ)] ![(804608479913/6250000000000 : ℝ), (22673521949603/50000000000000 : ℝ), (41779220402723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122485043/10000000000 : ℝ)|^8397 ≤ (804608479913/6250000000000 : ℝ)^6349
        have hw : |(-2122485043/10000000000 : ℝ)|=(2122485043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137485069/250000000 : ℝ)|^8397 ≤ (22673521949603/50000000000000 : ℝ)^6349
        have hw : |(137485069/250000000 : ℝ)|=(137485069/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584501769/5000000000 : ℝ)|^8397 ≤ (41779220402723/100000000000000 : ℝ)^6349
        have hw : |(2584501769/5000000000 : ℝ)|=(2584501769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s2_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685622361/5000000000 : ℝ)*x 0 + (-35841513/156250000 : ℝ)*x 1 + (5169008149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685622361/5000000000 : ℝ)^8397 ≤ (8790935193417/20000000000000 : ℝ)^6349 := by
    have hnat : (2685622361 : ℕ)^8397*20000000000000^6349 ≤ 8790935193417^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685622361 5000000000 8790935193417 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35841513/156250000 : ℝ)^8397 ≤ (2853210864787/20000000000000 : ℝ)^6349 := by
    have hnat : (35841513 : ℕ)^8397*20000000000000^6349 ≤ 2853210864787^6349*156250000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35841513 156250000 2853210864787 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169008149/10000000000 : ℝ)^8397 ≤ (4177926969371/10000000000000 : ℝ)^6349 := by
    have hnat : (5169008149 : ℕ)^8397*10000000000000^6349 ≤ 4177926969371^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169008149 10000000000 4177926969371 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685622361/5000000000 : ℝ), (-35841513/156250000 : ℝ), (5169008149/10000000000 : ℝ)] ![(8790935193417/20000000000000 : ℝ), (2853210864787/20000000000000 : ℝ), (4177926969371/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685622361/5000000000 : ℝ)|^8397 ≤ (8790935193417/20000000000000 : ℝ)^6349
        have hw : |(2685622361/5000000000 : ℝ)|=(2685622361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35841513/156250000 : ℝ)|^8397 ≤ (2853210864787/20000000000000 : ℝ)^6349
        have hw : |(-35841513/156250000 : ℝ)|=(35841513/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169008149/10000000000 : ℝ)|^8397 ≤ (4177926969371/10000000000000 : ℝ)^6349
        have hw : |(5169008149/10000000000 : ℝ)|=(5169008149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s2_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671405847/1250000000 : ℝ)*x 0 + (51690053/100000000 : ℝ)*x 1 + (-286732229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671405847/1250000000 : ℝ)^8397 ≤ (10988674549399/25000000000000 : ℝ)^6349 := by
    have hnat : (671405847 : ℕ)^8397*25000000000000^6349 ≤ 10988674549399^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671405847 1250000000 10988674549399 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51690053/100000000 : ℝ)^8397 ≤ (41779239238271/100000000000000 : ℝ)^6349 := by
    have hnat : (51690053 : ℕ)^8397*100000000000000^6349 ≤ 41779239238271^6349*100000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51690053 100000000 41779239238271 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286732229/1250000000 : ℝ)^8397 ≤ (14266062549323/100000000000000 : ℝ)^6349 := by
    have hnat : (286732229 : ℕ)^8397*100000000000000^6349 ≤ 14266062549323^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286732229 1250000000 14266062549323 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671405847/1250000000 : ℝ), (51690053/100000000 : ℝ), (-286732229/1250000000 : ℝ)] ![(10988674549399/25000000000000 : ℝ), (41779239238271/100000000000000 : ℝ), (14266062549323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671405847/1250000000 : ℝ)|^8397 ≤ (10988674549399/25000000000000 : ℝ)^6349
        have hw : |(671405847/1250000000 : ℝ)|=(671405847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51690053/100000000 : ℝ)|^8397 ≤ (41779239238271/100000000000000 : ℝ)^6349
        have hw : |(51690053/100000000 : ℝ)|=(51690053/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-286732229/1250000000 : ℝ)|^8397 ≤ (14266062549323/100000000000000 : ℝ)^6349
        have hw : |(-286732229/1250000000 : ℝ)|=(286732229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s2_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217328601/500000000 : ℝ)*x 0 + (4026348991/10000000000 : ℝ)*x 1 + (4691669251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217328601/500000000 : ℝ)^8397 ≤ (2076365295629/6250000000000 : ℝ)^6349 := by
    have hnat : (217328601 : ℕ)^8397*6250000000000^6349 ≤ 2076365295629^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217328601 500000000 2076365295629 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026348991/10000000000 : ℝ)^8397 ≤ (1200957091629/4000000000000 : ℝ)^6349 := by
    have hnat : (4026348991 : ℕ)^8397*4000000000000^6349 ≤ 1200957091629^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026348991 10000000000 1200957091629 4000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4691669251/10000000000 : ℝ)^8397 ≤ (4594278495403/12500000000000 : ℝ)^6349 := by
    have hnat : (4691669251 : ℕ)^8397*12500000000000^6349 ≤ 4594278495403^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4691669251 10000000000 4594278495403 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217328601/500000000 : ℝ), (4026348991/10000000000 : ℝ), (4691669251/10000000000 : ℝ)] ![(2076365295629/6250000000000 : ℝ), (1200957091629/4000000000000 : ℝ), (4594278495403/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217328601/500000000 : ℝ)|^8397 ≤ (2076365295629/6250000000000 : ℝ)^6349
        have hw : |(217328601/500000000 : ℝ)|=(217328601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026348991/10000000000 : ℝ)|^8397 ≤ (1200957091629/4000000000000 : ℝ)^6349
        have hw : |(4026348991/10000000000 : ℝ)|=(4026348991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4691669251/10000000000 : ℝ)|^8397 ≤ (4594278495403/12500000000000 : ℝ)^6349
        have hw : |(4691669251/10000000000 : ℝ)|=(4691669251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s2_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122570587/10000000000 : ℝ)*x 0 + (323199139/625000000 : ℝ)*x 1 + (5497200053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122570587/10000000000 : ℝ)^8397 ≤ (12874421910903/100000000000000 : ℝ)^6349 := by
    have hnat : (2122570587 : ℕ)^8397*100000000000000^6349 ≤ 12874421910903^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122570587 10000000000 12874421910903 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323199139/625000000 : ℝ)^8397 ≤ (41802554616113/100000000000000 : ℝ)^6349 := by
    have hnat : (323199139 : ℕ)^8397*100000000000000^6349 ≤ 41802554616113^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323199139 625000000 41802554616113 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497200053/10000000000 : ℝ)^8397 ≤ (2832688966219/6250000000000 : ℝ)^6349 := by
    have hnat : (5497200053 : ℕ)^8397*6250000000000^6349 ≤ 2832688966219^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497200053 10000000000 2832688966219 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122570587/10000000000 : ℝ), (323199139/625000000 : ℝ), (5497200053/10000000000 : ℝ)] ![(12874421910903/100000000000000 : ℝ), (41802554616113/100000000000000 : ℝ), (2832688966219/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122570587/10000000000 : ℝ)|^8397 ≤ (12874421910903/100000000000000 : ℝ)^6349
        have hw : |(-2122570587/10000000000 : ℝ)|=(2122570587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323199139/625000000 : ℝ)|^8397 ≤ (41802554616113/100000000000000 : ℝ)^6349
        have hw : |(323199139/625000000 : ℝ)|=(323199139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497200053/10000000000 : ℝ)|^8397 ≤ (2832688966219/6250000000000 : ℝ)^6349
        have hw : |(5497200053/10000000000 : ℝ)|=(5497200053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s2_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643537007/5000000000 : ℝ)*x 0 + (-1965663237/10000000000 : ℝ)*x 1 + (5497200077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643537007/5000000000 : ℝ)^8397 ≤ (2690375268689/6250000000000 : ℝ)^6349 := by
    have hnat : (2643537007 : ℕ)^8397*6250000000000^6349 ≤ 2690375268689^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643537007 5000000000 2690375268689 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965663237/10000000000 : ℝ)^8397 ≤ (11630971967637/100000000000000 : ℝ)^6349 := by
    have hnat : (1965663237 : ℕ)^8397*100000000000000^6349 ≤ 11630971967637^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965663237 10000000000 11630971967637 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497200077/10000000000 : ℝ)^8397 ≤ (22661511860603/50000000000000 : ℝ)^6349 := by
    have hnat : (5497200077 : ℕ)^8397*50000000000000^6349 ≤ 22661511860603^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497200077 10000000000 22661511860603 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643537007/5000000000 : ℝ), (-1965663237/10000000000 : ℝ), (5497200077/10000000000 : ℝ)] ![(2690375268689/6250000000000 : ℝ), (11630971967637/100000000000000 : ℝ), (22661511860603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643537007/5000000000 : ℝ)|^8397 ≤ (2690375268689/6250000000000 : ℝ)^6349
        have hw : |(2643537007/5000000000 : ℝ)|=(2643537007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1965663237/10000000000 : ℝ)|^8397 ≤ (11630971967637/100000000000000 : ℝ)^6349
        have hw : |(-1965663237/10000000000 : ℝ)|=(1965663237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497200077/10000000000 : ℝ)|^8397 ≤ (22661511860603/50000000000000 : ℝ)^6349
        have hw : |(5497200077/10000000000 : ℝ)|=(5497200077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s2_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528707419/1000000000 : ℝ)*x 0 + (54972001/100000000 : ℝ)*x 1 + (-1965662963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528707419/1000000000 : ℝ)^8397 ≤ (43046006194197/100000000000000 : ℝ)^6349 := by
    have hnat : (528707419 : ℕ)^8397*100000000000000^6349 ≤ 43046006194197^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528707419 1000000000 43046006194197 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54972001/100000000 : ℝ)^8397 ≤ (11330755993001/25000000000000 : ℝ)^6349 := by
    have hnat : (54972001 : ℕ)^8397*25000000000000^6349 ≤ 11330755993001^6349*100000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54972001 100000000 11330755993001 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965662963/10000000000 : ℝ)^8397 ≤ (11630969823383/100000000000000 : ℝ)^6349 := by
    have hnat : (1965662963 : ℕ)^8397*100000000000000^6349 ≤ 11630969823383^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965662963 10000000000 11630969823383 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528707419/1000000000 : ℝ), (54972001/100000000 : ℝ), (-1965662963/10000000000 : ℝ)] ![(43046006194197/100000000000000 : ℝ), (11330755993001/25000000000000 : ℝ), (11630969823383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528707419/1000000000 : ℝ)|^8397 ≤ (43046006194197/100000000000000 : ℝ)^6349
        have hw : |(528707419/1000000000 : ℝ)|=(528707419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54972001/100000000 : ℝ)|^8397 ≤ (11330755993001/25000000000000 : ℝ)^6349
        have hw : |(54972001/100000000 : ℝ)|=(54972001/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965662963/10000000000 : ℝ)|^8397 ≤ (11630969823383/100000000000000 : ℝ)^6349
        have hw : |(-1965662963/10000000000 : ℝ)|=(1965662963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s2_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086686673/2500000000 : ℝ)*x 0 + (46872767/100000000 : ℝ)*x 1 + (2015391569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086686673/2500000000 : ℝ)^8397 ≤ (33223610449909/100000000000000 : ℝ)^6349 := by
    have hnat : (1086686673 : ℕ)^8397*100000000000000^6349 ≤ 33223610449909^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086686673 2500000000 33223610449909 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46872767/100000000 : ℝ)^8397 ≤ (9177180980793/25000000000000 : ℝ)^6349 := by
    have hnat : (46872767 : ℕ)^8397*25000000000000^6349 ≤ 9177180980793^6349*100000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46872767 100000000 9177180980793 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015391569/5000000000 : ℝ)^8397 ≤ (117451818797/390625000000 : ℝ)^6349 := by
    have hnat : (2015391569 : ℕ)^8397*390625000000^6349 ≤ 117451818797^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015391569 5000000000 117451818797 390625000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086686673/2500000000 : ℝ), (46872767/100000000 : ℝ), (2015391569/5000000000 : ℝ)] ![(33223610449909/100000000000000 : ℝ), (9177180980793/25000000000000 : ℝ), (117451818797/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086686673/2500000000 : ℝ)|^8397 ≤ (33223610449909/100000000000000 : ℝ)^6349
        have hw : |(1086686673/2500000000 : ℝ)|=(1086686673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46872767/100000000 : ℝ)|^8397 ≤ (9177180980793/25000000000000 : ℝ)^6349
        have hw : |(46872767/100000000 : ℝ)|=(46872767/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015391569/5000000000 : ℝ)|^8397 ≤ (117451818797/390625000000 : ℝ)^6349
        have hw : |(2015391569/5000000000 : ℝ)|=(2015391569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10081/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (599/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4671/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (653/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10081/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (599/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10081/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (599/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10081/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (599/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10081/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (599/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10081/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (599/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10081/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (599/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (599/10000 : ℝ) ^ (2099/512 : ℝ) ≤ (972584937751933/100000000000000000000 : ℝ) := by
    have hpowers : (599/10000 : ℝ)^2099 ≤ (972584937751933/100000000000000000000 : ℝ)^512 := by
      have hnat : (599 : ℕ)^2099*100000000000000000000^512 ≤ 972584937751933^512*10000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        599 10000 972584937751933 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (599/10000 : ℝ)) (X := (972584937751933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (10081/50000 : ℝ) ^ (2099/512 : ℝ) ≤ (70441642439676749/50000000000000000000 : ℝ) := by
    have hpowers : (10081/50000 : ℝ)^2099 ≤ (70441642439676749/50000000000000000000 : ℝ)^512 := by
      have hnat : (10081 : ℕ)^2099*50000000000000000000^512 ≤ 70441642439676749^512*50000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10081 50000 70441642439676749 50000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10081/50000 : ℝ)) (X := (70441642439676749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000972584937751933/50000000000000000000 : ℝ) ≤ (625002965458709/625000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50000972584937751933/50000000000000000000 : ℝ)^512 ≤ (625002965458709/625000000000000 : ℝ)^2099 := by
      have hnat : (50000972584937751933 : ℕ)^512*625000000000000^2099 ≤ 625002965458709^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000972584937751933 50000000000000000000 625002965458709 625000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625002965458709/625000000000000 : ℝ)) (X := (50000972584937751933/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100141855869817105431/100000000000000000000 : ℝ) ≤ (200069167497293/200000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (100141855869817105431/100000000000000000000 : ℝ)^512 ≤ (200069167497293/200000000000000 : ℝ)^2099 := by
      have hnat : (100141855869817105431 : ℕ)^512*200000000000000^2099 ≤ 200069167497293^2099*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100141855869817105431 100000000000000000000 200069167497293 200000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200069167497293/200000000000000 : ℝ)) (X := (100141855869817105431/100000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25070441642439676749/25000000000000000000 : ℝ) ≤ (2501717325597489/2500000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (25070441642439676749/25000000000000000000 : ℝ)^512 ≤ (2501717325597489/2500000000000000 : ℝ)^2099 := by
      have hnat : (25070441642439676749 : ℕ)^512*2500000000000000^2099 ≤ 2501717325597489^2099*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25070441642439676749 25000000000000000000 2501717325597489 2500000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501717325597489/2500000000000000 : ℝ)) (X := (25070441642439676749/25000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(972584937751933/100000000000000000000 : ℝ) ≤ ((17709976188992502161/17715000000000000000 : ℝ)+2*(1705463762653/708600000000000 : ℝ)*(599/10000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (17709976188992502161/17715000000000000000 : ℝ)+2*(1705463762653/708600000000000 : ℝ)*(599/10000 : ℝ)=(625002965458709/625000000000000 : ℝ) by norm_num, show 1+2*(972584937751933/100000000000000000000 : ℝ)=(50000972584937751933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70441642439676749/50000000000000000000 : ℝ)+(972584937751933/100000000000000000000 : ℝ) ≤ ((17709976188992502161/17715000000000000000 : ℝ)+(1705463762653/708600000000000 : ℝ)*((10081/50000 : ℝ)+(599/10000 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (17709976188992502161/17715000000000000000 : ℝ)+(1705463762653/708600000000000 : ℝ)*((10081/50000 : ℝ)+(599/10000 : ℝ))=(200069167497293/200000000000000 : ℝ) by norm_num, show 1+(70441642439676749/50000000000000000000 : ℝ)+(972584937751933/100000000000000000000 : ℝ)=(100141855869817105431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70441642439676749/50000000000000000000 : ℝ) ≤ ((17709976188992502161/17715000000000000000 : ℝ)+2*(1705463762653/708600000000000 : ℝ)*(10081/50000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (17709976188992502161/17715000000000000000 : ℝ)+2*(1705463762653/708600000000000 : ℝ)*(10081/50000 : ℝ)=(2501717325597489/2500000000000000 : ℝ) by norm_num, show 1+2*(70441642439676749/50000000000000000000 : ℝ)=(25070441642439676749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17709976188992502161/17715000000000000000 : ℝ)*(X 1 0+X 2 0)+(1705463762653/708600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (599/10000 : ℝ)) (hi := (10081/50000 : ℝ)) (c := (17709976188992502161/17715000000000000000 : ℝ)) (alpha := (1705463762653/708600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17709976188992502161/17715000000000000000 : ℝ)*(X 0 1+X 2 1)+(1705463762653/708600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (599/10000 : ℝ)) (hi := (10081/50000 : ℝ)) (c := (17709976188992502161/17715000000000000000 : ℝ)) (alpha := (1705463762653/708600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17709976188992502161/17715000000000000000 : ℝ)*(X 0 2+X 1 2)+(1705463762653/708600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (599/10000 : ℝ)) (hi := (10081/50000 : ℝ)) (c := (17709976188992502161/17715000000000000000 : ℝ)) (alpha := (1705463762653/708600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2122485043/10000000000 : ℝ)*X 0 0+(137485069/250000000 : ℝ)*X 0 1+(2584501769/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685622361/5000000000 : ℝ)*X 1 0+(-35841513/156250000 : ℝ)*X 1 1+(5169008149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671405847/1250000000 : ℝ)*X 2 0+(51690053/100000000 : ℝ)*X 2 1+(-286732229/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217328601/500000000 : ℝ)*X 0 0+(4026348991/10000000000 : ℝ)*X 0 1+(4691669251/10000000000 : ℝ)*X 0 2+(217328601/500000000 : ℝ)*X 1 0+(4026348991/10000000000 : ℝ)*X 1 1+(4691669251/10000000000 : ℝ)*X 1 2+(217328601/500000000 : ℝ)*X 2 0+(4026348991/10000000000 : ℝ)*X 2 1+(4691669251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2122570587/10000000000 : ℝ)*X 0 0+(323199139/625000000 : ℝ)*X 0 1+(5497200053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643537007/5000000000 : ℝ)*X 1 0+(-1965663237/10000000000 : ℝ)*X 1 1+(5497200077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528707419/1000000000 : ℝ)*X 2 0+(54972001/100000000 : ℝ)*X 2 1+(-1965662963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086686673/2500000000 : ℝ)*X 0 0+(46872767/100000000 : ℝ)*X 0 1+(2015391569/5000000000 : ℝ)*X 0 2+(1086686673/2500000000 : ℝ)*X 1 0+(46872767/100000000 : ℝ)*X 1 1+(2015391569/5000000000 : ℝ)*X 1 2+(1086686673/2500000000 : ℝ)*X 2 0+(46872767/100000000 : ℝ)*X 2 1+(2015391569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57686875231968522000603421/29525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24207431/12500000000000 : ℝ)*(base19) + (79690741/6250000000000 : ℝ)*(base23) + (936099/500000000000 : ℝ)*(upper2) + (120953819/25000000000000 : ℝ)*(upper3) + (114031387/50000000000000 : ℝ)*(upper4) + (452976674886839/20000000000000 : ℝ)*(major0) + (452976674886839/20000000000000 : ℝ)*(major1) + (452976674886839/20000000000000 : ℝ)*(major2) + (1513338045881289/50000000000000 : ℝ)*(sp0) + (1513353265422557/50000000000000 : ℝ)*(sp1) + (1513352724726353/50000000000000 : ℝ)*(sp2) + (375761105963797/25000000000000 : ℝ)*(sp3) + (957273187/3125000000000 : ℝ)*(sp4) + (7767690459/50000000000000 : ℝ)*(sp7) + (751529979618053/50000000000000 : ℝ)*(f.failure) + (1513353362252281/50000000000000 : ℝ)*(f.sum) + (4935925963777/7086000000000000000000000000 : ℝ)*base66 + (229079249679144693/118100000000000000000000000000000 : ℝ)*base67 + (951468442228744693/118100000000000000000000000000000 : ℝ)*base69 + (142602911452855307/118100000000000000000000000000000 : ℝ)*base72 + (6694400196707/7086000000000000000000000000 : ℝ)*base73 + (1210732442781744693/118100000000000000000000000000000 : ℝ)*base75 + (1121659059128344693/118100000000000000000000000000000 : ℝ)*base77 + (974503053596744693/118100000000000000000000000000000 : ℝ)*base79 + (5414754803413/7086000000000000000000000000 : ℝ)*base82 + (297747/156250000000000000000 : ℝ)*base90 + (297747/156250000000000000000 : ℝ)*base92 + (297747/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (959252643927626973124962057/147625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1631105233/100000000000000 : ℝ)*(base19) + (1843576307/100000000000000 : ℝ)*(base23) + (857841/4000000000000 : ℝ)*(upper2) + (26631857/12500000000000 : ℝ)*(upper3) + (13345597/10000000000000 : ℝ)*(upper5) + (1147649675768863/50000000000000 : ℝ)*(major0) + (1147649675768863/50000000000000 : ℝ)*(major1) + (1147649675768863/50000000000000 : ℝ)*(major2) + (16111329919/100000000000000 : ℝ)*(sp1) + (20495250271/100000000000000 : ℝ)*(sp2) + (1533676682735829/50000000000000 : ℝ)*(sp4) + (1533667811518253/50000000000000 : ℝ)*(sp5) + (76683275666127/2500000000000 : ℝ)*(sp6) + (1523245121007087/100000000000000 : ℝ)*(sp7) + (1523245121007087/100000000000000 : ℝ)*(f.failure) + (1533676682735829/50000000000000 : ℝ)*(f.sum) + (38665598072569/17715000000000000000000000000 : ℝ)*base65 + (1058979181354495981/295250000000000000000000000000000 : ℝ)*base67 + (1767022756747495981/295250000000000000000000000000000 : ℝ)*base69 + (1256387313095995981/295250000000000000000000000000000 : ℝ)*base71 + (47526580628989/17715000000000000000000000000 : ℝ)*base73 + (1057906514612254019/295250000000000000000000000000000 : ℝ)*base76 + (3114995247142495981/295250000000000000000000000000000 : ℝ)*base77 + (994161242732504019/295250000000000000000000000000000 : ℝ)*base80 + (28929938312329/17715000000000000000000000000 : ℝ)*base81 + (768613/312500000000000000000 : ℝ)*base90 + (768613/312500000000000000000 : ℝ)*base92 + (768613/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1204_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10081/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (599/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (653/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1204_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (653/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1204_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1204_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1204_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (653/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
