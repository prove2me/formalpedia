-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1268_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:00.633532+00:00
-- url     : https://prove2.me/submissions/354ebc60-c9f4-49df-8fc1-cdf940392b76

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
theorem support_rectangle_w1268_s6_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-421607239/2000000000 : ℝ)*x 0 + (5390876309/10000000000 : ℝ)*x 1 + (2633698389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421607239/2000000000 : ℝ)^8461 ≤ (6411027450873/50000000000000 : ℝ)^6413 := by
    have hnat : (421607239 : ℕ)^8461*50000000000000^6413 ≤ 6411027450873^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421607239 2000000000 6411027450873 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390876309/10000000000 : ℝ)^8461 ≤ (1382975397611/3125000000000 : ℝ)^6413 := by
    have hnat : (5390876309 : ℕ)^8461*3125000000000^6413 ≤ 1382975397611^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390876309 10000000000 1382975397611 3125000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633698389/5000000000 : ℝ)^8461 ≤ (21461366178223/50000000000000 : ℝ)^6413 := by
    have hnat : (2633698389 : ℕ)^8461*50000000000000^6413 ≤ 21461366178223^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633698389 5000000000 21461366178223 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421607239/2000000000 : ℝ), (5390876309/10000000000 : ℝ), (2633698389/5000000000 : ℝ)] ![(6411027450873/50000000000000 : ℝ), (1382975397611/3125000000000 : ℝ), (21461366178223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421607239/2000000000 : ℝ)|^8461 ≤ (6411027450873/50000000000000 : ℝ)^6413
        have hw : |(-421607239/2000000000 : ℝ)|=(421607239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390876309/10000000000 : ℝ)|^8461 ≤ (1382975397611/3125000000000 : ℝ)^6413
        have hw : |(5390876309/10000000000 : ℝ)|=(5390876309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633698389/5000000000 : ℝ)|^8461 ≤ (21461366178223/50000000000000 : ℝ)^6413
        have hw : |(2633698389/5000000000 : ℝ)|=(2633698389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s6_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336052141/2500000000 : ℝ)*x 0 + (-2170639831/10000000000 : ℝ)*x 1 + (5267396771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336052141/2500000000 : ℝ)^8461 ≤ (21875228983871/50000000000000 : ℝ)^6413 := by
    have hnat : (1336052141 : ℕ)^8461*50000000000000^6413 ≤ 21875228983871^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336052141 2500000000 21875228983871 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170639831/10000000000 : ℝ)^8461 ≤ (3331702435099/25000000000000 : ℝ)^6413 := by
    have hnat : (2170639831 : ℕ)^8461*25000000000000^6413 ≤ 3331702435099^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170639831 10000000000 3331702435099 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267396771/10000000000 : ℝ)^8461 ≤ (10730683070297/25000000000000 : ℝ)^6413 := by
    have hnat : (5267396771 : ℕ)^8461*25000000000000^6413 ≤ 10730683070297^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267396771 10000000000 10730683070297 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336052141/2500000000 : ℝ), (-2170639831/10000000000 : ℝ), (5267396771/10000000000 : ℝ)] ![(21875228983871/50000000000000 : ℝ), (3331702435099/25000000000000 : ℝ), (10730683070297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336052141/2500000000 : ℝ)|^8461 ≤ (21875228983871/50000000000000 : ℝ)^6413
        have hw : |(1336052141/2500000000 : ℝ)|=(1336052141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170639831/10000000000 : ℝ)|^8461 ≤ (3331702435099/25000000000000 : ℝ)^6413
        have hw : |(-2170639831/10000000000 : ℝ)|=(2170639831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267396771/10000000000 : ℝ)|^8461 ≤ (10730683070297/25000000000000 : ℝ)^6413
        have hw : |(5267396771/10000000000 : ℝ)|=(5267396771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s6_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534420857/1000000000 : ℝ)*x 0 + (5267396771/10000000000 : ℝ)*x 1 + (-2170639823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534420857/1000000000 : ℝ)^8461 ≤ (10937614508137/25000000000000 : ℝ)^6413 := by
    have hnat : (534420857 : ℕ)^8461*25000000000000^6413 ≤ 10937614508137^6413*1000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534420857 1000000000 10937614508137 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267396771/10000000000 : ℝ)^8461 ≤ (10730683070297/25000000000000 : ℝ)^6413 := by
    have hnat : (5267396771 : ℕ)^8461*25000000000000^6413 ≤ 10730683070297^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267396771 10000000000 10730683070297 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170639823/10000000000 : ℝ)^8461 ≤ (6663404837797/50000000000000 : ℝ)^6413 := by
    have hnat : (2170639823 : ℕ)^8461*50000000000000^6413 ≤ 6663404837797^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170639823 10000000000 6663404837797 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534420857/1000000000 : ℝ), (5267396771/10000000000 : ℝ), (-2170639823/10000000000 : ℝ)] ![(10937614508137/25000000000000 : ℝ), (10730683070297/25000000000000 : ℝ), (6663404837797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534420857/1000000000 : ℝ)|^8461 ≤ (10937614508137/25000000000000 : ℝ)^6413
        have hw : |(534420857/1000000000 : ℝ)|=(534420857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267396771/10000000000 : ℝ)|^8461 ≤ (10730683070297/25000000000000 : ℝ)^6413
        have hw : |(5267396771/10000000000 : ℝ)|=(5267396771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170639823/10000000000 : ℝ)|^8461 ≤ (6663404837797/50000000000000 : ℝ)^6413
        have hw : |(-2170639823/10000000000 : ℝ)|=(2170639823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s6_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (135850359/312500000 : ℝ)*x 0 + (4223100137/10000000000 : ℝ)*x 1 + (4474845213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135850359/312500000 : ℝ)^8461 ≤ (33317537947689/100000000000000 : ℝ)^6413 := by
    have hnat : (135850359 : ℕ)^8461*100000000000000^6413 ≤ 33317537947689^6413*312500000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135850359 312500000 33317537947689 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223100137/10000000000 : ℝ)^8461 ≤ (32068324320831/100000000000000 : ℝ)^6413 := by
    have hnat : (4223100137 : ℕ)^8461*100000000000000^6413 ≤ 32068324320831^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223100137 10000000000 32068324320831 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474845213/10000000000 : ℝ)^8461 ≤ (34614137712699/100000000000000 : ℝ)^6413 := by
    have hnat : (4474845213 : ℕ)^8461*100000000000000^6413 ≤ 34614137712699^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474845213 10000000000 34614137712699 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135850359/312500000 : ℝ), (4223100137/10000000000 : ℝ), (4474845213/10000000000 : ℝ)] ![(33317537947689/100000000000000 : ℝ), (32068324320831/100000000000000 : ℝ), (34614137712699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135850359/312500000 : ℝ)|^8461 ≤ (33317537947689/100000000000000 : ℝ)^6413
        have hw : |(135850359/312500000 : ℝ)|=(135850359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223100137/10000000000 : ℝ)|^8461 ≤ (32068324320831/100000000000000 : ℝ)^6413
        have hw : |(4223100137/10000000000 : ℝ)|=(4223100137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474845213/10000000000 : ℝ)|^8461 ≤ (34614137712699/100000000000000 : ℝ)^6413
        have hw : |(4474845213/10000000000 : ℝ)|=(4474845213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s6_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-210804083/1000000000 : ℝ)*x 0 + (1053541857/2000000000 : ℝ)*x 1 + (5390562667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210804083/1000000000 : ℝ)^8461 ≤ (2564418419441/20000000000000 : ℝ)^6413 := by
    have hnat : (210804083 : ℕ)^8461*20000000000000^6413 ≤ 2564418419441^6413*1000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210804083 1000000000 2564418419441 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053541857/2000000000 : ℝ)^8461 ≤ (42926092173619/100000000000000 : ℝ)^6413 := by
    have hnat : (1053541857 : ℕ)^8461*100000000000000^6413 ≤ 42926092173619^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053541857 2000000000 42926092173619 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390562667/10000000000 : ℝ)^8461 ≤ (44251815722351/100000000000000 : ℝ)^6413 := by
    have hnat : (5390562667 : ℕ)^8461*100000000000000^6413 ≤ 44251815722351^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390562667 10000000000 44251815722351 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210804083/1000000000 : ℝ), (1053541857/2000000000 : ℝ), (5390562667/10000000000 : ℝ)] ![(2564418419441/20000000000000 : ℝ), (42926092173619/100000000000000 : ℝ), (44251815722351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210804083/1000000000 : ℝ)|^8461 ≤ (2564418419441/20000000000000 : ℝ)^6413
        have hw : |(-210804083/1000000000 : ℝ)|=(210804083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053541857/2000000000 : ℝ)|^8461 ≤ (42926092173619/100000000000000 : ℝ)^6413
        have hw : |(1053541857/2000000000 : ℝ)|=(1053541857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390562667/10000000000 : ℝ)|^8461 ≤ (44251815722351/100000000000000 : ℝ)^6413
        have hw : |(5390562667/10000000000 : ℝ)|=(5390562667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s6_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656323729/5000000000 : ℝ)*x 0 + (-2047473931/10000000000 : ℝ)*x 1 + (2695281333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656323729/5000000000 : ℝ)^8461 ≤ (10852472932013/25000000000000 : ℝ)^6413 := by
    have hnat : (2656323729 : ℕ)^8461*25000000000000^6413 ≤ 10852472932013^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656323729 5000000000 10852472932013 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047473931/10000000000 : ℝ)^8461 ≤ (12338292544877/100000000000000 : ℝ)^6413 := by
    have hnat : (2047473931 : ℕ)^8461*100000000000000^6413 ≤ 12338292544877^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047473931 10000000000 12338292544877 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695281333/5000000000 : ℝ)^8461 ≤ (44251815711521/100000000000000 : ℝ)^6413 := by
    have hnat : (2695281333 : ℕ)^8461*100000000000000^6413 ≤ 44251815711521^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695281333 5000000000 44251815711521 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656323729/5000000000 : ℝ), (-2047473931/10000000000 : ℝ), (2695281333/5000000000 : ℝ)] ![(10852472932013/25000000000000 : ℝ), (12338292544877/100000000000000 : ℝ), (44251815711521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656323729/5000000000 : ℝ)|^8461 ≤ (10852472932013/25000000000000 : ℝ)^6413
        have hw : |(2656323729/5000000000 : ℝ)|=(2656323729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047473931/10000000000 : ℝ)|^8461 ≤ (12338292544877/100000000000000 : ℝ)^6413
        have hw : |(-2047473931/10000000000 : ℝ)|=(2047473931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695281333/5000000000 : ℝ)|^8461 ≤ (44251815711521/100000000000000 : ℝ)^6413
        have hw : |(2695281333/5000000000 : ℝ)|=(2695281333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s6_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166020233/312500000 : ℝ)*x 0 + (2695281333/5000000000 : ℝ)*x 1 + (-409494787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166020233/312500000 : ℝ)^8461 ≤ (43409891706491/100000000000000 : ℝ)^6413 := by
    have hnat : (166020233 : ℕ)^8461*100000000000000^6413 ≤ 43409891706491^6413*312500000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166020233 312500000 43409891706491 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695281333/5000000000 : ℝ)^8461 ≤ (44251815711521/100000000000000 : ℝ)^6413 := by
    have hnat : (2695281333 : ℕ)^8461*100000000000000^6413 ≤ 44251815711521^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695281333 5000000000 44251815711521 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409494787/2000000000 : ℝ)^8461 ≤ (12338292576679/100000000000000 : ℝ)^6413 := by
    have hnat : (409494787 : ℕ)^8461*100000000000000^6413 ≤ 12338292576679^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409494787 2000000000 12338292576679 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166020233/312500000 : ℝ), (2695281333/5000000000 : ℝ), (-409494787/2000000000 : ℝ)] ![(43409891706491/100000000000000 : ℝ), (44251815711521/100000000000000 : ℝ), (12338292576679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166020233/312500000 : ℝ)|^8461 ≤ (43409891706491/100000000000000 : ℝ)^6413
        have hw : |(166020233/312500000 : ℝ)|=(166020233/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695281333/5000000000 : ℝ)|^8461 ≤ (44251815711521/100000000000000 : ℝ)^6413
        have hw : |(2695281333/5000000000 : ℝ)|=(2695281333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409494787/2000000000 : ℝ)|^8461 ≤ (12338292576679/100000000000000 : ℝ)^6413
        have hw : |(-409494787/2000000000 : ℝ)|=(409494787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s6_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67925327/156250000 : ℝ)*x 0 + (4474208083/10000000000 : ℝ)*x 1 + (4223739599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67925327/156250000 : ℝ)^8461 ≤ (33317633401821/100000000000000 : ℝ)^6413 := by
    have hnat : (67925327 : ℕ)^8461*100000000000000^6413 ≤ 33317633401821^6413*156250000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67925327 156250000 33317633401821 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474208083/10000000000 : ℝ)^8461 ≤ (6921527121069/20000000000000 : ℝ)^6413 := by
    have hnat : (4474208083 : ℕ)^8461*20000000000000^6413 ≤ 6921527121069^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474208083 10000000000 6921527121069 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223739599/10000000000 : ℝ)^8461 ≤ (32074730964719/100000000000000 : ℝ)^6413 := by
    have hnat : (4223739599 : ℕ)^8461*100000000000000^6413 ≤ 32074730964719^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223739599 10000000000 32074730964719 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67925327/156250000 : ℝ), (4474208083/10000000000 : ℝ), (4223739599/10000000000 : ℝ)] ![(33317633401821/100000000000000 : ℝ), (6921527121069/20000000000000 : ℝ), (32074730964719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67925327/156250000 : ℝ)|^8461 ≤ (33317633401821/100000000000000 : ℝ)^6413
        have hw : |(67925327/156250000 : ℝ)|=(67925327/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474208083/10000000000 : ℝ)|^8461 ≤ (6921527121069/20000000000000 : ℝ)^6413
        have hw : |(4474208083/10000000000 : ℝ)|=(4474208083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223739599/10000000000 : ℝ)|^8461 ≤ (32074730964719/100000000000000 : ℝ)^6413
        have hw : |(4223739599/10000000000 : ℝ)|=(4223739599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5753/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7061/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11487/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (13117338022214387/100000000000000000000 : ℝ) := by
    have hpowers : (11487/100000 : ℝ)^2115 ≤ (13117338022214387/100000000000000000000 : ℝ)^512 := by
      have hnat : (11487 : ℕ)^2115*100000000000000000000^512 ≤ 13117338022214387^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11487 100000 13117338022214387 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11487/100000 : ℝ)) (X := (13117338022214387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14141/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (3095657100879961/10000000000000000000 : ℝ) := by
    have hpowers : (14141/100000 : ℝ)^2115 ≤ (3095657100879961/10000000000000000000 : ℝ)^512 := by
      have hnat : (14141 : ℕ)^2115*10000000000000000000^512 ≤ 3095657100879961^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14141 100000 3095657100879961 10000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14141/100000 : ℝ)) (X := (3095657100879961/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013117338022214387/50000000000000000000 : ℝ) ≤ (5000317513449889/5000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50013117338022214387/50000000000000000000 : ℝ)^512 ≤ (5000317513449889/5000000000000000 : ℝ)^2115 := by
      have hnat : (50013117338022214387 : ℕ)^512*5000000000000000^2115 ≤ 5000317513449889^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013117338022214387 50000000000000000000 5000317513449889 5000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000317513449889/5000000000000000 : ℝ)) (X := (50013117338022214387/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044073909031013997/100000000000000000000 : ℝ) ≤ (10001066764699571/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (100044073909031013997/100000000000000000000 : ℝ)^512 ≤ (10001066764699571/10000000000000000 : ℝ)^2115 := by
      have hnat : (100044073909031013997 : ℕ)^512*10000000000000000^2115 ≤ 10001066764699571^2115*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044073909031013997 100000000000000000000 10001066764699571 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001066764699571/10000000000000000 : ℝ)) (X := (100044073909031013997/100000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003095657100879961/5000000000000000000 : ℝ) ≤ (2500374625624841/2500000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (5003095657100879961/5000000000000000000 : ℝ)^512 ≤ (2500374625624841/2500000000000000 : ℝ)^2115 := by
      have hnat : (5003095657100879961 : ℕ)^512*2500000000000000^2115 ≤ 2500374625624841^2115*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003095657100879961 5000000000000000000 2500374625624841 2500000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500374625624841/2500000000000000 : ℝ)) (X := (5003095657100879961/5000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13117338022214387/100000000000000000000 : ℝ) ≤ ((2653176661717956643/2654000000000000000 : ℝ)+2*(431737799793/265400000000000 : ℝ)*(11487/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (2653176661717956643/2654000000000000000 : ℝ)+2*(431737799793/265400000000000 : ℝ)*(11487/100000 : ℝ)=(5000317513449889/5000000000000000 : ℝ) by norm_num, show 1+2*(13117338022214387/100000000000000000000 : ℝ)=(50013117338022214387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3095657100879961/10000000000000000000 : ℝ)+(13117338022214387/100000000000000000000 : ℝ) ≤ ((2653176661717956643/2654000000000000000 : ℝ)+(431737799793/265400000000000 : ℝ)*((14141/100000 : ℝ)+(11487/100000 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (2653176661717956643/2654000000000000000 : ℝ)+(431737799793/265400000000000 : ℝ)*((14141/100000 : ℝ)+(11487/100000 : ℝ))=(10001066764699571/10000000000000000 : ℝ) by norm_num, show 1+(3095657100879961/10000000000000000000 : ℝ)+(13117338022214387/100000000000000000000 : ℝ)=(100044073909031013997/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3095657100879961/10000000000000000000 : ℝ) ≤ ((2653176661717956643/2654000000000000000 : ℝ)+2*(431737799793/265400000000000 : ℝ)*(14141/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (2653176661717956643/2654000000000000000 : ℝ)+2*(431737799793/265400000000000 : ℝ)*(14141/100000 : ℝ)=(2500374625624841/2500000000000000 : ℝ) by norm_num, show 1+2*(3095657100879961/10000000000000000000 : ℝ)=(5003095657100879961/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2653176661717956643/2654000000000000000 : ℝ)*(X 1 0+X 2 0)+(431737799793/265400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (14141/100000 : ℝ)) (c := (2653176661717956643/2654000000000000000 : ℝ)) (alpha := (431737799793/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2653176661717956643/2654000000000000000 : ℝ)*(X 0 1+X 2 1)+(431737799793/265400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (14141/100000 : ℝ)) (c := (2653176661717956643/2654000000000000000 : ℝ)) (alpha := (431737799793/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2653176661717956643/2654000000000000000 : ℝ)*(X 0 2+X 1 2)+(431737799793/265400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (14141/100000 : ℝ)) (c := (2653176661717956643/2654000000000000000 : ℝ)) (alpha := (431737799793/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421607239/2000000000 : ℝ)*X 0 0+(5390876309/10000000000 : ℝ)*X 0 1+(2633698389/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336052141/2500000000 : ℝ)*X 1 0+(-2170639831/10000000000 : ℝ)*X 1 1+(5267396771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534420857/1000000000 : ℝ)*X 2 0+(5267396771/10000000000 : ℝ)*X 2 1+(-2170639823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135850359/312500000 : ℝ)*X 0 0+(4223100137/10000000000 : ℝ)*X 0 1+(4474845213/10000000000 : ℝ)*X 0 2+(135850359/312500000 : ℝ)*X 1 0+(4223100137/10000000000 : ℝ)*X 1 1+(4474845213/10000000000 : ℝ)*X 1 2+(135850359/312500000 : ℝ)*X 2 0+(4223100137/10000000000 : ℝ)*X 2 1+(4474845213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210804083/1000000000 : ℝ)*X 0 0+(1053541857/2000000000 : ℝ)*X 0 1+(5390562667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656323729/5000000000 : ℝ)*X 1 0+(-2047473931/10000000000 : ℝ)*X 1 1+(2695281333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166020233/312500000 : ℝ)*X 2 0+(2695281333/5000000000 : ℝ)*X 2 1+(-409494787/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((67925327/156250000 : ℝ)*X 0 0+(4474208083/10000000000 : ℝ)*X 0 1+(4223739599/10000000000 : ℝ)*X 0 2+(67925327/156250000 : ℝ)*X 1 0+(4474208083/10000000000 : ℝ)*X 1 1+(4223739599/10000000000 : ℝ)*X 1 2+(67925327/156250000 : ℝ)*X 2 0+(4474208083/10000000000 : ℝ)*X 2 1+(4223739599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (611397408193531875482009889/132700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (903434307/100000000000000 : ℝ)*(base19) + (423065679/50000000000000 : ℝ)*(base23) + (17741513/50000000000000 : ℝ)*(lower2) + (57059187/50000000000000 : ℝ)*(upper3) + (40169381/50000000000000 : ℝ)*(upper5) + (6035428105706759/100000000000000 : ℝ)*(major0) + (6035428105706759/100000000000000 : ℝ)*(major1) + (6035428105706759/100000000000000 : ℝ)*(major2) + (8098533646984797/100000000000000 : ℝ)*(sp0) + (1012319716497831/12500000000000 : ℝ)*(sp1) + (2024639447321399/25000000000000 : ℝ)*(sp2) + (993071072787017/25000000000000 : ℝ)*(sp3) + (12494216079/50000000000000 : ℝ)*(sp4) + (3282817409/25000000000000 : ℝ)*(sp7) + (496537177802213/12500000000000 : ℝ)*(f.failure) + (4049279317708477/50000000000000 : ℝ)*(f.sum) + (35927361633897/13270000000000000000000000000 : ℝ)*base65 + (17620641774879963/265400000000000000000000000000000 : ℝ)*base68 + (1485889070782920037/265400000000000000000000000000000 : ℝ)*base69 + (3014433574937320037/265400000000000000000000000000000 : ℝ)*base71 + (14123533726567/13270000000000000000000000000 : ℝ)*base73 + (263999330619479963/265400000000000000000000000000000 : ℝ)*base76 + (5089925205118120037/265400000000000000000000000000000 : ℝ)*base77 + (235159797094920037/265400000000000000000000000000000 : ℝ)*base79 + (30929665947087/13270000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4970177/1250000000000000000000 : ℝ)*base90 + (4970177/1250000000000000000000 : ℝ)*base92 + (4970177/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34120015046743755897464169/4146875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1465718277/100000000000000 : ℝ)*(base19) + (317211969/20000000000000 : ℝ)*(base23) + (10256793/6250000000000 : ℝ)*(upper3) + (57086039/100000000000000 : ℝ)*(lower4) + (168941519/100000000000000 : ℝ)*(upper5) + (189567195577189/3125000000000 : ℝ)*(major0) + (189567195577189/3125000000000 : ℝ)*(major1) + (189567195577189/3125000000000 : ℝ)*(major2) + (41463669027/100000000000000 : ℝ)*(sp1) + (44148972359/100000000000000 : ℝ)*(sp2) + (4069891313041753/50000000000000 : ℝ)*(sp4) + (4069869848348101/50000000000000 : ℝ)*(sp5) + (4069868445525651/50000000000000 : ℝ)*(sp6) + (1996258808296857/50000000000000 : ℝ)*(sp7) + (1996258808296857/50000000000000 : ℝ)*(f.failure) + (4069891313041753/50000000000000 : ℝ)*(f.sum) + (8308924867647/1658750000000000000000000000 : ℝ)*base66 + (22025654359686527/8293750000000000000000000000000 : ℝ)*base67 + (55041350365111527/8293750000000000000000000000000 : ℝ)*base69 + (52087335981113473/8293750000000000000000000000000 : ℝ)*base72 + (35494048787473/6635000000000000000000000000 : ℝ)*base74 + (230788933059055277/8293750000000000000000000000000 : ℝ)*base75 + (42866366278275973/8293750000000000000000000000000 : ℝ)*base78 + (46283291400330277/8293750000000000000000000000000 : ℝ)*base79 + (12105336039433/6635000000000000000000000000 : ℝ)*base82 + (18257147/5000000000000000000000 : ℝ)*base89 + (18257147/5000000000000000000000 : ℝ)*base91 + (18257147/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1268_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5753/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1268_s7_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108049121/10000000000 : ℝ)*x 0 + (5390702123/10000000000 : ℝ)*x 1 + (329222663/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108049121/10000000000 : ℝ)^8461 ≤ (64110793159/500000000000 : ℝ)^6413 := by
    have hnat : (2108049121 : ℕ)^8461*500000000000^6413 ≤ 64110793159^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108049121 10000000000 64110793159 500000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390702123/10000000000 : ℝ)^8461 ≤ (22126663068953/50000000000000 : ℝ)^6413 := by
    have hnat : (5390702123 : ℕ)^8461*50000000000000^6413 ≤ 22126663068953^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390702123 10000000000 22126663068953 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329222663/625000000 : ℝ)^8461 ≤ (1716980608629/4000000000000 : ℝ)^6413 := by
    have hnat : (329222663 : ℕ)^8461*4000000000000^6413 ≤ 1716980608629^6413*625000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329222663 625000000 1716980608629 4000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108049121/10000000000 : ℝ), (5390702123/10000000000 : ℝ), (329222663/625000000 : ℝ)] ![(64110793159/500000000000 : ℝ), (22126663068953/50000000000000 : ℝ), (1716980608629/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108049121/10000000000 : ℝ)|^8461 ≤ (64110793159/500000000000 : ℝ)^6413
        have hw : |(-2108049121/10000000000 : ℝ)|=(2108049121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390702123/10000000000 : ℝ)|^8461 ≤ (22126663068953/50000000000000 : ℝ)^6413
        have hw : |(5390702123/10000000000 : ℝ)|=(5390702123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329222663/625000000 : ℝ)|^8461 ≤ (1716980608629/4000000000000 : ℝ)^6413
        have hw : |(329222663/625000000 : ℝ)|=(329222663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s7_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336041237/2500000000 : ℝ)*x 0 + (-271309759/1250000000 : ℝ)*x 1 + (2633781231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336041237/2500000000 : ℝ)^8461 ≤ (43749986876611/100000000000000 : ℝ)^6413 := by
    have hnat : (1336041237 : ℕ)^8461*100000000000000^6413 ≤ 43749986876611^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336041237 2500000000 43749986876611 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271309759/1250000000 : ℝ)^8461 ≤ (6662749733127/50000000000000 : ℝ)^6413 := by
    have hnat : (271309759 : ℕ)^8461*50000000000000^6413 ≤ 6662749733127^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271309759 1250000000 6662749733127 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633781231/5000000000 : ℝ)^8461 ≤ (10731128411513/25000000000000 : ℝ)^6413 := by
    have hnat : (2633781231 : ℕ)^8461*25000000000000^6413 ≤ 10731128411513^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633781231 5000000000 10731128411513 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336041237/2500000000 : ℝ), (-271309759/1250000000 : ℝ), (2633781231/5000000000 : ℝ)] ![(43749986876611/100000000000000 : ℝ), (6662749733127/50000000000000 : ℝ), (10731128411513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336041237/2500000000 : ℝ)|^8461 ≤ (43749986876611/100000000000000 : ℝ)^6413
        have hw : |(1336041237/2500000000 : ℝ)|=(1336041237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271309759/1250000000 : ℝ)|^8461 ≤ (6662749733127/50000000000000 : ℝ)^6413
        have hw : |(-271309759/1250000000 : ℝ)|=(271309759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633781231/5000000000 : ℝ)|^8461 ≤ (10731128411513/25000000000000 : ℝ)^6413
        have hw : |(2633781231/5000000000 : ℝ)|=(2633781231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s7_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106883303/200000000 : ℝ)*x 0 + (1053512453/2000000000 : ℝ)*x 1 + (-434095613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106883303/200000000 : ℝ)^8461 ≤ (21874994529193/50000000000000 : ℝ)^6413 := by
    have hnat : (106883303 : ℕ)^8461*50000000000000^6413 ≤ 21874994529193^6413*200000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106883303 200000000 21874994529193 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053512453/2000000000 : ℝ)^8461 ≤ (4292451152807/10000000000000 : ℝ)^6413 := by
    have hnat : (1053512453 : ℕ)^8461*10000000000000^6413 ≤ 4292451152807^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053512453 2000000000 4292451152807 10000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434095613/2000000000 : ℝ)^8461 ≤ (6662749704777/50000000000000 : ℝ)^6413 := by
    have hnat : (434095613 : ℕ)^8461*50000000000000^6413 ≤ 6662749704777^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434095613 2000000000 6662749704777 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106883303/200000000 : ℝ), (1053512453/2000000000 : ℝ), (-434095613/2000000000 : ℝ)] ![(21874994529193/50000000000000 : ℝ), (4292451152807/10000000000000 : ℝ), (6662749704777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106883303/200000000 : ℝ)|^8461 ≤ (21874994529193/50000000000000 : ℝ)^6413
        have hw : |(106883303/200000000 : ℝ)|=(106883303/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053512453/2000000000 : ℝ)|^8461 ≤ (4292451152807/10000000000000 : ℝ)^6413
        have hw : |(1053512453/2000000000 : ℝ)|=(1053512453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434095613/2000000000 : ℝ)|^8461 ≤ (6662749704777/50000000000000 : ℝ)^6413
        have hw : |(-434095613/2000000000 : ℝ)|=(434095613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s7_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543402429/1250000000 : ℝ)*x 0 + (2111723137/5000000000 : ℝ)*x 1 + (4474497539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543402429/1250000000 : ℝ)^8461 ≤ (8329404568691/25000000000000 : ℝ)^6413 := by
    have hnat : (543402429 : ℕ)^8461*25000000000000^6413 ≤ 8329404568691^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543402429 1250000000 8329404568691 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111723137/5000000000 : ℝ)^8461 ≤ (501121752513/1562500000000 : ℝ)^6413 := by
    have hnat : (2111723137 : ℕ)^8461*1562500000000^6413 ≤ 501121752513^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111723137 5000000000 501121752513 1562500000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474497539/10000000000 : ℝ)^8461 ≤ (17305294778043/50000000000000 : ℝ)^6413 := by
    have hnat : (4474497539 : ℕ)^8461*50000000000000^6413 ≤ 17305294778043^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474497539 10000000000 17305294778043 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543402429/1250000000 : ℝ), (2111723137/5000000000 : ℝ), (4474497539/10000000000 : ℝ)] ![(8329404568691/25000000000000 : ℝ), (501121752513/1562500000000 : ℝ), (17305294778043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543402429/1250000000 : ℝ)|^8461 ≤ (8329404568691/25000000000000 : ℝ)^6413
        have hw : |(543402429/1250000000 : ℝ)|=(543402429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111723137/5000000000 : ℝ)|^8461 ≤ (501121752513/1562500000000 : ℝ)^6413
        have hw : |(2111723137/5000000000 : ℝ)|=(2111723137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474497539/10000000000 : ℝ)|^8461 ≤ (17305294778043/50000000000000 : ℝ)^6413
        have hw : |(4474497539/10000000000 : ℝ)|=(4474497539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s7_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108053373/10000000000 : ℝ)*x 0 + (2633936413/5000000000 : ℝ)*x 1 + (5390391029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108053373/10000000000 : ℝ)^8461 ≤ (12822192753783/100000000000000 : ℝ)^6413 := by
    have hnat : (2108053373 : ℕ)^8461*100000000000000^6413 ≤ 12822192753783^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108053373 10000000000 12822192753783 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633936413/5000000000 : ℝ)^8461 ≤ (42927850456759/100000000000000 : ℝ)^6413 := by
    have hnat : (2633936413 : ℕ)^8461*100000000000000^6413 ≤ 42927850456759^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633936413 5000000000 42927850456759 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390391029/10000000000 : ℝ)^8461 ≤ (22124978384079/50000000000000 : ℝ)^6413 := by
    have hnat : (5390391029 : ℕ)^8461*50000000000000^6413 ≤ 22124978384079^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390391029 10000000000 22124978384079 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108053373/10000000000 : ℝ), (2633936413/5000000000 : ℝ), (5390391029/10000000000 : ℝ)] ![(12822192753783/100000000000000 : ℝ), (42927850456759/100000000000000 : ℝ), (22124978384079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108053373/10000000000 : ℝ)|^8461 ≤ (12822192753783/100000000000000 : ℝ)^6413
        have hw : |(-2108053373/10000000000 : ℝ)|=(2108053373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633936413/5000000000 : ℝ)|^8461 ≤ (42927850456759/100000000000000 : ℝ)^6413
        have hw : |(2633936413/5000000000 : ℝ)|=(2633936413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390391029/10000000000 : ℝ)|^8461 ≤ (22124978384079/50000000000000 : ℝ)^6413
        have hw : |(5390391029/10000000000 : ℝ)|=(5390391029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s7_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312690907/10000000000 : ℝ)*x 0 + (-2047649417/10000000000 : ℝ)*x 1 + (1347597649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312690907/10000000000 : ℝ)^8461 ≤ (21705180064903/50000000000000 : ℝ)^6413 := by
    have hnat : (5312690907 : ℕ)^8461*50000000000000^6413 ≤ 21705180064903^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312690907 10000000000 21705180064903 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047649417/10000000000 : ℝ)^8461 ≤ (6169843887037/50000000000000 : ℝ)^6413 := by
    have hnat : (2047649417 : ℕ)^8461*50000000000000^6413 ≤ 6169843887037^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047649417 10000000000 6169843887037 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347597649/2500000000 : ℝ)^8461 ≤ (44249952078503/100000000000000 : ℝ)^6413 := by
    have hnat : (1347597649 : ℕ)^8461*100000000000000^6413 ≤ 44249952078503^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347597649 2500000000 44249952078503 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312690907/10000000000 : ℝ), (-2047649417/10000000000 : ℝ), (1347597649/2500000000 : ℝ)] ![(21705180064903/50000000000000 : ℝ), (6169843887037/50000000000000 : ℝ), (44249952078503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312690907/10000000000 : ℝ)|^8461 ≤ (21705180064903/50000000000000 : ℝ)^6413
        have hw : |(5312690907/10000000000 : ℝ)|=(5312690907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047649417/10000000000 : ℝ)|^8461 ≤ (6169843887037/50000000000000 : ℝ)^6413
        have hw : |(-2047649417/10000000000 : ℝ)|=(2047649417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347597649/2500000000 : ℝ)|^8461 ≤ (44249952078503/100000000000000 : ℝ)^6413
        have hw : |(1347597649/2500000000 : ℝ)|=(1347597649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s7_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328172791/2500000000 : ℝ)*x 0 + (2695195041/5000000000 : ℝ)*x 1 + (-2047649769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328172791/2500000000 : ℝ)^8461 ≤ (43410362900397/100000000000000 : ℝ)^6413 := by
    have hnat : (1328172791 : ℕ)^8461*100000000000000^6413 ≤ 43410362900397^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328172791 2500000000 43410362900397 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695195041/5000000000 : ℝ)^8461 ≤ (2765621656973/6250000000000 : ℝ)^6413 := by
    have hnat : (2695195041 : ℕ)^8461*6250000000000^6413 ≤ 2765621656973^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695195041 5000000000 2765621656973 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047649769/10000000000 : ℝ)^8461 ≤ (1542461321593/12500000000000 : ℝ)^6413 := by
    have hnat : (2047649769 : ℕ)^8461*12500000000000^6413 ≤ 1542461321593^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047649769 10000000000 1542461321593 12500000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328172791/2500000000 : ℝ), (2695195041/5000000000 : ℝ), (-2047649769/10000000000 : ℝ)] ![(43410362900397/100000000000000 : ℝ), (2765621656973/6250000000000 : ℝ), (1542461321593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328172791/2500000000 : ℝ)|^8461 ≤ (43410362900397/100000000000000 : ℝ)^6413
        have hw : |(1328172791/2500000000 : ℝ)|=(1328172791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695195041/5000000000 : ℝ)|^8461 ≤ (2765621656973/6250000000000 : ℝ)^6413
        have hw : |(2695195041/5000000000 : ℝ)|=(2695195041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2047649769/10000000000 : ℝ)|^8461 ≤ (1542461321593/12500000000000 : ℝ)^6413
        have hw : |(-2047649769/10000000000 : ℝ)|=(2047649769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s7_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347229571/10000000000 : ℝ)*x 0 + (89477279/200000000 : ℝ)*x 1 + (264005087/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347229571/10000000000 : ℝ)^8461 ≤ (33317720797013/100000000000000 : ℝ)^6413 := by
    have hnat : (4347229571 : ℕ)^8461*100000000000000^6413 ≤ 33317720797013^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347229571 10000000000 33317720797013 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89477279/200000000 : ℝ)^8461 ≤ (34604123745357/100000000000000 : ℝ)^6413 := by
    have hnat : (89477279 : ℕ)^8461*100000000000000^6413 ≤ 34604123745357^6413*200000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89477279 200000000 34604123745357 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264005087/625000000 : ℝ)^8461 ≤ (32078155448531/100000000000000 : ℝ)^6413 := by
    have hnat : (264005087 : ℕ)^8461*100000000000000^6413 ≤ 32078155448531^6413*625000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264005087 625000000 32078155448531 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347229571/10000000000 : ℝ), (89477279/200000000 : ℝ), (264005087/625000000 : ℝ)] ![(33317720797013/100000000000000 : ℝ), (34604123745357/100000000000000 : ℝ), (32078155448531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347229571/10000000000 : ℝ)|^8461 ≤ (33317720797013/100000000000000 : ℝ)^6413
        have hw : |(4347229571/10000000000 : ℝ)|=(4347229571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89477279/200000000 : ℝ)|^8461 ≤ (34604123745357/100000000000000 : ℝ)^6413
        have hw : |(89477279/200000000 : ℝ)|=(89477279/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264005087/625000000 : ℝ)|^8461 ≤ (32078155448531/100000000000000 : ℝ)^6413
        have hw : |(264005087/625000000 : ℝ)|=(264005087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5753/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11509/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7059/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5753/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5753/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5753/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5753/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5753/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5753/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5753/50000 : ℝ) ^ (2115/512 : ℝ) ≤ (2641439234714761/20000000000000000000 : ℝ) := by
    have hpowers : (5753/50000 : ℝ)^2115 ≤ (2641439234714761/20000000000000000000 : ℝ)^512 := by
      have hnat : (5753 : ℕ)^2115*20000000000000000000^512 ≤ 2641439234714761^512*50000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5753 50000 2641439234714761 20000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5753/50000 : ℝ)) (X := (2641439234714761/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7061/50000 : ℝ) ^ (2115/512 : ℝ) ≤ (6157022962431661/20000000000000000000 : ℝ) := by
    have hpowers : (7061/50000 : ℝ)^2115 ≤ (6157022962431661/20000000000000000000 : ℝ)^512 := by
      have hnat : (7061 : ℕ)^2115*20000000000000000000^512 ≤ 6157022962431661^512*50000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7061 50000 6157022962431661 20000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7061/50000 : ℝ)) (X := (6157022962431661/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002641439234714761/10000000000000000000 : ℝ) ≤ (10000639376611011/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (10002641439234714761/10000000000000000000 : ℝ)^512 ≤ (10000639376611011/10000000000000000 : ℝ)^2115 := by
      have hnat : (10002641439234714761 : ℕ)^512*10000000000000000^2115 ≤ 10000639376611011^2115*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002641439234714761 10000000000000000000 10000639376611011 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000639376611011/10000000000000000 : ℝ)) (X := (10002641439234714761/10000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004399231098573211/10000000000000000000 : ℝ) ≤ (10001064790029987/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (10004399231098573211/10000000000000000000 : ℝ)^512 ≤ (10001064790029987/10000000000000000 : ℝ)^2115 := by
      have hnat : (10004399231098573211 : ℕ)^512*10000000000000000^2115 ≤ 10001064790029987^2115*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004399231098573211 10000000000000000000 10001064790029987 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001064790029987/10000000000000000 : ℝ)) (X := (10004399231098573211/10000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006157022962431661/10000000000000000000 : ℝ) ≤ (10001490203448963/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (10006157022962431661/10000000000000000000 : ℝ)^512 ≤ (10001490203448963/10000000000000000 : ℝ)^2115 := by
      have hnat : (10006157022962431661 : ℕ)^512*10000000000000000^2115 ≤ 10001490203448963^2115*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006157022962431661 10000000000000000000 10001490203448963 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001490203448963/10000000000000000 : ℝ)) (X := (10006157022962431661/10000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2641439234714761/20000000000000000000 : ℝ) ≤ ((1089661791484038711/1090000000000000000 : ℝ)+2*(4431389781/2725000000000 : ℝ)*(5753/50000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (1089661791484038711/1090000000000000000 : ℝ)+2*(4431389781/2725000000000 : ℝ)*(5753/50000 : ℝ)=(10000639376611011/10000000000000000 : ℝ) by norm_num, show 1+2*(2641439234714761/20000000000000000000 : ℝ)=(10002641439234714761/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6157022962431661/20000000000000000000 : ℝ)+(2641439234714761/20000000000000000000 : ℝ) ≤ ((1089661791484038711/1090000000000000000 : ℝ)+(4431389781/2725000000000 : ℝ)*((7061/50000 : ℝ)+(5753/50000 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (1089661791484038711/1090000000000000000 : ℝ)+(4431389781/2725000000000 : ℝ)*((7061/50000 : ℝ)+(5753/50000 : ℝ))=(10001064790029987/10000000000000000 : ℝ) by norm_num, show 1+(6157022962431661/20000000000000000000 : ℝ)+(2641439234714761/20000000000000000000 : ℝ)=(10004399231098573211/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6157022962431661/20000000000000000000 : ℝ) ≤ ((1089661791484038711/1090000000000000000 : ℝ)+2*(4431389781/2725000000000 : ℝ)*(7061/50000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (1089661791484038711/1090000000000000000 : ℝ)+2*(4431389781/2725000000000 : ℝ)*(7061/50000 : ℝ)=(10001490203448963/10000000000000000 : ℝ) by norm_num, show 1+2*(6157022962431661/20000000000000000000 : ℝ)=(10006157022962431661/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1089661791484038711/1090000000000000000 : ℝ)*(X 1 0+X 2 0)+(4431389781/2725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (5753/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (1089661791484038711/1090000000000000000 : ℝ)) (alpha := (4431389781/2725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1089661791484038711/1090000000000000000 : ℝ)*(X 0 1+X 2 1)+(4431389781/2725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (5753/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (1089661791484038711/1090000000000000000 : ℝ)) (alpha := (4431389781/2725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1089661791484038711/1090000000000000000 : ℝ)*(X 0 2+X 1 2)+(4431389781/2725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (5753/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (1089661791484038711/1090000000000000000 : ℝ)) (alpha := (4431389781/2725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108049121/10000000000 : ℝ)*X 0 0+(5390702123/10000000000 : ℝ)*X 0 1+(329222663/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336041237/2500000000 : ℝ)*X 1 0+(-271309759/1250000000 : ℝ)*X 1 1+(2633781231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106883303/200000000 : ℝ)*X 2 0+(1053512453/2000000000 : ℝ)*X 2 1+(-434095613/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543402429/1250000000 : ℝ)*X 0 0+(2111723137/5000000000 : ℝ)*X 0 1+(4474497539/10000000000 : ℝ)*X 0 2+(543402429/1250000000 : ℝ)*X 1 0+(2111723137/5000000000 : ℝ)*X 1 1+(4474497539/10000000000 : ℝ)*X 1 2+(543402429/1250000000 : ℝ)*X 2 0+(2111723137/5000000000 : ℝ)*X 2 1+(4474497539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108053373/10000000000 : ℝ)*X 0 0+(2633936413/5000000000 : ℝ)*X 0 1+(5390391029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312690907/10000000000 : ℝ)*X 1 0+(-2047649417/10000000000 : ℝ)*X 1 1+(1347597649/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328172791/2500000000 : ℝ)*X 2 0+(2695195041/5000000000 : ℝ)*X 2 1+(-2047649769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347229571/10000000000 : ℝ)*X 0 0+(89477279/200000000 : ℝ)*X 0 1+(264005087/625000000 : ℝ)*X 0 2+(4347229571/10000000000 : ℝ)*X 1 0+(89477279/200000000 : ℝ)*X 1 1+(264005087/625000000 : ℝ)*X 1 2+(4347229571/10000000000 : ℝ)*X 2 0+(89477279/200000000 : ℝ)*X 2 1+(264005087/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (513825223758257519477159439/54500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (435152891/20000000000000 : ℝ)*(base19) + (762914391/50000000000000 : ℝ)*(base23) + (2936391/4000000000000 : ℝ)*(upper2) + (617999713/100000000000000 : ℝ)*(upper3) + (73098609/12500000000000 : ℝ)*(upper4) + (6052100330452961/100000000000000 : ℝ)*(major0) + (6052100330452961/100000000000000 : ℝ)*(major1) + (6052100330452961/100000000000000 : ℝ)*(major2) + (8120906014678737/100000000000000 : ℝ)*(sp0) + (4060463850801993/50000000000000 : ℝ)*(sp1) + (8120928351539659/100000000000000 : ℝ)*(sp2) + (1991625334824823/50000000000000 : ℝ)*(sp3) + (2982836213/12500000000000 : ℝ)*(sp4) + (9899810817/50000000000000 : ℝ)*(sp7) + (49790880865891/1250000000000 : ℝ)*(f.failure) + (8120929877368441/100000000000000 : ℝ)*(f.sum) + (3193507033399/545000000000000000000000000 : ℝ)*base65 + (1374299532126026729/109000000000000000000000000000000 : ℝ)*base68 + (1832462695601026729/109000000000000000000000000000000 : ℝ)*base70 + (1593813253821026729/109000000000000000000000000000000 : ℝ)*base72 + (556319096531/136250000000000000000000000 : ℝ)*base73 + (899100275781026729/109000000000000000000000000000000 : ℝ)*base76 + (1497064976119026729/109000000000000000000000000000000 : ℝ)*base78 + (1234662409446026729/109000000000000000000000000000000 : ℝ)*base80 + (281720507749/545000000000000000000000000 : ℝ)*base81 + (397161/125000000000000000000 : ℝ)*base89 + (397161/125000000000000000000 : ℝ)*base91 + (397161/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1811256001809411494291451/1362500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1601946317/100000000000000 : ℝ)*(base19) + (1038892819/50000000000000 : ℝ)*(base23) + (130190103/100000000000000 : ℝ)*(upper2) + (158263361/50000000000000 : ℝ)*(upper5) + (304139967985447/5000000000000 : ℝ)*(major0) + (304139967985447/5000000000000 : ℝ)*(major1) + (304139967985447/5000000000000 : ℝ)*(major2) + (28108562617/100000000000000 : ℝ)*(sp0) + (29727219517/50000000000000 : ℝ)*(sp1) + (15881250539/50000000000000 : ℝ)*(sp2) + (8162095122140319/100000000000000 : ℝ)*(sp4) + (1632412434863517/20000000000000 : ℝ)*(sp5) + (408104469520811/5000000000000 : ℝ)*(sp6) + (2001737722201431/50000000000000 : ℝ)*(sp7) + (2001737722201431/50000000000000 : ℝ)*(f.failure) + (1020265403837867/12500000000000 : ℝ)*(f.sum) + (10926972889/10900000000000000000000000 : ℝ)*base65 + (66253965077811183/5450000000000000000000000000000 : ℝ)*base68 + (79271480860511183/5450000000000000000000000000000 : ℝ)*base70 + (54849729682611183/5450000000000000000000000000000 : ℝ)*base72 + (372309842449/109000000000000000000000000 : ℝ)*base73 + (116956862806961183/5450000000000000000000000000000 : ℝ)*base76 + (27032013826461183/5450000000000000000000000000000 : ℝ)*base78 + (3096498350938817/5450000000000000000000000000000 : ℝ)*base79 + (84621360787/54500000000000000000000000 : ℝ)*base82 + (79436501/5000000000000000000000 : ℝ)*base89 + (79436501/5000000000000000000000 : ℝ)*base91 + (79436501/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1268_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5753/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1268_s8_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054026881/5000000000 : ℝ)*x 0 + (5390669287/10000000000 : ℝ)*x 1 + (5267592223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054026881/5000000000 : ℝ)^8461 ≤ (320554896887/2500000000000 : ℝ)^6413 := by
    have hnat : (1054026881 : ℕ)^8461*2500000000000^6413 ≤ 320554896887^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054026881 5000000000 320554896887 2500000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390669287/10000000000 : ℝ)^8461 ≤ (44252970497691/100000000000000 : ℝ)^6413 := by
    have hnat : (5390669287 : ℕ)^8461*100000000000000^6413 ≤ 44252970497691^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390669287 10000000000 44252970497691 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267592223/10000000000 : ℝ)^8461 ≤ (42924833612217/100000000000000 : ℝ)^6413 := by
    have hnat : (5267592223 : ℕ)^8461*100000000000000^6413 ≤ 42924833612217^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267592223 10000000000 42924833612217 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054026881/5000000000 : ℝ), (5390669287/10000000000 : ℝ), (5267592223/10000000000 : ℝ)] ![(320554896887/2500000000000 : ℝ), (44252970497691/100000000000000 : ℝ), (42924833612217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054026881/5000000000 : ℝ)|^8461 ≤ (320554896887/2500000000000 : ℝ)^6413
        have hw : |(-1054026881/5000000000 : ℝ)|=(1054026881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390669287/10000000000 : ℝ)|^8461 ≤ (44252970497691/100000000000000 : ℝ)^6413
        have hw : |(5390669287/10000000000 : ℝ)|=(5390669287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267592223/10000000000 : ℝ)|^8461 ≤ (42924833612217/100000000000000 : ℝ)^6413
        have hw : |(5267592223/10000000000 : ℝ)|=(5267592223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s8_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336039/2500000 : ℝ)*x 0 + (-2170450557/10000000000 : ℝ)*x 1 + (5267592181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336039/2500000 : ℝ)^8461 ≤ (43749890230499/100000000000000 : ℝ)^6413 := by
    have hnat : (1336039 : ℕ)^8461*100000000000000^6413 ≤ 43749890230499^6413*2500000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336039 2500000 43749890230499 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170450557/10000000000 : ℝ)^8461 ≤ (6662638296697/50000000000000 : ℝ)^6413 := by
    have hnat : (2170450557 : ℕ)^8461*50000000000000^6413 ≤ 6662638296697^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170450557 10000000000 6662638296697 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267592181/10000000000 : ℝ)^8461 ≤ (42924833160667/100000000000000 : ℝ)^6413 := by
    have hnat : (5267592181 : ℕ)^8461*100000000000000^6413 ≤ 42924833160667^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267592181 10000000000 42924833160667 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336039/2500000 : ℝ), (-2170450557/10000000000 : ℝ), (5267592181/10000000000 : ℝ)] ![(43749890230499/100000000000000 : ℝ), (6662638296697/50000000000000 : ℝ), (42924833160667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336039/2500000 : ℝ)|^8461 ≤ (43749890230499/100000000000000 : ℝ)^6413
        have hw : |(1336039/2500000 : ℝ)|=(1336039/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170450557/10000000000 : ℝ)|^8461 ≤ (6662638296697/50000000000000 : ℝ)^6413
        have hw : |(-2170450557/10000000000 : ℝ)|=(2170450557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267592181/10000000000 : ℝ)|^8461 ≤ (42924833160667/100000000000000 : ℝ)^6413
        have hw : |(5267592181/10000000000 : ℝ)|=(5267592181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s8_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336038989/2500000000 : ℝ)*x 0 + (2633796129/5000000000 : ℝ)*x 1 + (-2170450513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336038989/2500000000 : ℝ)^8461 ≤ (43749889755261/100000000000000 : ℝ)^6413 := by
    have hnat : (1336038989 : ℕ)^8461*100000000000000^6413 ≤ 43749889755261^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336038989 2500000000 43749889755261 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633796129/5000000000 : ℝ)^8461 ≤ (42924833988509/100000000000000 : ℝ)^6413 := by
    have hnat : (2633796129 : ℕ)^8461*100000000000000^6413 ≤ 42924833988509^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633796129 5000000000 42924833988509 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170450513/10000000000 : ℝ)^8461 ≤ (208207441203/1562500000000 : ℝ)^6413 := by
    have hnat : (2170450513 : ℕ)^8461*1562500000000^6413 ≤ 208207441203^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170450513 10000000000 208207441203 1562500000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336038989/2500000000 : ℝ), (2633796129/5000000000 : ℝ), (-2170450513/10000000000 : ℝ)] ![(43749889755261/100000000000000 : ℝ), (42924833988509/100000000000000 : ℝ), (208207441203/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336038989/2500000000 : ℝ)|^8461 ≤ (43749889755261/100000000000000 : ℝ)^6413
        have hw : |(1336038989/2500000000 : ℝ)|=(1336038989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633796129/5000000000 : ℝ)|^8461 ≤ (42924833988509/100000000000000 : ℝ)^6413
        have hw : |(2633796129/5000000000 : ℝ)|=(2633796129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170450513/10000000000 : ℝ)|^8461 ≤ (208207441203/1562500000000 : ℝ)^6413
        have hw : |(-2170450513/10000000000 : ℝ)|=(2170450513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s8_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086805401/2500000000 : ℝ)*x 0 + (4223509043/10000000000 : ℝ)*x 1 + (894886753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086805401/2500000000 : ℝ)^8461 ≤ (3331764023731/10000000000000 : ℝ)^6413 := by
    have hnat : (1086805401 : ℕ)^8461*10000000000000^6413 ≤ 3331764023731^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086805401 2500000000 3331764023731 10000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223509043/10000000000 : ℝ)^8461 ≤ (16036210516917/50000000000000 : ℝ)^6413 := by
    have hnat : (4223509043 : ℕ)^8461*50000000000000^6413 ≤ 16036210516917^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223509043 10000000000 16036210516917 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894886753/2000000000 : ℝ)^8461 ≤ (1730496936283/5000000000000 : ℝ)^6413 := by
    have hnat : (894886753 : ℕ)^8461*5000000000000^6413 ≤ 1730496936283^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894886753 2000000000 1730496936283 5000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086805401/2500000000 : ℝ), (4223509043/10000000000 : ℝ), (894886753/2000000000 : ℝ)] ![(3331764023731/10000000000000 : ℝ), (16036210516917/50000000000000 : ℝ), (1730496936283/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086805401/2500000000 : ℝ)|^8461 ≤ (3331764023731/10000000000000 : ℝ)^6413
        have hw : |(1086805401/2500000000 : ℝ)|=(1086805401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223509043/10000000000 : ℝ)|^8461 ≤ (16036210516917/50000000000000 : ℝ)^6413
        have hw : |(4223509043/10000000000 : ℝ)|=(4223509043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(894886753/2000000000 : ℝ)|^8461 ≤ (1730496936283/5000000000000 : ℝ)^6413
        have hw : |(894886753/2000000000 : ℝ)|=(894886753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s8_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108058307/10000000000 : ℝ)*x 0 + (5267902969/10000000000 : ℝ)*x 1 + (5390357451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108058307/10000000000 : ℝ)^8461 ≤ (6411116174397/50000000000000 : ℝ)^6413 := by
    have hnat : (2108058307 : ℕ)^8461*50000000000000^6413 ≤ 6411116174397^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108058307 10000000000 6411116174397 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267902969/10000000000 : ℝ)^8461 ≤ (2146408726799/5000000000000 : ℝ)^6413 := by
    have hnat : (5267902969 : ℕ)^8461*5000000000000^6413 ≤ 2146408726799^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267902969 10000000000 2146408726799 5000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390357451/10000000000 : ℝ)^8461 ≤ (44249593098199/100000000000000 : ℝ)^6413 := by
    have hnat : (5390357451 : ℕ)^8461*100000000000000^6413 ≤ 44249593098199^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390357451 10000000000 44249593098199 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108058307/10000000000 : ℝ), (5267902969/10000000000 : ℝ), (5390357451/10000000000 : ℝ)] ![(6411116174397/50000000000000 : ℝ), (2146408726799/5000000000000 : ℝ), (44249593098199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108058307/10000000000 : ℝ)|^8461 ≤ (6411116174397/50000000000000 : ℝ)^6413
        have hw : |(-2108058307/10000000000 : ℝ)|=(2108058307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267902969/10000000000 : ℝ)|^8461 ≤ (2146408726799/5000000000000 : ℝ)^6413
        have hw : |(5267902969/10000000000 : ℝ)|=(5267902969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390357451/10000000000 : ℝ)|^8461 ≤ (44249593098199/100000000000000 : ℝ)^6413
        have hw : |(5390357451/10000000000 : ℝ)|=(5390357451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s8_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347230933/10000000000 : ℝ)*x 0 + (2236900427/5000000000 : ℝ)*x 1 + (105603607/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347230933/10000000000 : ℝ)^8461 ≤ (33317734569117/100000000000000 : ℝ)^6413 := by
    have hnat : (4347230933 : ℕ)^8461*100000000000000^6413 ≤ 33317734569117^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347230933 10000000000 33317734569117 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236900427/5000000000 : ℝ)^8461 ≤ (34603479863203/100000000000000 : ℝ)^6413 := by
    have hnat : (2236900427 : ℕ)^8461*100000000000000^6413 ≤ 34603479863203^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236900427 5000000000 34603479863203 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105603607/250000000 : ℝ)^8461 ≤ (6415757108807/20000000000000 : ℝ)^6413 := by
    have hnat : (105603607 : ℕ)^8461*20000000000000^6413 ≤ 6415757108807^6413*250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105603607 250000000 6415757108807 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347230933/10000000000 : ℝ), (2236900427/5000000000 : ℝ), (105603607/250000000 : ℝ)] ![(33317734569117/100000000000000 : ℝ), (34603479863203/100000000000000 : ℝ), (6415757108807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347230933/10000000000 : ℝ)|^8461 ≤ (33317734569117/100000000000000 : ℝ)^6413
        have hw : |(4347230933/10000000000 : ℝ)|=(4347230933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236900427/5000000000 : ℝ)|^8461 ≤ (34603479863203/100000000000000 : ℝ)^6413
        have hw : |(2236900427/5000000000 : ℝ)|=(2236900427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105603607/250000000 : ℝ)|^8461 ≤ (6415757108807/20000000000000 : ℝ)^6413
        have hw : |(105603607/250000000 : ℝ)|=(105603607/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1151/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7059/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11509/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (13221426838166941/100000000000000000000 : ℝ) := by
    have hpowers : (11509/100000 : ℝ)^2115 ≤ (13221426838166941/100000000000000000000 : ℝ)^512 := by
      have hnat : (11509 : ℕ)^2115*100000000000000000000^512 ≤ 13221426838166941^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11509 100000 13221426838166941 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11509/100000 : ℝ)) (X := (13221426838166941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7059/50000 : ℝ) ^ (2115/512 : ℝ) ≤ (30749110675482441/100000000000000000000 : ℝ) := by
    have hpowers : (7059/50000 : ℝ)^2115 ≤ (30749110675482441/100000000000000000000 : ℝ)^512 := by
      have hnat : (7059 : ℕ)^2115*100000000000000000000^512 ≤ 30749110675482441^512*50000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7059 50000 30749110675482441 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7059/50000 : ℝ)) (X := (30749110675482441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013221426838166941/50000000000000000000 : ℝ) ≤ (5000320032732983/5000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50013221426838166941/50000000000000000000 : ℝ)^512 ≤ (5000320032732983/5000000000000000 : ℝ)^2115 := by
      have hnat : (50013221426838166941 : ℕ)^512*5000000000000000^2115 ≤ 5000320032732983^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013221426838166941 50000000000000000000 5000320032732983 5000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000320032732983/5000000000000000 : ℝ)) (X := (50013221426838166941/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021985268756824691/50000000000000000000 : ℝ) ≤ (10001064263112587/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50021985268756824691/50000000000000000000 : ℝ)^512 ≤ (10001064263112587/10000000000000000 : ℝ)^2115 := by
      have hnat : (50021985268756824691 : ℕ)^512*10000000000000000^2115 ≤ 10001064263112587^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021985268756824691 50000000000000000000 10001064263112587 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001064263112587/10000000000000000 : ℝ)) (X := (50021985268756824691/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030749110675482441/50000000000000000000 : ℝ) ≤ (1250186057594901/1250000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50030749110675482441/50000000000000000000 : ℝ)^512 ≤ (1250186057594901/1250000000000000 : ℝ)^2115 := by
      have hnat : (50030749110675482441 : ℕ)^512*1250000000000000^2115 ≤ 1250186057594901^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030749110675482441 50000000000000000000 1250186057594901 1250000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250186057594901/1250000000000000 : ℝ)) (X := (50030749110675482441/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13221426838166941/100000000000000000000 : ℝ) ≤ ((6520476437342695779/6522500000000000000 : ℝ)+2*(424197646621/260900000000000 : ℝ)*(11509/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (6520476437342695779/6522500000000000000 : ℝ)+2*(424197646621/260900000000000 : ℝ)*(11509/100000 : ℝ)=(5000320032732983/5000000000000000 : ℝ) by norm_num, show 1+2*(13221426838166941/100000000000000000000 : ℝ)=(50013221426838166941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30749110675482441/100000000000000000000 : ℝ)+(13221426838166941/100000000000000000000 : ℝ) ≤ ((6520476437342695779/6522500000000000000 : ℝ)+(424197646621/260900000000000 : ℝ)*((7059/50000 : ℝ)+(11509/100000 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (6520476437342695779/6522500000000000000 : ℝ)+(424197646621/260900000000000 : ℝ)*((7059/50000 : ℝ)+(11509/100000 : ℝ))=(10001064263112587/10000000000000000 : ℝ) by norm_num, show 1+(30749110675482441/100000000000000000000 : ℝ)+(13221426838166941/100000000000000000000 : ℝ)=(50021985268756824691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30749110675482441/100000000000000000000 : ℝ) ≤ ((6520476437342695779/6522500000000000000 : ℝ)+2*(424197646621/260900000000000 : ℝ)*(7059/50000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (6520476437342695779/6522500000000000000 : ℝ)+2*(424197646621/260900000000000 : ℝ)*(7059/50000 : ℝ)=(1250186057594901/1250000000000000 : ℝ) by norm_num, show 1+2*(30749110675482441/100000000000000000000 : ℝ)=(50030749110675482441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6520476437342695779/6522500000000000000 : ℝ)*(X 1 0+X 2 0)+(424197646621/260900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (6520476437342695779/6522500000000000000 : ℝ)) (alpha := (424197646621/260900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6520476437342695779/6522500000000000000 : ℝ)*(X 0 1+X 2 1)+(424197646621/260900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (6520476437342695779/6522500000000000000 : ℝ)) (alpha := (424197646621/260900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6520476437342695779/6522500000000000000 : ℝ)*(X 0 2+X 1 2)+(424197646621/260900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (6520476437342695779/6522500000000000000 : ℝ)) (alpha := (424197646621/260900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054026881/5000000000 : ℝ)*X 0 0+(5390669287/10000000000 : ℝ)*X 0 1+(5267592223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336039/2500000 : ℝ)*X 1 0+(-2170450557/10000000000 : ℝ)*X 1 1+(5267592181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336038989/2500000000 : ℝ)*X 2 0+(2633796129/5000000000 : ℝ)*X 2 1+(-2170450513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086805401/2500000000 : ℝ)*X 0 0+(4223509043/10000000000 : ℝ)*X 0 1+(894886753/2000000000 : ℝ)*X 0 2+(1086805401/2500000000 : ℝ)*X 1 0+(4223509043/10000000000 : ℝ)*X 1 1+(894886753/2000000000 : ℝ)*X 1 2+(1086805401/2500000000 : ℝ)*X 2 0+(4223509043/10000000000 : ℝ)*X 2 1+(894886753/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108058307/10000000000 : ℝ)*X 0 0+(5267902969/10000000000 : ℝ)*X 0 1+(5390357451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4347230933/10000000000 : ℝ)*X 0 0+(2236900427/5000000000 : ℝ)*X 0 1+(105603607/250000000 : ℝ)*X 0 2+(4347230933/10000000000 : ℝ)*X 1 0+(2236900427/5000000000 : ℝ)*X 1 1+(105603607/250000000 : ℝ)*X 1 2+(4347230933/10000000000 : ℝ)*X 2 0+(2236900427/5000000000 : ℝ)*X 2 1+(105603607/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20272663251810483223239873/3261250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (238573617/20000000000000 : ℝ)*(base19) + (138896663/12500000000000 : ℝ)*(base23) + (3954359/50000000000000 : ℝ)*(lower2) + (26668601/25000000000000 : ℝ)*(upper3) + (156545909/100000000000000 : ℝ)*(upper5) + (60551763055421/1000000000000 : ℝ)*(major0) + (60551763055421/1000000000000 : ℝ)*(major1) + (60551763055421/1000000000000 : ℝ)*(major2) + (8125022926431917/100000000000000 : ℝ)*(sp0) + (8125056247748833/100000000000000 : ℝ)*(sp1) + (8125056329443613/100000000000000 : ℝ)*(sp2) + (99631938976499/2500000000000 : ℝ)*(sp3) + (6902837/20000000000 : ℝ)*(sp4) + (2175524977/12500000000000 : ℝ)*(sp5) + (31135116900467/781250000000 : ℝ)*(f.failure) + (4062528720308459/50000000000000 : ℝ)*(f.sum) + (737574667153/1304500000000000000000000000 : ℝ)*base66 + (36316941296525459/6522500000000000000000000000000 : ℝ)*base67 + (82287136155945459/6522500000000000000000000000000 : ℝ)*base69 + (51293753834987041/6522500000000000000000000000000 : ℝ)*base72 + (10923487224553/2609000000000000000000000000 : ℝ)*base73 + (12237313988399541/6522500000000000000000000000000 : ℝ)*base76 + (12560470859882959/6522500000000000000000000000000 : ℝ)*base77 + (77391406834587959/6522500000000000000000000000000 : ℝ)*base79 + (8672365425479/2609000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (692543/78125000000000000000 : ℝ)*base90 + (692543/78125000000000000000 : ℝ)*base92 + (692543/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1268_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1268_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1268_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1268_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1268_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1268_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
