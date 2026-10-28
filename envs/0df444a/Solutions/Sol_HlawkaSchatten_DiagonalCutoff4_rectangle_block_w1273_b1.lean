-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1273_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:25.996748+00:00
-- url     : https://prove2.me/submissions/e6e38d53-2f22-46aa-9304-62a43ac520cb

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
theorem support_rectangle_w1273_s3_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-525681569/2500000000 : ℝ)*x 0 + (2708461203/5000000000 : ℝ)*x 1 + (5243004353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525681569/2500000000 : ℝ)^8467 ≤ (12785410345583/100000000000000 : ℝ)^6419 := by
    have hnat : (525681569 : ℕ)^8467*100000000000000^6419 ≤ 12785410345583^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525681569 2500000000 12785410345583 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708461203/5000000000 : ℝ)^8467 ≤ (5568210573523/12500000000000 : ℝ)^6419 := by
    have hnat : (2708461203 : ℕ)^8467*12500000000000^6419 ≤ 5568210573523^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708461203 5000000000 5568210573523 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243004353/10000000000 : ℝ)^8467 ≤ (21334452528201/50000000000000 : ℝ)^6419 := by
    have hnat : (5243004353 : ℕ)^8467*50000000000000^6419 ≤ 21334452528201^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243004353 10000000000 21334452528201 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525681569/2500000000 : ℝ), (2708461203/5000000000 : ℝ), (5243004353/10000000000 : ℝ)] ![(12785410345583/100000000000000 : ℝ), (5568210573523/12500000000000 : ℝ), (21334452528201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525681569/2500000000 : ℝ)|^8467 ≤ (12785410345583/100000000000000 : ℝ)^6419
        have hw : |(-525681569/2500000000 : ℝ)|=(525681569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708461203/5000000000 : ℝ)|^8467 ≤ (5568210573523/12500000000000 : ℝ)^6419
        have hw : |(2708461203/5000000000 : ℝ)|=(2708461203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243004353/10000000000 : ℝ)|^8467 ≤ (21334452528201/50000000000000 : ℝ)^6419
        have hw : |(5243004353/10000000000 : ℝ)|=(5243004353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s3_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5350792819/10000000000 : ℝ)*x 0 + (-2191397501/10000000000 : ℝ)*x 1 + (1048600893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350792819/10000000000 : ℝ)^8467 ≤ (10957442155819/25000000000000 : ℝ)^6419 := by
    have hnat : (5350792819 : ℕ)^8467*25000000000000^6419 ≤ 10957442155819^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350792819 10000000000 10957442155819 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191397501/10000000000 : ℝ)^8467 ≤ (2700265020773/20000000000000 : ℝ)^6419 := by
    have hnat : (2191397501 : ℕ)^8467*20000000000000^6419 ≤ 2700265020773^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191397501 10000000000 2700265020773 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048600893/2000000000 : ℝ)^8467 ≤ (42668906258699/100000000000000 : ℝ)^6419 := by
    have hnat : (1048600893 : ℕ)^8467*100000000000000^6419 ≤ 42668906258699^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048600893 2000000000 42668906258699 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350792819/10000000000 : ℝ), (-2191397501/10000000000 : ℝ), (1048600893/2000000000 : ℝ)] ![(10957442155819/25000000000000 : ℝ), (2700265020773/20000000000000 : ℝ), (42668906258699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350792819/10000000000 : ℝ)|^8467 ≤ (10957442155819/25000000000000 : ℝ)^6419
        have hw : |(5350792819/10000000000 : ℝ)|=(5350792819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191397501/10000000000 : ℝ)|^8467 ≤ (2700265020773/20000000000000 : ℝ)^6419
        have hw : |(-2191397501/10000000000 : ℝ)|=(2191397501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048600893/2000000000 : ℝ)|^8467 ≤ (42668906258699/100000000000000 : ℝ)^6419
        have hw : |(1048600893/2000000000 : ℝ)|=(1048600893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s3_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070158597/2000000000 : ℝ)*x 0 + (2621501503/5000000000 : ℝ)*x 1 + (-273924901/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070158597/2000000000 : ℝ)^8467 ≤ (21914885208429/50000000000000 : ℝ)^6419 := by
    have hnat : (1070158597 : ℕ)^8467*50000000000000^6419 ≤ 21914885208429^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070158597 2000000000 21914885208429 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621501503/5000000000 : ℝ)^8467 ≤ (10667222649161/25000000000000 : ℝ)^6419 := by
    have hnat : (2621501503 : ℕ)^8467*25000000000000^6419 ≤ 10667222649161^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621501503 5000000000 10667222649161 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273924901/1250000000 : ℝ)^8467 ≤ (6750669488123/50000000000000 : ℝ)^6419 := by
    have hnat : (273924901 : ℕ)^8467*50000000000000^6419 ≤ 6750669488123^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273924901 1250000000 6750669488123 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070158597/2000000000 : ℝ), (2621501503/5000000000 : ℝ), (-273924901/1250000000 : ℝ)] ![(21914885208429/50000000000000 : ℝ), (10667222649161/25000000000000 : ℝ), (6750669488123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070158597/2000000000 : ℝ)|^8467 ≤ (21914885208429/50000000000000 : ℝ)^6419
        have hw : |(1070158597/2000000000 : ℝ)|=(1070158597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621501503/5000000000 : ℝ)|^8467 ≤ (10667222649161/25000000000000 : ℝ)^6419
        have hw : |(2621501503/5000000000 : ℝ)|=(2621501503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273924901/1250000000 : ℝ)|^8467 ≤ (6750669488123/50000000000000 : ℝ)^6419
        have hw : |(-273924901/1250000000 : ℝ)|=(273924901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s3_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4344853701/10000000000 : ℝ)*x 0 + (417085393/1000000000 : ℝ)*x 1 + (226292113/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344853701/10000000000 : ℝ)^8467 ≤ (8325496110387/25000000000000 : ℝ)^6419 := by
    have hnat : (4344853701 : ℕ)^8467*25000000000000^6419 ≤ 8325496110387^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344853701 10000000000 8325496110387 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417085393/1000000000 : ℝ)^8467 ≤ (7888541256143/25000000000000 : ℝ)^6419 := by
    have hnat : (417085393 : ℕ)^8467*25000000000000^6419 ≤ 7888541256143^6419*1000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417085393 1000000000 7888541256143 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226292113/500000000 : ℝ)^8467 ≤ (35143850516699/100000000000000 : ℝ)^6419 := by
    have hnat : (226292113 : ℕ)^8467*100000000000000^6419 ≤ 35143850516699^6419*500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226292113 500000000 35143850516699 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344853701/10000000000 : ℝ), (417085393/1000000000 : ℝ), (226292113/500000000 : ℝ)] ![(8325496110387/25000000000000 : ℝ), (7888541256143/25000000000000 : ℝ), (35143850516699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344853701/10000000000 : ℝ)|^8467 ≤ (8325496110387/25000000000000 : ℝ)^6419
        have hw : |(4344853701/10000000000 : ℝ)|=(4344853701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417085393/1000000000 : ℝ)|^8467 ≤ (7888541256143/25000000000000 : ℝ)^6419
        have hw : |(417085393/1000000000 : ℝ)|=(417085393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226292113/500000000 : ℝ)|^8467 ≤ (35143850516699/100000000000000 : ℝ)^6419
        have hw : |(226292113/500000000 : ℝ)|=(226292113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s3_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-262842417/1250000000 : ℝ)*x 0 + (1310905883/2500000000 : ℝ)*x 1 + (135407499/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262842417/1250000000 : ℝ)^8467 ≤ (12785515091649/100000000000000 : ℝ)^6419 := by
    have hnat : (262842417 : ℕ)^8467*100000000000000^6419 ≤ 12785515091649^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262842417 1250000000 12785515091649 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310905883/2500000000 : ℝ)^8467 ≤ (53344439921/125000000000 : ℝ)^6419 := by
    have hnat : (1310905883 : ℕ)^8467*125000000000^6419 ≤ 53344439921^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310905883 2500000000 53344439921 125000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135407499/250000000 : ℝ)^8467 ≤ (11134733238411/25000000000000 : ℝ)^6419 := by
    have hnat : (135407499 : ℕ)^8467*25000000000000^6419 ≤ 11134733238411^6419*250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135407499 250000000 11134733238411 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262842417/1250000000 : ℝ), (1310905883/2500000000 : ℝ), (135407499/250000000 : ℝ)] ![(12785515091649/100000000000000 : ℝ), (53344439921/125000000000 : ℝ), (11134733238411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262842417/1250000000 : ℝ)|^8467 ≤ (12785515091649/100000000000000 : ℝ)^6419
        have hw : |(-262842417/1250000000 : ℝ)|=(262842417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310905883/2500000000 : ℝ)|^8467 ≤ (53344439921/125000000000 : ℝ)^6419
        have hw : |(1310905883/2500000000 : ℝ)|=(1310905883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135407499/250000000 : ℝ)|^8467 ≤ (11134733238411/25000000000000 : ℝ)^6419
        have hw : |(135407499/250000000 : ℝ)|=(135407499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s3_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326582123/2500000000 : ℝ)*x 0 + (-1009050727/5000000000 : ℝ)*x 1 + (5416299793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326582123/2500000000 : ℝ)^8467 ≤ (43349982417073/100000000000000 : ℝ)^6419 := by
    have hnat : (1326582123 : ℕ)^8467*100000000000000^6419 ≤ 43349982417073^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326582123 2500000000 43349982417073 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009050727/5000000000 : ℝ)^8467 ≤ (378471450957/3125000000000 : ℝ)^6419 := by
    have hnat : (1009050727 : ℕ)^8467*3125000000000^6419 ≤ 378471450957^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009050727 5000000000 378471450957 3125000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416299793/10000000000 : ℝ)^8467 ≤ (22269465571119/50000000000000 : ℝ)^6419 := by
    have hnat : (5416299793 : ℕ)^8467*50000000000000^6419 ≤ 22269465571119^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416299793 10000000000 22269465571119 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326582123/2500000000 : ℝ), (-1009050727/5000000000 : ℝ), (5416299793/10000000000 : ℝ)] ![(43349982417073/100000000000000 : ℝ), (378471450957/3125000000000 : ℝ), (22269465571119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326582123/2500000000 : ℝ)|^8467 ≤ (43349982417073/100000000000000 : ℝ)^6419
        have hw : |(1326582123/2500000000 : ℝ)|=(1326582123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1009050727/5000000000 : ℝ)|^8467 ≤ (378471450957/3125000000000 : ℝ)^6419
        have hw : |(-1009050727/5000000000 : ℝ)|=(1009050727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416299793/10000000000 : ℝ)|^8467 ≤ (22269465571119/50000000000000 : ℝ)^6419
        have hw : |(5416299793/10000000000 : ℝ)|=(5416299793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s3_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2653163881/5000000000 : ℝ)*x 0 + (1083260047/2000000000 : ℝ)*x 1 + (-1009050921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653163881/5000000000 : ℝ)^8467 ≤ (10837493637651/25000000000000 : ℝ)^6419 := by
    have hnat : (2653163881 : ℕ)^8467*25000000000000^6419 ≤ 10837493637651^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653163881 5000000000 10837493637651 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083260047/2000000000 : ℝ)^8467 ≤ (22269467968249/50000000000000 : ℝ)^6419 := by
    have hnat : (1083260047 : ℕ)^8467*50000000000000^6419 ≤ 22269467968249^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083260047 2000000000 22269467968249 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009050921/5000000000 : ℝ)^8467 ≤ (12111089502007/100000000000000 : ℝ)^6419 := by
    have hnat : (1009050921 : ℕ)^8467*100000000000000^6419 ≤ 12111089502007^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009050921 5000000000 12111089502007 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653163881/5000000000 : ℝ), (1083260047/2000000000 : ℝ), (-1009050921/5000000000 : ℝ)] ![(10837493637651/25000000000000 : ℝ), (22269467968249/50000000000000 : ℝ), (12111089502007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653163881/5000000000 : ℝ)|^8467 ≤ (10837493637651/25000000000000 : ℝ)^6419
        have hw : |(2653163881/5000000000 : ℝ)|=(2653163881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083260047/2000000000 : ℝ)|^8467 ≤ (22269467968249/50000000000000 : ℝ)^6419
        have hw : |(1083260047/2000000000 : ℝ)|=(1083260047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1009050921/5000000000 : ℝ)|^8467 ≤ (12111089502007/100000000000000 : ℝ)^6419
        have hw : |(-1009050921/5000000000 : ℝ)|=(1009050921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s3_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2172439973/5000000000 : ℝ)*x 0 + (4524576549/10000000000 : ℝ)*x 1 + (4172126351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172439973/5000000000 : ℝ)^8467 ≤ (3330224978241/10000000000000 : ℝ)^6419 := by
    have hnat : (2172439973 : ℕ)^8467*10000000000000^6419 ≤ 3330224978241^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172439973 5000000000 3330224978241 10000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524576549/10000000000 : ℝ)^8467 ≤ (35130886866881/100000000000000 : ℝ)^6419 := by
    have hnat : (4524576549 : ℕ)^8467*100000000000000^6419 ≤ 35130886866881^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524576549 10000000000 35130886866881 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172126351/10000000000 : ℝ)^8467 ≤ (3945857916577/12500000000000 : ℝ)^6419 := by
    have hnat : (4172126351 : ℕ)^8467*12500000000000^6419 ≤ 3945857916577^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172126351 10000000000 3945857916577 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172439973/5000000000 : ℝ), (4524576549/10000000000 : ℝ), (4172126351/10000000000 : ℝ)] ![(3330224978241/10000000000000 : ℝ), (35130886866881/100000000000000 : ℝ), (3945857916577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172439973/5000000000 : ℝ)|^8467 ≤ (3330224978241/10000000000000 : ℝ)^6419
        have hw : |(2172439973/5000000000 : ℝ)|=(2172439973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524576549/10000000000 : ℝ)|^8467 ≤ (35130886866881/100000000000000 : ℝ)^6419
        have hw : |(4524576549/10000000000 : ℝ)|=(4524576549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172126351/10000000000 : ℝ)|^8467 ≤ (3945857916577/12500000000000 : ℝ)^6419
        have hw : |(4172126351/10000000000 : ℝ)|=(4172126351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10991/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14673/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9627/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (392505832596801/6250000000000000000 : ℝ) := by
    have hpowers : (9627/100000 : ℝ)^4233 ≤ (392505832596801/6250000000000000000 : ℝ)^1024 := by
      have hnat : (9627 : ℕ)^4233*6250000000000000000^1024 ≤ 392505832596801^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9627 100000 392505832596801 6250000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9627/100000 : ℝ)) (X := (392505832596801/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16141/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (53180388522367487/100000000000000000000 : ℝ) := by
    have hpowers : (16141/100000 : ℝ)^4233 ≤ (53180388522367487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16141 : ℕ)^4233*100000000000000000000^1024 ≤ 53180388522367487^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16141 100000 53180388522367487 100000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16141/100000 : ℝ)) (X := (53180388522367487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125392505832596801/3125000000000000000 : ℝ) ≤ (10000303827518081/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (3125392505832596801/3125000000000000000 : ℝ)^1024 ≤ (10000303827518081/10000000000000000 : ℝ)^4233 := by
      have hnat : (3125392505832596801 : ℕ)^1024*10000000000000000^4233 ≤ 10000303827518081^4233*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125392505832596801 3125000000000000000 10000303827518081 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000303827518081/10000000000000000 : ℝ)) (X := (3125392505832596801/3125000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100059460481843916303/100000000000000000000 : ℝ) ≤ (10001438077373341/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (100059460481843916303/100000000000000000000 : ℝ)^1024 ≤ (10001438077373341/10000000000000000 : ℝ)^4233 := by
      have hnat : (100059460481843916303 : ℕ)^1024*10000000000000000^4233 ≤ 10001438077373341^4233*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100059460481843916303 100000000000000000000 10001438077373341 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001438077373341/10000000000000000 : ℝ)) (X := (100059460481843916303/100000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50053180388522367487/50000000000000000000 : ℝ) ≤ (10002572327228601/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50053180388522367487/50000000000000000000 : ℝ)^1024 ≤ (10002572327228601/10000000000000000 : ℝ)^4233 := by
      have hnat : (50053180388522367487 : ℕ)^1024*10000000000000000^4233 ≤ 10002572327228601^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053180388522367487 50000000000000000000 10002572327228601 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002572327228601/10000000000000000 : ℝ)) (X := (50053180388522367487/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(392505832596801/6250000000000000000 : ℝ) ≤ ((32560070142869801797/32570000000000000000 : ℝ)+2*(56712492763/32570000000000 : ℝ)*(9627/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (32560070142869801797/32570000000000000000 : ℝ)+2*(56712492763/32570000000000 : ℝ)*(9627/100000 : ℝ)=(10000303827518081/10000000000000000 : ℝ) by norm_num, show 1+2*(392505832596801/6250000000000000000 : ℝ)=(3125392505832596801/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53180388522367487/100000000000000000000 : ℝ)+(392505832596801/6250000000000000000 : ℝ) ≤ ((32560070142869801797/32570000000000000000 : ℝ)+(56712492763/32570000000000 : ℝ)*((16141/100000 : ℝ)+(9627/100000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (32560070142869801797/32570000000000000000 : ℝ)+(56712492763/32570000000000 : ℝ)*((16141/100000 : ℝ)+(9627/100000 : ℝ))=(10001438077373341/10000000000000000 : ℝ) by norm_num, show 1+(53180388522367487/100000000000000000000 : ℝ)+(392505832596801/6250000000000000000 : ℝ)=(100059460481843916303/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53180388522367487/100000000000000000000 : ℝ) ≤ ((32560070142869801797/32570000000000000000 : ℝ)+2*(56712492763/32570000000000 : ℝ)*(16141/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (32560070142869801797/32570000000000000000 : ℝ)+2*(56712492763/32570000000000 : ℝ)*(16141/100000 : ℝ)=(10002572327228601/10000000000000000 : ℝ) by norm_num, show 1+2*(53180388522367487/100000000000000000000 : ℝ)=(50053180388522367487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32560070142869801797/32570000000000000000 : ℝ)*(X 1 0+X 2 0)+(56712492763/32570000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (9627/100000 : ℝ)) (hi := (16141/100000 : ℝ)) (c := (32560070142869801797/32570000000000000000 : ℝ)) (alpha := (56712492763/32570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32560070142869801797/32570000000000000000 : ℝ)*(X 0 1+X 2 1)+(56712492763/32570000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (9627/100000 : ℝ)) (hi := (16141/100000 : ℝ)) (c := (32560070142869801797/32570000000000000000 : ℝ)) (alpha := (56712492763/32570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32560070142869801797/32570000000000000000 : ℝ)*(X 0 2+X 1 2)+(56712492763/32570000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (9627/100000 : ℝ)) (hi := (16141/100000 : ℝ)) (c := (32560070142869801797/32570000000000000000 : ℝ)) (alpha := (56712492763/32570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-525681569/2500000000 : ℝ)*X 0 0+(2708461203/5000000000 : ℝ)*X 0 1+(5243004353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350792819/10000000000 : ℝ)*X 1 0+(-2191397501/10000000000 : ℝ)*X 1 1+(1048600893/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070158597/2000000000 : ℝ)*X 2 0+(2621501503/5000000000 : ℝ)*X 2 1+(-273924901/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4344853701/10000000000 : ℝ)*X 0 0+(417085393/1000000000 : ℝ)*X 0 1+(226292113/500000000 : ℝ)*X 0 2+(4344853701/10000000000 : ℝ)*X 1 0+(417085393/1000000000 : ℝ)*X 1 1+(226292113/500000000 : ℝ)*X 1 2+(4344853701/10000000000 : ℝ)*X 2 0+(417085393/1000000000 : ℝ)*X 2 1+(226292113/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-262842417/1250000000 : ℝ)*X 0 0+(1310905883/2500000000 : ℝ)*X 0 1+(135407499/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326582123/2500000000 : ℝ)*X 1 0+(-1009050727/5000000000 : ℝ)*X 1 1+(5416299793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2653163881/5000000000 : ℝ)*X 2 0+(1083260047/2000000000 : ℝ)*X 2 1+(-1009050921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2172439973/5000000000 : ℝ)*X 0 0+(4524576549/10000000000 : ℝ)*X 0 1+(4172126351/10000000000 : ℝ)*X 0 2+(2172439973/5000000000 : ℝ)*X 1 0+(4524576549/10000000000 : ℝ)*X 1 1+(4172126351/10000000000 : ℝ)*X 1 2+(2172439973/5000000000 : ℝ)*X 2 0+(4524576549/10000000000 : ℝ)*X 2 1+(4172126351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4560199883643840016323937473/814250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348810681/20000000000000 : ℝ)*(base19) + (951972091/50000000000000 : ℝ)*(base23) + (282205437/50000000000000 : ℝ)*(upper3) + (30106987/20000000000000 : ℝ)*(lower4) + (2141734583101899/50000000000000 : ℝ)*(major0) + (2141734583101899/50000000000000 : ℝ)*(major1) + (2141734583101899/50000000000000 : ℝ)*(major2) + (1437469451015913/25000000000000 : ℝ)*(sp0) + (1437473770365399/25000000000000 : ℝ)*(sp1) + (1437464710481279/25000000000000 : ℝ)*(sp2) + (352126767958579/12500000000000 : ℝ)*(sp3) + (19021451349/100000000000000 : ℝ)*(sp4) + (36079645703/100000000000000 : ℝ)*(sp6) + (13588270461/50000000000000 : ℝ)*(sp7) + (1408520660104777/50000000000000 : ℝ)*(f.failure) + (5749896825515001/100000000000000 : ℝ)*(f.sum) + (29724883993/50890625000000000000000000 : ℝ)*base65 + (14376460824158312503/1628500000000000000000000000000000 : ℝ)*base67 + (12816107328288312503/1628500000000000000000000000000000 : ℝ)*base69 + (3074763567233312503/1628500000000000000000000000000000 : ℝ)*base71 + (2590090491927/1628500000000000000000000000 : ℝ)*base73 + (930820983984312503/1628500000000000000000000000000000 : ℝ)*base75 + (13432123195606312503/1628500000000000000000000000000000 : ℝ)*base77 + (12565556576209812503/1628500000000000000000000000000000 : ℝ)*base79 + (1477916143617/814250000000000000000000000 : ℝ)*base82 + (9915531/5000000000000000000000 : ℝ)*base89 + (9915531/5000000000000000000000 : ℝ)*base91 + (9915531/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1911638547602425042187404527/407125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (626872641/20000000000000 : ℝ)*(base19) + (269358757/12500000000000 : ℝ)*(base23) + (2060467/4000000000000 : ℝ)*(upper3) + (28070139/100000000000000 : ℝ)*(lower4) + (476992821/100000000000000 : ℝ)*(upper5) + (2157114052407303/50000000000000 : ℝ)*(major0) + (2157114052407303/50000000000000 : ℝ)*(major1) + (2157114052407303/50000000000000 : ℝ)*(major2) + (74351320401/100000000000000 : ℝ)*(sp1) + (46223355943/100000000000000 : ℝ)*(sp2) + (1447796497235579/25000000000000 : ℝ)*(sp4) + (5791108503258711/100000000000000 : ℝ)*(sp5) + (2895568805358159/50000000000000 : ℝ)*(sp6) + (1418635032085797/50000000000000 : ℝ)*(sp7) + (1418635032085797/50000000000000 : ℝ)*(f.failure) + (1447796497235579/25000000000000 : ℝ)*(f.sum) + (150791287869/40712500000000000000000000 : ℝ)*base65 + (28497995617001323491/1628500000000000000000000000000000 : ℝ)*base67 + (27406327977775323491/1628500000000000000000000000000000 : ℝ)*base69 + (20251403628096823491/1628500000000000000000000000000000 : ℝ)*base71 + (4645281750871/3257000000000000000000000000 : ℝ)*base74 + (9964718540027323491/1628500000000000000000000000000000 : ℝ)*base75 + (16983352724806823491/1628500000000000000000000000000000 : ℝ)*base77 + (1288115023964676509/1628500000000000000000000000000000 : ℝ)*base80 + (5314768152049/1628500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (89429409/5000000000000000000000 : ℝ)*base90 + (89429409/5000000000000000000000 : ℝ)*base92 + (89429409/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1273_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10991/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1273_s4_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263103233/1250000000 : ℝ)*x 0 + (5396237103/10000000000 : ℝ)*x 1 + (5262313141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263103233/1250000000 : ℝ)^8467 ≤ (2560450497731/20000000000000 : ℝ)^6419 := by
    have hnat : (263103233 : ℕ)^8467*20000000000000^6419 ≤ 2560450497731^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263103233 1250000000 2560450497731 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396237103/10000000000 : ℝ)^8467 ≤ (22160722516741/50000000000000 : ℝ)^6419 := by
    have hnat : (5396237103 : ℕ)^8467*50000000000000^6419 ≤ 22160722516741^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396237103 10000000000 22160722516741 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262313141/10000000000 : ℝ)^8467 ≤ (21438151235553/50000000000000 : ℝ)^6419 := by
    have hnat : (5262313141 : ℕ)^8467*50000000000000^6419 ≤ 21438151235553^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262313141 10000000000 21438151235553 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263103233/1250000000 : ℝ), (5396237103/10000000000 : ℝ), (5262313141/10000000000 : ℝ)] ![(2560450497731/20000000000000 : ℝ), (22160722516741/50000000000000 : ℝ), (21438151235553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263103233/1250000000 : ℝ)|^8467 ≤ (2560450497731/20000000000000 : ℝ)^6419
        have hw : |(-263103233/1250000000 : ℝ)|=(263103233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396237103/10000000000 : ℝ)|^8467 ≤ (22160722516741/50000000000000 : ℝ)^6419
        have hw : |(5396237103/10000000000 : ℝ)|=(5396237103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262313141/10000000000 : ℝ)|^8467 ≤ (21438151235553/50000000000000 : ℝ)^6419
        have hw : |(5262313141/10000000000 : ℝ)|=(5262313141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s4_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345563299/10000000000 : ℝ)*x 0 + (-10864019/50000000 : ℝ)*x 1 + (2631156573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345563299/10000000000 : ℝ)^8467 ≤ (43773273973159/100000000000000 : ℝ)^6419 := by
    have hnat : (5345563299 : ℕ)^8467*100000000000000^6419 ≤ 43773273973159^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345563299 10000000000 43773273973159 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10864019/50000000 : ℝ)^8467 ≤ (13350423491337/100000000000000 : ℝ)^6419 := by
    have hnat : (10864019 : ℕ)^8467*100000000000000^6419 ≤ 13350423491337^6419*50000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10864019 50000000 13350423491337 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631156573/5000000000 : ℝ)^8467 ≤ (42876302524843/100000000000000 : ℝ)^6419 := by
    have hnat : (2631156573 : ℕ)^8467*100000000000000^6419 ≤ 42876302524843^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631156573 5000000000 42876302524843 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345563299/10000000000 : ℝ), (-10864019/50000000 : ℝ), (2631156573/5000000000 : ℝ)] ![(43773273973159/100000000000000 : ℝ), (13350423491337/100000000000000 : ℝ), (42876302524843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345563299/10000000000 : ℝ)|^8467 ≤ (43773273973159/100000000000000 : ℝ)^6419
        have hw : |(5345563299/10000000000 : ℝ)|=(5345563299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10864019/50000000 : ℝ)|^8467 ≤ (13350423491337/100000000000000 : ℝ)^6419
        have hw : |(-10864019/50000000 : ℝ)|=(10864019/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631156573/5000000000 : ℝ)|^8467 ≤ (42876302524843/100000000000000 : ℝ)^6419
        have hw : |(2631156573/5000000000 : ℝ)|=(2631156573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s4_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069112651/2000000000 : ℝ)*x 0 + (1052462631/2000000000 : ℝ)*x 1 + (-2172803847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069112651/2000000000 : ℝ)^8467 ≤ (437732734979/1000000000000 : ℝ)^6419 := by
    have hnat : (1069112651 : ℕ)^8467*1000000000000^6419 ≤ 437732734979^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069112651 2000000000 437732734979 1000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052462631/2000000000 : ℝ)^8467 ≤ (4287630262157/10000000000000 : ℝ)^6419 := by
    have hnat : (1052462631 : ℕ)^8467*10000000000000^6419 ≤ 4287630262157^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052462631 2000000000 4287630262157 10000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172803847/10000000000 : ℝ)^8467 ≤ (6675211936129/50000000000000 : ℝ)^6419 := by
    have hnat : (2172803847 : ℕ)^8467*50000000000000^6419 ≤ 6675211936129^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172803847 10000000000 6675211936129 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069112651/2000000000 : ℝ), (1052462631/2000000000 : ℝ), (-2172803847/10000000000 : ℝ)] ![(437732734979/1000000000000 : ℝ), (4287630262157/10000000000000 : ℝ), (6675211936129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069112651/2000000000 : ℝ)|^8467 ≤ (437732734979/1000000000000 : ℝ)^6419
        have hw : |(1069112651/2000000000 : ℝ)|=(1069112651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052462631/2000000000 : ℝ)|^8467 ≤ (4287630262157/10000000000000 : ℝ)^6419
        have hw : |(1052462631/2000000000 : ℝ)|=(1052462631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172803847/10000000000 : ℝ)|^8467 ≤ (6675211936129/50000000000000 : ℝ)^6419
        have hw : |(-2172803847/10000000000 : ℝ)|=(2172803847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s4_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869222921/2000000000 : ℝ)*x 0 + (210575571/500000000 : ℝ)*x 1 + (1121216311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869222921/2000000000 : ℝ)^8467 ≤ (1041085404587/3125000000000 : ℝ)^6419 := by
    have hnat : (869222921 : ℕ)^8467*3125000000000^6419 ≤ 1041085404587^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869222921 2000000000 1041085404587 3125000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210575571/500000000 : ℝ)^8467 ≤ (31960522080429/100000000000000 : ℝ)^6419 := by
    have hnat : (210575571 : ℕ)^8467*100000000000000^6419 ≤ 31960522080429^6419*500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210575571 500000000 31960522080429 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121216311/2500000000 : ℝ)^8467 ≤ (17362372479993/50000000000000 : ℝ)^6419 := by
    have hnat : (1121216311 : ℕ)^8467*50000000000000^6419 ≤ 17362372479993^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121216311 2500000000 17362372479993 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869222921/2000000000 : ℝ), (210575571/500000000 : ℝ), (1121216311/2500000000 : ℝ)] ![(1041085404587/3125000000000 : ℝ), (31960522080429/100000000000000 : ℝ), (17362372479993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869222921/2000000000 : ℝ)|^8467 ≤ (1041085404587/3125000000000 : ℝ)^6419
        have hw : |(869222921/2000000000 : ℝ)|=(869222921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210575571/500000000 : ℝ)|^8467 ≤ (31960522080429/100000000000000 : ℝ)^6419
        have hw : |(210575571/500000000 : ℝ)|=(210575571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121216311/2500000000 : ℝ)|^8467 ≤ (17362372479993/50000000000000 : ℝ)^6419
        have hw : |(1121216311/2500000000 : ℝ)|=(1121216311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s4_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104831593/10000000000 : ℝ)*x 0 + (263134063/500000000 : ℝ)*x 1 + (5395867673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104831593/10000000000 : ℝ)^8467 ≤ (12802298451977/100000000000000 : ℝ)^6419 := by
    have hnat : (2104831593 : ℕ)^8467*100000000000000^6419 ≤ 12802298451977^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104831593 10000000000 12802298451977 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263134063/500000000 : ℝ)^8467 ≤ (42880258832017/100000000000000 : ℝ)^6419 := by
    have hnat : (263134063 : ℕ)^8467*100000000000000^6419 ≤ 42880258832017^6419*500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263134063 500000000 42880258832017 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395867673/10000000000 : ℝ)^8467 ≤ (2215872135361/5000000000000 : ℝ)^6419 := by
    have hnat : (5395867673 : ℕ)^8467*5000000000000^6419 ≤ 2215872135361^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395867673 10000000000 2215872135361 5000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104831593/10000000000 : ℝ), (263134063/500000000 : ℝ), (5395867673/10000000000 : ℝ)] ![(12802298451977/100000000000000 : ℝ), (42880258832017/100000000000000 : ℝ), (2215872135361/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104831593/10000000000 : ℝ)|^8467 ≤ (12802298451977/100000000000000 : ℝ)^6419
        have hw : |(-2104831593/10000000000 : ℝ)|=(2104831593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263134063/500000000 : ℝ)|^8467 ≤ (42880258832017/100000000000000 : ℝ)^6419
        have hw : |(263134063/500000000 : ℝ)|=(263134063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395867673/10000000000 : ℝ)|^8467 ≤ (2215872135361/5000000000000 : ℝ)^6419
        have hw : |(5395867673/10000000000 : ℝ)|=(5395867673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s4_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311320727/10000000000 : ℝ)*x 0 + (-2039249333/10000000000 : ℝ)*x 1 + (2697933821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311320727/10000000000 : ℝ)^8467 ≤ (21701893369369/50000000000000 : ℝ)^6419 := by
    have hnat : (5311320727 : ℕ)^8467*50000000000000^6419 ≤ 21701893369369^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311320727 10000000000 21701893369369 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039249333/10000000000 : ℝ)^8467 ≤ (245575417633/2000000000000 : ℝ)^6419 := by
    have hnat : (2039249333 : ℕ)^8467*2000000000000^6419 ≤ 245575417633^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039249333 10000000000 245575417633 2000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697933821/5000000000 : ℝ)^8467 ≤ (2769840148211/6250000000000 : ℝ)^6419 := by
    have hnat : (2697933821 : ℕ)^8467*6250000000000^6419 ≤ 2769840148211^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697933821 5000000000 2769840148211 6250000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311320727/10000000000 : ℝ), (-2039249333/10000000000 : ℝ), (2697933821/5000000000 : ℝ)] ![(21701893369369/50000000000000 : ℝ), (245575417633/2000000000000 : ℝ), (2769840148211/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311320727/10000000000 : ℝ)|^8467 ≤ (21701893369369/50000000000000 : ℝ)^6419
        have hw : |(5311320727/10000000000 : ℝ)|=(5311320727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039249333/10000000000 : ℝ)|^8467 ≤ (245575417633/2000000000000 : ℝ)^6419
        have hw : |(-2039249333/10000000000 : ℝ)|=(2039249333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697933821/5000000000 : ℝ)|^8467 ≤ (2769840148211/6250000000000 : ℝ)^6419
        have hw : |(2697933821/5000000000 : ℝ)|=(2697933821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s4_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311320969/10000000000 : ℝ)*x 0 + (5395867381/10000000000 : ℝ)*x 1 + (-25490617/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311320969/10000000000 : ℝ)^8467 ≤ (43403789347309/100000000000000 : ℝ)^6419 := by
    have hnat : (5311320969 : ℕ)^8467*100000000000000^6419 ≤ 43403789347309^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311320969 10000000000 43403789347309 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395867381/10000000000 : ℝ)^8467 ≤ (11079359885947/25000000000000 : ℝ)^6419 := by
    have hnat : (5395867381 : ℕ)^8467*25000000000000^6419 ≤ 11079359885947^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395867381 10000000000 11079359885947 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25490617/125000000 : ℝ)^8467 ≤ (3069692774023/25000000000000 : ℝ)^6419 := by
    have hnat : (25490617 : ℕ)^8467*25000000000000^6419 ≤ 3069692774023^6419*125000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25490617 125000000 3069692774023 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311320969/10000000000 : ℝ), (5395867381/10000000000 : ℝ), (-25490617/125000000 : ℝ)] ![(43403789347309/100000000000000 : ℝ), (11079359885947/25000000000000 : ℝ), (3069692774023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311320969/10000000000 : ℝ)|^8467 ≤ (43403789347309/100000000000000 : ℝ)^6419
        have hw : |(5311320969/10000000000 : ℝ)|=(5311320969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395867381/10000000000 : ℝ)|^8467 ≤ (11079359885947/25000000000000 : ℝ)^6419
        have hw : |(5395867381/10000000000 : ℝ)|=(5395867381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25490617/125000000 : ℝ)|^8467 ≤ (3069692774023/25000000000000 : ℝ)^6419
        have hw : |(-25490617/125000000 : ℝ)|=(25490617/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s4_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (6790823/15625000 : ℝ)*x 0 + (3587291/8000000 : ℝ)*x 1 + (842453173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6790823/15625000 : ℝ)^8467 ≤ (8328713860629/25000000000000 : ℝ)^6419 := by
    have hnat : (6790823 : ℕ)^8467*25000000000000^6419 ≤ 8328713860629^6419*15625000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6790823 15625000 8328713860629 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3587291/8000000 : ℝ)^8467 ≤ (34717070183111/100000000000000 : ℝ)^6419 := by
    have hnat : (3587291 : ℕ)^8467*100000000000000^6419 ≤ 34717070183111^6419*8000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3587291 8000000 34717070183111 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842453173/2000000000 : ℝ)^8467 ≤ (7992018590013/25000000000000 : ℝ)^6419 := by
    have hnat : (842453173 : ℕ)^8467*25000000000000^6419 ≤ 7992018590013^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842453173 2000000000 7992018590013 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6790823/15625000 : ℝ), (3587291/8000000 : ℝ), (842453173/2000000000 : ℝ)] ![(8328713860629/25000000000000 : ℝ), (34717070183111/100000000000000 : ℝ), (7992018590013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6790823/15625000 : ℝ)|^8467 ≤ (8328713860629/25000000000000 : ℝ)^6419
        have hw : |(6790823/15625000 : ℝ)|=(6790823/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3587291/8000000 : ℝ)|^8467 ≤ (34717070183111/100000000000000 : ℝ)^6419
        have hw : |(3587291/8000000 : ℝ)|=(3587291/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(842453173/2000000000 : ℝ)|^8467 ≤ (7992018590013/25000000000000 : ℝ)^6419
        have hw : |(842453173/2000000000 : ℝ)|=(842453173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10991/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (5430253483530369/50000000000000000000 : ℝ) := by
    have hpowers : (10991/100000 : ℝ)^4233 ≤ (5430253483530369/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10991 : ℕ)^4233*50000000000000000000^1024 ≤ 5430253483530369^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10991 100000 5430253483530369 50000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10991/100000 : ℝ)) (X := (5430253483530369/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14673/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (35856262409376407/100000000000000000000 : ℝ) := by
    have hpowers : (14673/100000 : ℝ)^4233 ≤ (35856262409376407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14673 : ℕ)^4233*100000000000000000000^1024 ≤ 35856262409376407^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14673 100000 35856262409376407 100000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14673/100000 : ℝ)) (X := (35856262409376407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005430253483530369/25000000000000000000 : ℝ) ≤ (5000262703605421/5000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (25005430253483530369/25000000000000000000 : ℝ)^1024 ≤ (5000262703605421/5000000000000000 : ℝ)^4233 := by
      have hnat : (25005430253483530369 : ℕ)^1024*5000000000000000^4233 ≤ 5000262703605421^4233*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005430253483530369 25000000000000000000 5000262703605421 5000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000262703605421/5000000000000000 : ℝ)) (X := (25005430253483530369/25000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009343353875287429/20000000000000000000 : ℝ) ≤ (10001129919752289/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (20009343353875287429/20000000000000000000 : ℝ)^1024 ≤ (10001129919752289/10000000000000000 : ℝ)^4233 := by
      have hnat : (20009343353875287429 : ℕ)^1024*10000000000000000^4233 ≤ 10001129919752289^4233*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009343353875287429 20000000000000000000 10001129919752289 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001129919752289/10000000000000000 : ℝ)) (X := (20009343353875287429/20000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035856262409376407/50000000000000000000 : ℝ) ≤ (1250216804036717/1250000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50035856262409376407/50000000000000000000 : ℝ)^1024 ≤ (1250216804036717/1250000000000000 : ℝ)^4233 := by
      have hnat : (50035856262409376407 : ℕ)^1024*1250000000000000^4233 ≤ 1250216804036717^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035856262409376407 50000000000000000000 1250216804036717 1250000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250216804036717/1250000000000000 : ℝ)) (X := (50035856262409376407/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5430253483530369/50000000000000000000 : ℝ) ≤ ((3680864615466423229/3682000000000000000 : ℝ)+2*(604512541447/368200000000000 : ℝ)*(10991/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (3680864615466423229/3682000000000000000 : ℝ)+2*(604512541447/368200000000000 : ℝ)*(10991/100000 : ℝ)=(5000262703605421/5000000000000000 : ℝ) by norm_num, show 1+2*(5430253483530369/50000000000000000000 : ℝ)=(25005430253483530369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35856262409376407/100000000000000000000 : ℝ)+(5430253483530369/50000000000000000000 : ℝ) ≤ ((3680864615466423229/3682000000000000000 : ℝ)+(604512541447/368200000000000 : ℝ)*((14673/100000 : ℝ)+(10991/100000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (3680864615466423229/3682000000000000000 : ℝ)+(604512541447/368200000000000 : ℝ)*((14673/100000 : ℝ)+(10991/100000 : ℝ))=(10001129919752289/10000000000000000 : ℝ) by norm_num, show 1+(35856262409376407/100000000000000000000 : ℝ)+(5430253483530369/50000000000000000000 : ℝ)=(20009343353875287429/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35856262409376407/100000000000000000000 : ℝ) ≤ ((3680864615466423229/3682000000000000000 : ℝ)+2*(604512541447/368200000000000 : ℝ)*(14673/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (3680864615466423229/3682000000000000000 : ℝ)+2*(604512541447/368200000000000 : ℝ)*(14673/100000 : ℝ)=(1250216804036717/1250000000000000 : ℝ) by norm_num, show 1+2*(35856262409376407/100000000000000000000 : ℝ)=(50035856262409376407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3680864615466423229/3682000000000000000 : ℝ)*(X 1 0+X 2 0)+(604512541447/368200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (10991/100000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (3680864615466423229/3682000000000000000 : ℝ)) (alpha := (604512541447/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3680864615466423229/3682000000000000000 : ℝ)*(X 0 1+X 2 1)+(604512541447/368200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (10991/100000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (3680864615466423229/3682000000000000000 : ℝ)) (alpha := (604512541447/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3680864615466423229/3682000000000000000 : ℝ)*(X 0 2+X 1 2)+(604512541447/368200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (10991/100000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (3680864615466423229/3682000000000000000 : ℝ)) (alpha := (604512541447/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-263103233/1250000000 : ℝ)*X 0 0+(5396237103/10000000000 : ℝ)*X 0 1+(5262313141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345563299/10000000000 : ℝ)*X 1 0+(-10864019/50000000 : ℝ)*X 1 1+(2631156573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069112651/2000000000 : ℝ)*X 2 0+(1052462631/2000000000 : ℝ)*X 2 1+(-2172803847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869222921/2000000000 : ℝ)*X 0 0+(210575571/500000000 : ℝ)*X 0 1+(1121216311/2500000000 : ℝ)*X 0 2+(869222921/2000000000 : ℝ)*X 1 0+(210575571/500000000 : ℝ)*X 1 1+(1121216311/2500000000 : ℝ)*X 1 2+(869222921/2000000000 : ℝ)*X 2 0+(210575571/500000000 : ℝ)*X 2 1+(1121216311/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2104831593/10000000000 : ℝ)*X 0 0+(263134063/500000000 : ℝ)*X 0 1+(5395867673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311320727/10000000000 : ℝ)*X 1 0+(-2039249333/10000000000 : ℝ)*X 1 1+(2697933821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311320969/10000000000 : ℝ)*X 2 0+(5395867381/10000000000 : ℝ)*X 2 1+(-25490617/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((6790823/15625000 : ℝ)*X 0 0+(3587291/8000000 : ℝ)*X 0 1+(842453173/2000000000 : ℝ)*X 0 2+(6790823/15625000 : ℝ)*X 1 0+(3587291/8000000 : ℝ)*X 1 1+(842453173/2000000000 : ℝ)*X 1 2+(6790823/15625000 : ℝ)*X 2 0+(3587291/8000000 : ℝ)*X 2 1+(842453173/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148736498371238782362875793/26300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72728471/6250000000000 : ℝ)*(base19) + (1010950837/100000000000000 : ℝ)*(base23) + (48774539/100000000000000 : ℝ)*(lower2) + (96862823/50000000000000 : ℝ)*(upper3) + (43081459/100000000000000 : ℝ)*(upper5) + (5562638132006091/100000000000000 : ℝ)*(major0) + (5562638132006091/100000000000000 : ℝ)*(major1) + (5562638132006091/100000000000000 : ℝ)*(major2) + (7466956908971747/100000000000000 : ℝ)*(sp0) + (1493396559757941/20000000000000 : ℝ)*(sp1) + (1866745737873601/25000000000000 : ℝ)*(sp2) + (182913783745097/5000000000000 : ℝ)*(sp3) + (13526736747/50000000000000 : ℝ)*(sp4) + (8219076159/50000000000000 : ℝ)*(sp7) + (228643257065891/6250000000000 : ℝ)*(f.failure) + (7466983962445241/100000000000000 : ℝ)*(f.sum) + (5229180146577/18410000000000000000000000000 : ℝ)*base65 + (4941002856595542161/368200000000000000000000000000000 : ℝ)*base68 + (4606016903887142161/368200000000000000000000000000000 : ℝ)*base70 + (5804626551182342161/368200000000000000000000000000000 : ℝ)*base72 + (35770589249323/18410000000000000000000000000 : ℝ)*base74 + (6019232990803342161/368200000000000000000000000000000 : ℝ)*base76 + (3850768915627342161/368200000000000000000000000000000 : ℝ)*base78 + (4778049775195342161/368200000000000000000000000000000 : ℝ)*base80 + (149591849161543/18410000000000000000000000000 : ℝ)*base82 + (2012727/625000000000000000000 : ℝ)*base90 + (2012727/625000000000000000000 : ℝ)*base92 + (2012727/625000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243779098308186709414941111/26300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (676591511/50000000000000 : ℝ)*(base19) + (2160638711/100000000000000 : ℝ)*(base23) + (7985499/25000000000000 : ℝ)*(upper3) + (286517/125000000000 : ℝ)*(lower4) + (106769167/50000000000000 : ℝ)*(upper5) + (5593401616899929/100000000000000 : ℝ)*(major0) + (5593401616899929/100000000000000 : ℝ)*(major1) + (5593401616899929/100000000000000 : ℝ)*(major2) + (2657181761/6250000000000 : ℝ)*(sp1) + (382062561/800000000000 : ℝ)*(sp2) + (7508279077929357/100000000000000 : ℝ)*(sp4) + (7508235209838159/100000000000000 : ℝ)*(sp5) + (7508229159470521/100000000000000 : ℝ)*(sp6) + (459815480862281/12500000000000 : ℝ)*(sp7) + (459815480862281/12500000000000 : ℝ)*(f.failure) + (7508279077929357/100000000000000 : ℝ)*(f.sum) + (16359857420439/2630000000000000000000000000 : ℝ)*base65 + (189530640899617037/52600000000000000000000000000000 : ℝ)*base68 + (493752776551782963/52600000000000000000000000000000 : ℝ)*base69 + (111226640762182963/52600000000000000000000000000000 : ℝ)*base71 + (12817425224219/2630000000000000000000000000 : ℝ)*base73 + (886219443967982963/52600000000000000000000000000000 : ℝ)*base75 + (311220134106017037/52600000000000000000000000000000 : ℝ)*base78 + (193477834154782963/52600000000000000000000000000000 : ℝ)*base79 + (13102980546059/2630000000000000000000000000 : ℝ)*base81 + (15089557/1250000000000000000000 : ℝ)*base90 + (15089557/1250000000000000000000 : ℝ)*base92 + (15089557/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1273_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1273_s5_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-26315333/125000000 : ℝ)*x 0 + (215666063/400000000 : ℝ)*x 1 + (2633317601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26315333/125000000 : ℝ)^8467 ≤ (3201366994913/25000000000000 : ℝ)^6419 := by
    have hnat : (26315333 : ℕ)^8467*25000000000000^6419 ≤ 3201366994913^6419*125000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26315333 125000000 3201366994913 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215666063/400000000 : ℝ)^8467 ≤ (44271772588971/100000000000000 : ℝ)^6419 := by
    have hnat : (215666063 : ℕ)^8467*100000000000000^6419 ≤ 44271772588971^6419*400000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215666063 400000000 44271772588971 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633317601/5000000000 : ℝ)^8467 ≤ (8584551882263/20000000000000 : ℝ)^6419 := by
    have hnat : (2633317601 : ℕ)^8467*20000000000000^6419 ≤ 8584551882263^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633317601 5000000000 8584551882263 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26315333/125000000 : ℝ), (215666063/400000000 : ℝ), (2633317601/5000000000 : ℝ)] ![(3201366994913/25000000000000 : ℝ), (44271772588971/100000000000000 : ℝ), (8584551882263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26315333/125000000 : ℝ)|^8467 ≤ (3201366994913/25000000000000 : ℝ)^6419
        have hw : |(-26315333/125000000 : ℝ)|=(26315333/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215666063/400000000 : ℝ)|^8467 ≤ (44271772588971/100000000000000 : ℝ)^6419
        have hw : |(215666063/400000000 : ℝ)|=(215666063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633317601/5000000000 : ℝ)|^8467 ≤ (8584551882263/20000000000000 : ℝ)^6419
        have hw : |(2633317601/5000000000 : ℝ)|=(2633317601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s5_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344401039/10000000000 : ℝ)*x 0 + (-67769349/312500000 : ℝ)*x 1 + (5266635331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344401039/10000000000 : ℝ)^8467 ≤ (8752144088053/20000000000000 : ℝ)^6419 := by
    have hnat : (5344401039 : ℕ)^8467*20000000000000^6419 ≤ 8752144088053^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344401039 10000000000 8752144088053 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67769349/312500000 : ℝ)^8467 ≤ (13316518746751/100000000000000 : ℝ)^6419 := by
    have hnat : (67769349 : ℕ)^8467*100000000000000^6419 ≤ 13316518746751^6419*312500000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67769349 312500000 13316518746751 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266635331/10000000000 : ℝ)^8467 ≤ (42922760798091/100000000000000 : ℝ)^6419 := by
    have hnat : (5266635331 : ℕ)^8467*100000000000000^6419 ≤ 42922760798091^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266635331 10000000000 42922760798091 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344401039/10000000000 : ℝ), (-67769349/312500000 : ℝ), (5266635331/10000000000 : ℝ)] ![(8752144088053/20000000000000 : ℝ), (13316518746751/100000000000000 : ℝ), (42922760798091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344401039/10000000000 : ℝ)|^8467 ≤ (8752144088053/20000000000000 : ℝ)^6419
        have hw : |(5344401039/10000000000 : ℝ)|=(5344401039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67769349/312500000 : ℝ)|^8467 ≤ (13316518746751/100000000000000 : ℝ)^6419
        have hw : |(-67769349/312500000 : ℝ)|=(67769349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266635331/10000000000 : ℝ)|^8467 ≤ (42922760798091/100000000000000 : ℝ)^6419
        have hw : |(5266635331/10000000000 : ℝ)|=(5266635331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s5_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336100141/2500000000 : ℝ)*x 0 + (5266635961/10000000000 : ℝ)*x 1 + (-1084309483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336100141/2500000000 : ℝ)^8467 ≤ (1367522353437/3125000000000 : ℝ)^6419 := by
    have hnat : (1336100141 : ℕ)^8467*3125000000000^6419 ≤ 1367522353437^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336100141 2500000000 1367522353437 3125000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266635961/10000000000 : ℝ)^8467 ≤ (21461383785359/50000000000000 : ℝ)^6419 := by
    have hnat : (5266635961 : ℕ)^8467*50000000000000^6419 ≤ 21461383785359^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266635961 10000000000 21461383785359 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084309483/5000000000 : ℝ)^8467 ≤ (13316517110609/100000000000000 : ℝ)^6419 := by
    have hnat : (1084309483 : ℕ)^8467*100000000000000^6419 ≤ 13316517110609^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084309483 5000000000 13316517110609 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336100141/2500000000 : ℝ), (5266635961/10000000000 : ℝ), (-1084309483/5000000000 : ℝ)] ![(1367522353437/3125000000000 : ℝ), (21461383785359/50000000000000 : ℝ), (13316517110609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336100141/2500000000 : ℝ)|^8467 ≤ (1367522353437/3125000000000 : ℝ)^6419
        have hw : |(1336100141/2500000000 : ℝ)|=(1336100141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266635961/10000000000 : ℝ)|^8467 ≤ (21461383785359/50000000000000 : ℝ)^6419
        have hw : |(5266635961/10000000000 : ℝ)|=(5266635961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1084309483/5000000000 : ℝ)|^8467 ≤ (13316517110609/100000000000000 : ℝ)^6419
        have hw : |(-1084309483/5000000000 : ℝ)|=(1084309483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s5_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173175537/5000000000 : ℝ)*x 0 + (4220573183/10000000000 : ℝ)*x 1 + (2237871683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173175537/5000000000 : ℝ)^8467 ≤ (33317123923409/100000000000000 : ℝ)^6419 := by
    have hnat : (2173175537 : ℕ)^8467*100000000000000^6419 ≤ 33317123923409^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173175537 5000000000 33317123923409 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4220573183/10000000000 : ℝ)^8467 ≤ (32051262281667/100000000000000 : ℝ)^6419 := by
    have hnat : (4220573183 : ℕ)^8467*100000000000000^6419 ≤ 32051262281667^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220573183 10000000000 32051262281667 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237871683/5000000000 : ℝ)^8467 ≤ (17315806889669/50000000000000 : ℝ)^6419 := by
    have hnat : (2237871683 : ℕ)^8467*50000000000000^6419 ≤ 17315806889669^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237871683 5000000000 17315806889669 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173175537/5000000000 : ℝ), (4220573183/10000000000 : ℝ), (2237871683/5000000000 : ℝ)] ![(33317123923409/100000000000000 : ℝ), (32051262281667/100000000000000 : ℝ), (17315806889669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173175537/5000000000 : ℝ)|^8467 ≤ (33317123923409/100000000000000 : ℝ)^6419
        have hw : |(2173175537/5000000000 : ℝ)|=(2173175537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4220573183/10000000000 : ℝ)|^8467 ≤ (32051262281667/100000000000000 : ℝ)^6419
        have hw : |(4220573183/10000000000 : ℝ)|=(4220573183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237871683/5000000000 : ℝ)|^8467 ≤ (17315806889669/50000000000000 : ℝ)^6419
        have hw : |(2237871683/5000000000 : ℝ)|=(2237871683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s5_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052615569/5000000000 : ℝ)*x 0 + (5266956707/10000000000 : ℝ)*x 1 + (539132913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052615569/5000000000 : ℝ)^8467 ≤ (6402752034473/50000000000000 : ℝ)^6419 := by
    have hnat : (1052615569 : ℕ)^8467*50000000000000^6419 ≤ 6402752034473^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052615569 5000000000 6402752034473 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266956707/10000000000 : ℝ)^8467 ≤ (21463107844157/50000000000000 : ℝ)^6419 := by
    have hnat : (5266956707 : ℕ)^8467*50000000000000^6419 ≤ 21463107844157^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266956707 10000000000 21463107844157 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539132913/1000000000 : ℝ)^8467 ≤ (44268280230787/100000000000000 : ℝ)^6419 := by
    have hnat : (539132913 : ℕ)^8467*100000000000000^6419 ≤ 44268280230787^6419*1000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539132913 1000000000 44268280230787 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052615569/5000000000 : ℝ), (5266956707/10000000000 : ℝ), (539132913/1000000000 : ℝ)] ![(6402752034473/50000000000000 : ℝ), (21463107844157/50000000000000 : ℝ), (44268280230787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052615569/5000000000 : ℝ)|^8467 ≤ (6402752034473/50000000000000 : ℝ)^6419
        have hw : |(-1052615569/5000000000 : ℝ)|=(1052615569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266956707/10000000000 : ℝ)|^8467 ≤ (21463107844157/50000000000000 : ℝ)^6419
        have hw : |(5266956707/10000000000 : ℝ)|=(5266956707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539132913/1000000000 : ℝ)|^8467 ≤ (44268280230787/100000000000000 : ℝ)^6419
        have hw : |(539132913/1000000000 : ℝ)|=(539132913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s5_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062486861/2000000000 : ℝ)*x 0 + (-1021963079/5000000000 : ℝ)*x 1 + (2695664559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062486861/2000000000 : ℝ)^8467 ≤ (43415790640837/100000000000000 : ℝ)^6419 := by
    have hnat : (1062486861 : ℕ)^8467*100000000000000^6419 ≤ 43415790640837^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062486861 2000000000 43415790640837 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021963079/5000000000 : ℝ)^8467 ≤ (3078982312789/25000000000000 : ℝ)^6419 := by
    have hnat : (1021963079 : ℕ)^8467*25000000000000^6419 ≤ 3078982312789^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021963079 5000000000 3078982312789 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695664559/5000000000 : ℝ)^8467 ≤ (22134140050409/50000000000000 : ℝ)^6419 := by
    have hnat : (2695664559 : ℕ)^8467*50000000000000^6419 ≤ 22134140050409^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695664559 5000000000 22134140050409 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062486861/2000000000 : ℝ), (-1021963079/5000000000 : ℝ), (2695664559/5000000000 : ℝ)] ![(43415790640837/100000000000000 : ℝ), (3078982312789/25000000000000 : ℝ), (22134140050409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062486861/2000000000 : ℝ)|^8467 ≤ (43415790640837/100000000000000 : ℝ)^6419
        have hw : |(1062486861/2000000000 : ℝ)|=(1062486861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021963079/5000000000 : ℝ)|^8467 ≤ (3078982312789/25000000000000 : ℝ)^6419
        have hw : |(-1021963079/5000000000 : ℝ)|=(1021963079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695664559/5000000000 : ℝ)|^8467 ≤ (22134140050409/50000000000000 : ℝ)^6419
        have hw : |(2695664559/5000000000 : ℝ)|=(2695664559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s5_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312434317/10000000000 : ℝ)*x 0 + (2695664557/5000000000 : ℝ)*x 1 + (-2043926147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312434317/10000000000 : ℝ)^8467 ≤ (43415790770197/100000000000000 : ℝ)^6419 := by
    have hnat : (5312434317 : ℕ)^8467*100000000000000^6419 ≤ 43415790770197^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312434317 10000000000 43415790770197 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695664557/5000000000 : ℝ)^8467 ≤ (8853656011499/20000000000000 : ℝ)^6419 := by
    have hnat : (2695664557 : ℕ)^8467*20000000000000^6419 ≤ 8853656011499^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695664557 5000000000 8853656011499 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043926147/10000000000 : ℝ)^8467 ≤ (12315929163727/100000000000000 : ℝ)^6419 := by
    have hnat : (2043926147 : ℕ)^8467*100000000000000^6419 ≤ 12315929163727^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043926147 10000000000 12315929163727 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312434317/10000000000 : ℝ), (2695664557/5000000000 : ℝ), (-2043926147/10000000000 : ℝ)] ![(43415790770197/100000000000000 : ℝ), (8853656011499/20000000000000 : ℝ), (12315929163727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312434317/10000000000 : ℝ)|^8467 ≤ (43415790770197/100000000000000 : ℝ)^6419
        have hw : |(5312434317/10000000000 : ℝ)|=(5312434317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695664557/5000000000 : ℝ)|^8467 ≤ (8853656011499/20000000000000 : ℝ)^6419
        have hw : |(2695664557/5000000000 : ℝ)|=(2695664557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2043926147/10000000000 : ℝ)|^8467 ≤ (12315929163727/100000000000000 : ℝ)^6419
        have hw : |(-2043926147/10000000000 : ℝ)|=(2043926147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s5_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346360873/10000000000 : ℝ)*x 0 + (4475088521/10000000000 : ℝ)*x 1 + (844246097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346360873/10000000000 : ℝ)^8467 ≤ (4164652875449/12500000000000 : ℝ)^6419 := by
    have hnat : (4346360873 : ℕ)^8467*12500000000000^6419 ≤ 4164652875449^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346360873 10000000000 4164652875449 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475088521/10000000000 : ℝ)^8467 ≤ (17312465184579/50000000000000 : ℝ)^6419 := by
    have hnat : (4475088521 : ℕ)^8467*50000000000000^6419 ≤ 17312465184579^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475088521 10000000000 17312465184579 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844246097/2000000000 : ℝ)^8467 ≤ (16028923306143/50000000000000 : ℝ)^6419 := by
    have hnat : (844246097 : ℕ)^8467*50000000000000^6419 ≤ 16028923306143^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844246097 2000000000 16028923306143 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346360873/10000000000 : ℝ), (4475088521/10000000000 : ℝ), (844246097/2000000000 : ℝ)] ![(4164652875449/12500000000000 : ℝ), (17312465184579/50000000000000 : ℝ), (16028923306143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346360873/10000000000 : ℝ)|^8467 ≤ (4164652875449/12500000000000 : ℝ)^6419
        have hw : |(4346360873/10000000000 : ℝ)|=(4346360873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475088521/10000000000 : ℝ)|^8467 ≤ (17312465184579/50000000000000 : ℝ)^6419
        have hw : |(4475088521/10000000000 : ℝ)|=(4475088521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844246097/2000000000 : ℝ)|^8467 ≤ (16028923306143/50000000000000 : ℝ)^6419
        have hw : |(844246097/2000000000 : ℝ)|=(844246097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2299/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (442/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11403/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (6322458310098999/50000000000000000000 : ℝ) := by
    have hpowers : (11403/100000 : ℝ)^4233 ≤ (6322458310098999/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11403 : ℕ)^4233*50000000000000000000^1024 ≤ 6322458310098999^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11403 100000 6322458310098999 50000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11403/100000 : ℝ)) (X := (6322458310098999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (4233/1024 : ℝ) ≤ (15840134196902119/50000000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^4233 ≤ (15840134196902119/50000000000000000000 : ℝ)^1024 := by
      have hnat : (89 : ℕ)^4233*50000000000000000000^1024 ≤ 15840134196902119^1024*625^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 15840134196902119 50000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (15840134196902119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006322458310098999/25000000000000000000 : ℝ) ≤ (10000611724713911/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (25006322458310098999/25000000000000000000 : ℝ)^1024 ≤ (10000611724713911/10000000000000000 : ℝ)^4233 := by
      have hnat : (25006322458310098999 : ℕ)^1024*10000000000000000^4233 ≤ 10000611724713911^4233*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006322458310098999 25000000000000000000 10000611724713911 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000611724713911/10000000000000000 : ℝ)) (X := (25006322458310098999/25000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011081296253500559/25000000000000000000 : ℝ) ≤ (10001072085176229/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (25011081296253500559/25000000000000000000 : ℝ)^1024 ≤ (10001072085176229/10000000000000000 : ℝ)^4233 := by
      have hnat : (25011081296253500559 : ℕ)^1024*10000000000000000^4233 ≤ 10001072085176229^4233*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011081296253500559 25000000000000000000 10001072085176229 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001072085176229/10000000000000000 : ℝ)) (X := (25011081296253500559/25000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015840134196902119/25000000000000000000 : ℝ) ≤ (10001532445638547/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (25015840134196902119/25000000000000000000 : ℝ)^1024 ≤ (10001532445638547/10000000000000000 : ℝ)^4233 := by
      have hnat : (25015840134196902119 : ℕ)^1024*10000000000000000^4233 ≤ 10001532445638547^4233*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015840134196902119 25000000000000000000 10001532445638547 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001532445638547/10000000000000000 : ℝ)) (X := (25015840134196902119/25000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6322458310098999/50000000000000000000 : ℝ) ≤ ((28361236482309741199/28370000000000000000 : ℝ)+2*(230180231159/141850000000000 : ℝ)*(11403/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (28361236482309741199/28370000000000000000 : ℝ)+2*(230180231159/141850000000000 : ℝ)*(11403/100000 : ℝ)=(10000611724713911/10000000000000000 : ℝ) by norm_num, show 1+2*(6322458310098999/50000000000000000000 : ℝ)=(25006322458310098999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15840134196902119/50000000000000000000 : ℝ)+(6322458310098999/50000000000000000000 : ℝ) ≤ ((28361236482309741199/28370000000000000000 : ℝ)+(230180231159/141850000000000 : ℝ)*((89/625 : ℝ)+(11403/100000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (28361236482309741199/28370000000000000000 : ℝ)+(230180231159/141850000000000 : ℝ)*((89/625 : ℝ)+(11403/100000 : ℝ))=(10001072085176229/10000000000000000 : ℝ) by norm_num, show 1+(15840134196902119/50000000000000000000 : ℝ)+(6322458310098999/50000000000000000000 : ℝ)=(25011081296253500559/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15840134196902119/50000000000000000000 : ℝ) ≤ ((28361236482309741199/28370000000000000000 : ℝ)+2*(230180231159/141850000000000 : ℝ)*(89/625 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (28361236482309741199/28370000000000000000 : ℝ)+2*(230180231159/141850000000000 : ℝ)*(89/625 : ℝ)=(10001532445638547/10000000000000000 : ℝ) by norm_num, show 1+2*(15840134196902119/50000000000000000000 : ℝ)=(25015840134196902119/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28361236482309741199/28370000000000000000 : ℝ)*(X 1 0+X 2 0)+(230180231159/141850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (89/625 : ℝ)) (c := (28361236482309741199/28370000000000000000 : ℝ)) (alpha := (230180231159/141850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28361236482309741199/28370000000000000000 : ℝ)*(X 0 1+X 2 1)+(230180231159/141850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (89/625 : ℝ)) (c := (28361236482309741199/28370000000000000000 : ℝ)) (alpha := (230180231159/141850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28361236482309741199/28370000000000000000 : ℝ)*(X 0 2+X 1 2)+(230180231159/141850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (89/625 : ℝ)) (c := (28361236482309741199/28370000000000000000 : ℝ)) (alpha := (230180231159/141850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-26315333/125000000 : ℝ)*X 0 0+(215666063/400000000 : ℝ)*X 0 1+(2633317601/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344401039/10000000000 : ℝ)*X 1 0+(-67769349/312500000 : ℝ)*X 1 1+(5266635331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336100141/2500000000 : ℝ)*X 2 0+(5266635961/10000000000 : ℝ)*X 2 1+(-1084309483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173175537/5000000000 : ℝ)*X 0 0+(4220573183/10000000000 : ℝ)*X 0 1+(2237871683/5000000000 : ℝ)*X 0 2+(2173175537/5000000000 : ℝ)*X 1 0+(4220573183/10000000000 : ℝ)*X 1 1+(2237871683/5000000000 : ℝ)*X 1 2+(2173175537/5000000000 : ℝ)*X 2 0+(4220573183/10000000000 : ℝ)*X 2 1+(2237871683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1052615569/5000000000 : ℝ)*X 0 0+(5266956707/10000000000 : ℝ)*X 0 1+(539132913/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062486861/2000000000 : ℝ)*X 1 0+(-1021963079/5000000000 : ℝ)*X 1 1+(2695664559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312434317/10000000000 : ℝ)*X 2 0+(2695664557/5000000000 : ℝ)*X 2 1+(-2043926147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346360873/10000000000 : ℝ)*X 0 0+(4475088521/10000000000 : ℝ)*X 0 1+(844246097/2000000000 : ℝ)*X 0 2+(4346360873/10000000000 : ℝ)*X 1 0+(4475088521/10000000000 : ℝ)*X 1 1+(844246097/2000000000 : ℝ)*X 1 2+(4346360873/10000000000 : ℝ)*X 2 0+(4475088521/10000000000 : ℝ)*X 2 1+(844246097/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91987317602654300732916087/70925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3222703901/100000000000000 : ℝ)*(base19) + (2099073083/100000000000000 : ℝ)*(base23) + (211165243/100000000000000 : ℝ)*(upper3) + (110276113/50000000000000 : ℝ)*(upper4) + (119526261/100000000000000 : ℝ)*(upper5) + (297955412683943/5000000000000 : ℝ)*(major0) + (297955412683943/5000000000000 : ℝ)*(major1) + (297955412683943/5000000000000 : ℝ)*(major2) + (1599814090348597/20000000000000 : ℝ)*(sp0) + (3999590451589809/50000000000000 : ℝ)*(sp1) + (1999795506702609/25000000000000 : ℝ)*(sp2) + (489874058659343/12500000000000 : ℝ)*(sp3) + (56837070267/50000000000000 : ℝ)*(sp4) + (2491810453/6250000000000 : ℝ)*(sp7) + (489879042280249/12500000000000 : ℝ)*(f.failure) + (7999184125883519/100000000000000 : ℝ)*(f.sum) + (119246088311/141850000000000000000000000 : ℝ)*base66 + (2631714971025217657/141850000000000000000000000000000 : ℝ)*base67 + (1629494548538367657/141850000000000000000000000000000 : ℝ)*base69 + (97093440145567657/141850000000000000000000000000000 : ℝ)*base71 + (982840929071/177312500000000000000000000 : ℝ)*base74 + (115618840207567657/141850000000000000000000000000000 : ℝ)*base75 + (1737352821681867657/141850000000000000000000000000000 : ℝ)*base77 + (2094759373651667657/141850000000000000000000000000000 : ℝ)*base79 + (472735789/709250000000000000000000 : ℝ)*base82 + (6685147/1250000000000000000000 : ℝ)*base89 + (6685147/1250000000000000000000 : ℝ)*base91 + (6685147/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3951267485869687599820992393/354625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387915509/20000000000000 : ℝ)*(base19) + (1080447187/50000000000000 : ℝ)*(base23) + (21653959/10000000000000 : ℝ)*(upper3) + (22709753/25000000000000 : ℝ)*(lower4) + (11362931/5000000000000 : ℝ)*(upper5) + (1497446860201331/25000000000000 : ℝ)*(major0) + (1497446860201331/25000000000000 : ℝ)*(major1) + (1497446860201331/25000000000000 : ℝ)*(major2) + (3346695549/6250000000000 : ℝ)*(sp1) + (1840401609/3125000000000 : ℝ)*(sp2) + (8040365876898761/100000000000000 : ℝ)*(sp4) + (8040310390192431/100000000000000 : ℝ)*(sp5) + (4020152411576449/50000000000000 : ℝ)*(sp6) + (984802158327129/25000000000000 : ℝ)*(sp7) + (984802158327129/25000000000000 : ℝ)*(f.failure) + (8040365876898761/100000000000000 : ℝ)*(f.sum) + (2292791146109/7092500000000000000000000000 : ℝ)*base66 + (1246205793088385869/709250000000000000000000000000000 : ℝ)*base67 + (366002905913635869/709250000000000000000000000000000 : ℝ)*base69 + (2654783847244614131/709250000000000000000000000000000 : ℝ)*base72 + (15208459178611/7092500000000000000000000000 : ℝ)*base73 + (8838160523267635869/709250000000000000000000000000000 : ℝ)*base75 + (8099937133085635869/709250000000000000000000000000000 : ℝ)*base77 + (3849820929906864131/709250000000000000000000000000000 : ℝ)*base80 + (32796856279739/7092500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (28646213/2500000000000000000000 : ℝ)*base90 + (28646213/2500000000000000000000 : ℝ)*base92 + (28646213/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1273_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (442/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1273_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (442/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1273_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1273_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1273_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (442/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1273_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
