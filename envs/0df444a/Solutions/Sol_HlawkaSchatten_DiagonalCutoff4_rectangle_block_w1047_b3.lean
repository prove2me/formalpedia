-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:52:59.743319+00:00
-- url     : https://prove2.me/submissions/dc046feb-59bb-4157-8ca9-aca8ba5ad330

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
theorem support_rectangle_w1047_s9_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106580209/5000000000 : ℝ)*x 0 + (5394661271/10000000000 : ℝ)*x 1 + (1052824537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106580209/5000000000 : ℝ)^515 ≤ (2687858041923/20000000000000 : ℝ)^387 := by
    have hnat : (1106580209 : ℕ)^515*20000000000000^387 ≤ 2687858041923^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106580209 5000000000 2687858041923 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394661271/10000000000 : ℝ)^515 ≤ (10996424967973/25000000000000 : ℝ)^387 := by
    have hnat : (5394661271 : ℕ)^515*25000000000000^387 ≤ 10996424967973^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394661271 10000000000 10996424967973 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052824537/2000000000 : ℝ)^515 ≤ (42575009901151/100000000000000 : ℝ)^387 := by
    have hnat : (1052824537 : ℕ)^515*100000000000000^387 ≤ 42575009901151^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052824537 2000000000 42575009901151 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106580209/5000000000 : ℝ), (5394661271/10000000000 : ℝ), (1052824537/2000000000 : ℝ)] ![(2687858041923/20000000000000 : ℝ), (10996424967973/25000000000000 : ℝ), (42575009901151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106580209/5000000000 : ℝ)|^515 ≤ (2687858041923/20000000000000 : ℝ)^387
        have hw : |(-1106580209/5000000000 : ℝ)|=(1106580209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394661271/10000000000 : ℝ)|^515 ≤ (10996424967973/25000000000000 : ℝ)^387
        have hw : |(5394661271/10000000000 : ℝ)|=(5394661271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052824537/2000000000 : ℝ)|^515 ≤ (42575009901151/100000000000000 : ℝ)^387
        have hw : |(1052824537/2000000000 : ℝ)|=(1052824537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s9_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336253301/2500000000 : ℝ)*x 0 + (-455879257/2000000000 : ℝ)*x 1 + (2632061347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336253301/2500000000 : ℝ)^515 ≤ (43447822738619/100000000000000 : ℝ)^387 := by
    have hnat : (1336253301 : ℕ)^515*100000000000000^387 ≤ 43447822738619^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336253301 2500000000 43447822738619 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455879257/2000000000 : ℝ)^515 ≤ (13977167244109/100000000000000 : ℝ)^387 := by
    have hnat : (455879257 : ℕ)^515*100000000000000^387 ≤ 13977167244109^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455879257 2000000000 13977167244109 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632061347/5000000000 : ℝ)^515 ≤ (665234531219/1562500000000 : ℝ)^387 := by
    have hnat : (2632061347 : ℕ)^515*1562500000000^387 ≤ 665234531219^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632061347 5000000000 665234531219 1562500000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336253301/2500000000 : ℝ), (-455879257/2000000000 : ℝ), (2632061347/5000000000 : ℝ)] ![(43447822738619/100000000000000 : ℝ), (13977167244109/100000000000000 : ℝ), (665234531219/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336253301/2500000000 : ℝ)|^515 ≤ (43447822738619/100000000000000 : ℝ)^387
        have hw : |(1336253301/2500000000 : ℝ)|=(1336253301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-455879257/2000000000 : ℝ)|^515 ≤ (13977167244109/100000000000000 : ℝ)^387
        have hw : |(-455879257/2000000000 : ℝ)|=(455879257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632061347/5000000000 : ℝ)|^515 ≤ (665234531219/1562500000000 : ℝ)^387
        have hw : |(2632061347/5000000000 : ℝ)|=(2632061347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s9_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-276645707/1250000000 : ℝ)*x 0 + (105288973/200000000 : ℝ)*x 1 + (1348583507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276645707/1250000000 : ℝ)^515 ≤ (13439332537383/100000000000000 : ℝ)^387 := by
    have hnat : (276645707 : ℕ)^515*100000000000000^387 ≤ 13439332537383^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276645707 1250000000 13439332537383 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105288973/200000000 : ℝ)^515 ≤ (42578518231153/100000000000000 : ℝ)^387 := by
    have hnat : (105288973 : ℕ)^515*100000000000000^387 ≤ 42578518231153^387*200000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105288973 200000000 42578518231153 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348583507/2500000000 : ℝ)^515 ≤ (8796429841543/20000000000000 : ℝ)^387 := by
    have hnat : (1348583507 : ℕ)^515*20000000000000^387 ≤ 8796429841543^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348583507 2500000000 8796429841543 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276645707/1250000000 : ℝ), (105288973/200000000 : ℝ), (1348583507/2500000000 : ℝ)] ![(13439332537383/100000000000000 : ℝ), (42578518231153/100000000000000 : ℝ), (8796429841543/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276645707/1250000000 : ℝ)|^515 ≤ (13439332537383/100000000000000 : ℝ)^387
        have hw : |(-276645707/1250000000 : ℝ)|=(276645707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105288973/200000000 : ℝ)|^515 ≤ (42578518231153/100000000000000 : ℝ)^387
        have hw : |(105288973/200000000 : ℝ)|=(105288973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348583507/2500000000 : ℝ)|^515 ≤ (8796429841543/20000000000000 : ℝ)^387
        have hw : |(1348583507/2500000000 : ℝ)|=(1348583507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s9_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312183329/10000000000 : ℝ)*x 0 + (-2149185419/10000000000 : ℝ)*x 1 + (674291667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312183329/10000000000 : ℝ)^515 ≤ (43093056110213/100000000000000 : ℝ)^387 := by
    have hnat : (5312183329 : ℕ)^515*100000000000000^387 ≤ 43093056110213^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312183329 10000000000 43093056110213 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149185419/10000000000 : ℝ)^515 ≤ (6462401085383/50000000000000 : ℝ)^387 := by
    have hnat : (2149185419 : ℕ)^515*50000000000000^387 ≤ 6462401085383^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149185419 10000000000 6462401085383 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674291667/1250000000 : ℝ)^515 ≤ (21991070849713/50000000000000 : ℝ)^387 := by
    have hnat : (674291667 : ℕ)^515*50000000000000^387 ≤ 21991070849713^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674291667 1250000000 21991070849713 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312183329/10000000000 : ℝ), (-2149185419/10000000000 : ℝ), (674291667/1250000000 : ℝ)] ![(43093056110213/100000000000000 : ℝ), (6462401085383/50000000000000 : ℝ), (21991070849713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312183329/10000000000 : ℝ)|^515 ≤ (43093056110213/100000000000000 : ℝ)^387
        have hw : |(5312183329/10000000000 : ℝ)|=(5312183329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149185419/10000000000 : ℝ)|^515 ≤ (6462401085383/50000000000000 : ℝ)^387
        have hw : |(-2149185419/10000000000 : ℝ)|=(2149185419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674291667/1250000000 : ℝ)|^515 ≤ (21991070849713/50000000000000 : ℝ)^387
        have hw : |(674291667/1250000000 : ℝ)|=(674291667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s9_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (664022897/1250000000 : ℝ)*x 0 + (8630933/16000000 : ℝ)*x 1 + (-2149185911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664022897/1250000000 : ℝ)^515 ≤ (10773263614637/25000000000000 : ℝ)^387 := by
    have hnat : (664022897 : ℕ)^515*25000000000000^387 ≤ 10773263614637^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664022897 1250000000 10773263614637 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8630933/16000000 : ℝ)^515 ≤ (879642788201/2000000000000 : ℝ)^387 := by
    have hnat : (8630933 : ℕ)^515*2000000000000^387 ≤ 879642788201^387*16000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8630933 16000000 879642788201 2000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149185911/10000000000 : ℝ)^515 ≤ (6462403054091/50000000000000 : ℝ)^387 := by
    have hnat : (2149185911 : ℕ)^515*50000000000000^387 ≤ 6462403054091^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149185911 10000000000 6462403054091 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664022897/1250000000 : ℝ), (8630933/16000000 : ℝ), (-2149185911/10000000000 : ℝ)] ![(10773263614637/25000000000000 : ℝ), (879642788201/2000000000000 : ℝ), (6462403054091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664022897/1250000000 : ℝ)|^515 ≤ (10773263614637/25000000000000 : ℝ)^387
        have hw : |(664022897/1250000000 : ℝ)|=(664022897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8630933/16000000 : ℝ)|^515 ≤ (879642788201/2000000000000 : ℝ)^387
        have hw : |(8630933/16000000 : ℝ)|=(8630933/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149185911/10000000000 : ℝ)|^515 ≤ (6462403054091/50000000000000 : ℝ)^387
        have hw : |(-2149185911/10000000000 : ℝ)|=(2149185911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s9_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (218912117/500000000 : ℝ)*x 0 + (2253459751/5000000000 : ℝ)*x 1 + (850664943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218912117/500000000 : ℝ)^515 ≤ (33316543325819/100000000000000 : ℝ)^387 := by
    have hnat : (218912117 : ℕ)^515*100000000000000^387 ≤ 33316543325819^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218912117 500000000 33316543325819 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253459751/5000000000 : ℝ)^515 ≤ (34625875970639/100000000000000 : ℝ)^387 := by
    have hnat : (2253459751 : ℕ)^515*100000000000000^387 ≤ 34625875970639^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253459751 5000000000 34625875970639 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850664943/2000000000 : ℝ)^515 ≤ (16028790342623/50000000000000 : ℝ)^387 := by
    have hnat : (850664943 : ℕ)^515*50000000000000^387 ≤ 16028790342623^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850664943 2000000000 16028790342623 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218912117/500000000 : ℝ), (2253459751/5000000000 : ℝ), (850664943/2000000000 : ℝ)] ![(33316543325819/100000000000000 : ℝ), (34625875970639/100000000000000 : ℝ), (16028790342623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218912117/500000000 : ℝ)|^515 ≤ (33316543325819/100000000000000 : ℝ)^387
        have hw : |(218912117/500000000 : ℝ)|=(218912117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253459751/5000000000 : ℝ)|^515 ≤ (34625875970639/100000000000000 : ℝ)^387
        have hw : |(2253459751/5000000000 : ℝ)|=(2253459751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850664943/2000000000 : ℝ)|^515 ≤ (16028790342623/50000000000000 : ℝ)^387
        have hw : |(850664943/2000000000 : ℝ)|=(850664943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (449/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1399/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (449/4000 : ℝ) ^ (8239/2048 : ℝ) ≤ (15098990694742767/100000000000000000000 : ℝ) := by
    have hpowers : (449/4000 : ℝ)^8239 ≤ (15098990694742767/100000000000000000000 : ℝ)^2048 := by
      have hnat : (449 : ℕ)^8239*100000000000000000000^2048 ≤ 15098990694742767^2048*4000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        449 4000 15098990694742767 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (449/4000 : ℝ)) (X := (15098990694742767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13991/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (4578286175012813/12500000000000000000 : ℝ) := by
    have hpowers : (13991/100000 : ℝ)^8239 ≤ (4578286175012813/12500000000000000000 : ℝ)^2048 := by
      have hnat : (13991 : ℕ)^8239*12500000000000000000^2048 ≤ 4578286175012813^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13991 100000 4578286175012813 12500000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13991/100000 : ℝ)) (X := (4578286175012813/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015098990694742767/50000000000000000000 : ℝ) ≤ (2500187639429161/2500000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50015098990694742767/50000000000000000000 : ℝ)^2048 ≤ (2500187639429161/2500000000000000 : ℝ)^8239 := by
      have hnat : (50015098990694742767 : ℕ)^2048*2500000000000000^8239 ≤ 2500187639429161^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015098990694742767 50000000000000000000 2500187639429161 2500000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500187639429161/2500000000000000 : ℝ)) (X := (50015098990694742767/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051725280094845271/100000000000000000000 : ℝ) ≤ (5000642752718177/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (100051725280094845271/100000000000000000000 : ℝ)^2048 ≤ (5000642752718177/5000000000000000 : ℝ)^8239 := by
      have hnat : (100051725280094845271 : ℕ)^2048*5000000000000000^8239 ≤ 5000642752718177^8239*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051725280094845271 100000000000000000000 5000642752718177 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000642752718177/5000000000000000 : ℝ)) (X := (100051725280094845271/100000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254578286175012813/6250000000000000000 : ℝ) ≤ (312556889161127/312500000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (6254578286175012813/6250000000000000000 : ℝ)^2048 ≤ (312556889161127/312500000000000 : ℝ)^8239 := by
      have hnat : (6254578286175012813 : ℕ)^2048*312500000000000^8239 ≤ 312556889161127^8239*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254578286175012813 6250000000000000000 312556889161127 312500000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312556889161127/312500000000000 : ℝ)) (X := (6254578286175012813/6250000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15098990694742767/100000000000000000000 : ℝ) ≤ ((2304172205528062317/2305000000000000000 : ℝ)+2*(17831590657/9220000000000 : ℝ)*(449/4000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (2304172205528062317/2305000000000000000 : ℝ)+2*(17831590657/9220000000000 : ℝ)*(449/4000 : ℝ)=(2500187639429161/2500000000000000 : ℝ) by norm_num, show 1+2*(15098990694742767/100000000000000000000 : ℝ)=(50015098990694742767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4578286175012813/12500000000000000000 : ℝ)+(15098990694742767/100000000000000000000 : ℝ) ≤ ((2304172205528062317/2305000000000000000 : ℝ)+(17831590657/9220000000000 : ℝ)*((13991/100000 : ℝ)+(449/4000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (2304172205528062317/2305000000000000000 : ℝ)+(17831590657/9220000000000 : ℝ)*((13991/100000 : ℝ)+(449/4000 : ℝ))=(5000642752718177/5000000000000000 : ℝ) by norm_num, show 1+(4578286175012813/12500000000000000000 : ℝ)+(15098990694742767/100000000000000000000 : ℝ)=(100051725280094845271/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4578286175012813/12500000000000000000 : ℝ) ≤ ((2304172205528062317/2305000000000000000 : ℝ)+2*(17831590657/9220000000000 : ℝ)*(13991/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (2304172205528062317/2305000000000000000 : ℝ)+2*(17831590657/9220000000000 : ℝ)*(13991/100000 : ℝ)=(312556889161127/312500000000000 : ℝ) by norm_num, show 1+2*(4578286175012813/12500000000000000000 : ℝ)=(6254578286175012813/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2304172205528062317/2305000000000000000 : ℝ)*(X 1 0+X 2 0)+(17831590657/9220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (13991/100000 : ℝ)) (c := (2304172205528062317/2305000000000000000 : ℝ)) (alpha := (17831590657/9220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2304172205528062317/2305000000000000000 : ℝ)*(X 0 1+X 2 1)+(17831590657/9220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (13991/100000 : ℝ)) (c := (2304172205528062317/2305000000000000000 : ℝ)) (alpha := (17831590657/9220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2304172205528062317/2305000000000000000 : ℝ)*(X 0 2+X 1 2)+(17831590657/9220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (13991/100000 : ℝ)) (c := (2304172205528062317/2305000000000000000 : ℝ)) (alpha := (17831590657/9220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106580209/5000000000 : ℝ)*X 0 0+(5394661271/10000000000 : ℝ)*X 0 1+(1052824537/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336253301/2500000000 : ℝ)*X 1 0+(-455879257/2000000000 : ℝ)*X 1 1+(2632061347/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-276645707/1250000000 : ℝ)*X 0 0+(105288973/200000000 : ℝ)*X 0 1+(1348583507/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312183329/10000000000 : ℝ)*X 1 0+(-2149185419/10000000000 : ℝ)*X 1 1+(674291667/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((664022897/1250000000 : ℝ)*X 2 0+(8630933/16000000 : ℝ)*X 2 1+(-2149185911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((218912117/500000000 : ℝ)*X 0 0+(2253459751/5000000000 : ℝ)*X 0 1+(850664943/2000000000 : ℝ)*X 0 2+(218912117/500000000 : ℝ)*X 1 0+(2253459751/5000000000 : ℝ)*X 1 1+(850664943/2000000000 : ℝ)*X 1 2+(218912117/500000000 : ℝ)*X 2 0+(2253459751/5000000000 : ℝ)*X 2 1+(850664943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37267780652673932105984013/28812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147483779/50000000000000 : ℝ)*(base19) + (785926213/100000000000000 : ℝ)*(base23) + (25994973/100000000000000 : ℝ)*(lower1) + (106131591/25000000000000 : ℝ)*(upper2) + (26829339/25000000000000 : ℝ)*(lower3) + (1455306242686163/25000000000000 : ℝ)*(major0) + (1455306242686163/25000000000000 : ℝ)*(major1) + (1455306242686163/25000000000000 : ℝ)*(major2) + (19113086577/50000000000000 : ℝ)*(sp0) + (218565167/1562500000000 : ℝ)*(sp1) + (7699121799040459/100000000000000 : ℝ)*(sp2) + (962393217759421/12500000000000 : ℝ)*(sp3) + (38495796196437/500000000000 : ℝ)*(sp4) + (492911234145049/12500000000000 : ℝ)*(sp5) + (492911234145049/12500000000000 : ℝ)*(f.failure) + (1924790006303403/25000000000000 : ℝ)*(f.sum) + (29090411907/11525000000000000000000000 : ℝ)*base66 + (150372719833130329/57625000000000000000000000000000 : ℝ)*base68 + (110293290342619671/57625000000000000000000000000000 : ℝ)*base69 + (412957618882630329/57625000000000000000000000000000 : ℝ)*base72 + (55317402333/115250000000000000000000000 : ℝ)*base73 + (191167504864630329/57625000000000000000000000000000 : ℝ)*base76 + (43689587249630329/57625000000000000000000000000000 : ℝ)*base78 + (707463230507369671/57625000000000000000000000000000 : ℝ)*base79 + (116618928829/115250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4022269/625000000000000000000 : ℝ)*base89 + (4022269/625000000000000000000 : ℝ)*base91 + (4022269/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1047_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_s10_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-276645493/1250000000 : ℝ)*x 0 + (2697327223/5000000000 : ℝ)*x 1 + (5264126919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276645493/1250000000 : ℝ)^515 ≤ (6719659351437/50000000000000 : ℝ)^387 := by
    have hnat : (276645493 : ℕ)^515*50000000000000^387 ≤ 6719659351437^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276645493 1250000000 6719659351437 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697327223/5000000000 : ℝ)^515 ≤ (5498203227287/12500000000000 : ℝ)^387 := by
    have hnat : (2697327223 : ℕ)^515*12500000000000^387 ≤ 5498203227287^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697327223 5000000000 5498203227287 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264126919/10000000000 : ℝ)^515 ≤ (21287527735413/50000000000000 : ℝ)^387 := by
    have hnat : (5264126919 : ℕ)^515*50000000000000^387 ≤ 21287527735413^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264126919 10000000000 21287527735413 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276645493/1250000000 : ℝ), (2697327223/5000000000 : ℝ), (5264126919/10000000000 : ℝ)] ![(6719659351437/50000000000000 : ℝ), (5498203227287/12500000000000 : ℝ), (21287527735413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276645493/1250000000 : ℝ)|^515 ≤ (6719659351437/50000000000000 : ℝ)^387
        have hw : |(-276645493/1250000000 : ℝ)|=(276645493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697327223/5000000000 : ℝ)|^515 ≤ (5498203227287/12500000000000 : ℝ)^387
        have hw : |(2697327223/5000000000 : ℝ)|=(2697327223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264126919/10000000000 : ℝ)|^515 ≤ (21287527735413/50000000000000 : ℝ)^387
        have hw : |(5264126919/10000000000 : ℝ)|=(5264126919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s10_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (267250479/500000000 : ℝ)*x 0 + (-91175813/400000000 : ℝ)*x 1 + (1052825413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267250479/500000000 : ℝ)^515 ≤ (5430972942129/12500000000000 : ℝ)^387 := by
    have hnat : (267250479 : ℕ)^515*12500000000000^387 ≤ 5430972942129^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267250479 500000000 5430972942129 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91175813/400000000 : ℝ)^515 ≤ (13977159410411/100000000000000 : ℝ)^387 := by
    have hnat : (91175813 : ℕ)^515*100000000000000^387 ≤ 13977159410411^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91175813 400000000 13977159410411 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052825413/2000000000 : ℝ)^515 ≤ (21287528521097/50000000000000 : ℝ)^387 := by
    have hnat : (1052825413 : ℕ)^515*50000000000000^387 ≤ 21287528521097^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052825413 2000000000 21287528521097 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267250479/500000000 : ℝ), (-91175813/400000000 : ℝ), (1052825413/2000000000 : ℝ)] ![(5430972942129/12500000000000 : ℝ), (13977159410411/100000000000000 : ℝ), (21287528521097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267250479/500000000 : ℝ)|^515 ≤ (5430972942129/12500000000000 : ℝ)^387
        have hw : |(267250479/500000000 : ℝ)|=(267250479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91175813/400000000 : ℝ)|^515 ≤ (13977159410411/100000000000000 : ℝ)^387
        have hw : |(-91175813/400000000 : ℝ)|=(91175813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052825413/2000000000 : ℝ)|^515 ≤ (21287528521097/50000000000000 : ℝ)^387
        have hw : |(1052825413/2000000000 : ℝ)|=(1052825413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s10_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (267250547/500000000 : ℝ)*x 0 + (210565053/400000000 : ℝ)*x 1 + (-1139697249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267250547/500000000 : ℝ)^515 ≤ (43447798248443/100000000000000 : ℝ)^387 := by
    have hnat : (267250547 : ℕ)^515*100000000000000^387 ≤ 43447798248443^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267250547 500000000 43447798248443 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210565053/400000000 : ℝ)^515 ≤ (1703001963109/4000000000000 : ℝ)^387 := by
    have hnat : (210565053 : ℕ)^515*4000000000000^387 ≤ 1703001963109^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210565053 400000000 1703001963109 4000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139697249/5000000000 : ℝ)^515 ≤ (1747144082751/12500000000000 : ℝ)^387 := by
    have hnat : (1139697249 : ℕ)^515*12500000000000^387 ≤ 1747144082751^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139697249 5000000000 1747144082751 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267250547/500000000 : ℝ), (210565053/400000000 : ℝ), (-1139697249/5000000000 : ℝ)] ![(43447798248443/100000000000000 : ℝ), (1703001963109/4000000000000 : ℝ), (1747144082751/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267250547/500000000 : ℝ)|^515 ≤ (43447798248443/100000000000000 : ℝ)^387
        have hw : |(267250547/500000000 : ℝ)|=(267250547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210565053/400000000 : ℝ)|^515 ≤ (1703001963109/4000000000000 : ℝ)^387
        have hw : |(210565053/400000000 : ℝ)|=(210565053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1139697249/5000000000 : ℝ)|^515 ≤ (1747144082751/12500000000000 : ℝ)^387
        have hw : |(-1139697249/5000000000 : ℝ)|=(1139697249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s10_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4378233021/10000000000 : ℝ)*x 0 + (2126348021/5000000000 : ℝ)*x 1 + (563443181/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378233021/10000000000 : ℝ)^515 ≤ (33316448957643/100000000000000 : ℝ)^387 := by
    have hnat : (4378233021 : ℕ)^515*100000000000000^387 ≤ 33316448957643^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378233021 10000000000 33316448957643 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126348021/5000000000 : ℝ)^515 ≤ (2003204705311/6250000000000 : ℝ)^387 := by
    have hnat : (2126348021 : ℕ)^515*6250000000000^387 ≤ 2003204705311^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126348021 5000000000 2003204705311 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563443181/1250000000 : ℝ)^515 ≤ (17316137868173/50000000000000 : ℝ)^387 := by
    have hnat : (563443181 : ℕ)^515*50000000000000^387 ≤ 17316137868173^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563443181 1250000000 17316137868173 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378233021/10000000000 : ℝ), (2126348021/5000000000 : ℝ), (563443181/1250000000 : ℝ)] ![(33316448957643/100000000000000 : ℝ), (2003204705311/6250000000000 : ℝ), (17316137868173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378233021/10000000000 : ℝ)|^515 ≤ (33316448957643/100000000000000 : ℝ)^387
        have hw : |(4378233021/10000000000 : ℝ)|=(4378233021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126348021/5000000000 : ℝ)|^515 ≤ (2003204705311/6250000000000 : ℝ)^387
        have hw : |(2126348021/5000000000 : ℝ)|=(2126348021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563443181/1250000000 : ℝ)|^515 ≤ (17316137868173/50000000000000 : ℝ)^387
        have hw : |(563443181/1250000000 : ℝ)|=(563443181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s10_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213168597/10000000000 : ℝ)*x 0 + (210578133/400000000 : ℝ)*x 1 + (5394327201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213168597/10000000000 : ℝ)^515 ≤ (3359839075833/25000000000000 : ℝ)^387 := by
    have hnat : (2213168597 : ℕ)^515*25000000000000^387 ≤ 3359839075833^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213168597 10000000000 3359839075833 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210578133/400000000 : ℝ)^515 ≤ (10644642137063/25000000000000 : ℝ)^387 := by
    have hnat : (210578133 : ℕ)^515*25000000000000^387 ≤ 10644642137063^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210578133 400000000 10644642137063 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394327201/10000000000 : ℝ)^515 ≤ (2748879695869/6250000000000 : ℝ)^387 := by
    have hnat : (5394327201 : ℕ)^515*6250000000000^387 ≤ 2748879695869^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394327201 10000000000 2748879695869 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213168597/10000000000 : ℝ), (210578133/400000000 : ℝ), (5394327201/10000000000 : ℝ)] ![(3359839075833/25000000000000 : ℝ), (10644642137063/25000000000000 : ℝ), (2748879695869/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213168597/10000000000 : ℝ)|^515 ≤ (3359839075833/25000000000000 : ℝ)^387
        have hw : |(-2213168597/10000000000 : ℝ)|=(2213168597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210578133/400000000 : ℝ)|^515 ≤ (10644642137063/25000000000000 : ℝ)^387
        have hw : |(210578133/400000000 : ℝ)|=(210578133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394327201/10000000000 : ℝ)|^515 ≤ (2748879695869/6250000000000 : ℝ)^387
        have hw : |(5394327201/10000000000 : ℝ)|=(5394327201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s10_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312183117/10000000000 : ℝ)*x 0 + (-107459767/500000000 : ℝ)*x 1 + (539432623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312183117/10000000000 : ℝ)^515 ≤ (673328965963/1562500000000 : ℝ)^387 := by
    have hnat : (5312183117 : ℕ)^515*1562500000000^387 ≤ 673328965963^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312183117 10000000000 673328965963 1562500000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107459767/500000000 : ℝ)^515 ≤ (2584976313479/20000000000000 : ℝ)^387 := by
    have hnat : (107459767 : ℕ)^515*20000000000000^387 ≤ 2584976313479^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107459767 500000000 2584976313479 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539432623/1000000000 : ℝ)^515 ≤ (21991032299217/50000000000000 : ℝ)^387 := by
    have hnat : (539432623 : ℕ)^515*50000000000000^387 ≤ 21991032299217^387*1000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539432623 1000000000 21991032299217 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312183117/10000000000 : ℝ), (-107459767/500000000 : ℝ), (539432623/1000000000 : ℝ)] ![(673328965963/1562500000000 : ℝ), (2584976313479/20000000000000 : ℝ), (21991032299217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312183117/10000000000 : ℝ)|^515 ≤ (673328965963/1562500000000 : ℝ)^387
        have hw : |(5312183117/10000000000 : ℝ)|=(5312183117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107459767/500000000 : ℝ)|^515 ≤ (2584976313479/20000000000000 : ℝ)^387
        have hw : |(-107459767/500000000 : ℝ)|=(107459767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539432623/1000000000 : ℝ)|^515 ≤ (21991032299217/50000000000000 : ℝ)^387
        have hw : |(539432623/1000000000 : ℝ)|=(539432623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s10_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1062436761/2000000000 : ℝ)*x 0 + (2697163081/5000000000 : ℝ)*x 1 + (-268649313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062436761/2000000000 : ℝ)^515 ≤ (21546530624363/50000000000000 : ℝ)^387 := by
    have hnat : (1062436761 : ℕ)^515*50000000000000^387 ≤ 21546530624363^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062436761 2000000000 21546530624363 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697163081/5000000000 : ℝ)^515 ≤ (21991031930313/50000000000000 : ℝ)^387 := by
    have hnat : (2697163081 : ℕ)^515*50000000000000^387 ≤ 21991031930313^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697163081 5000000000 21991031930313 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268649313/1250000000 : ℝ)^515 ≤ (6462437438489/50000000000000 : ℝ)^387 := by
    have hnat : (268649313 : ℕ)^515*50000000000000^387 ≤ 6462437438489^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268649313 1250000000 6462437438489 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062436761/2000000000 : ℝ), (2697163081/5000000000 : ℝ), (-268649313/1250000000 : ℝ)] ![(21546530624363/50000000000000 : ℝ), (21991031930313/50000000000000 : ℝ), (6462437438489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062436761/2000000000 : ℝ)|^515 ≤ (21546530624363/50000000000000 : ℝ)^387
        have hw : |(1062436761/2000000000 : ℝ)|=(1062436761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697163081/5000000000 : ℝ)|^515 ≤ (21991031930313/50000000000000 : ℝ)^387
        have hw : |(2697163081/5000000000 : ℝ)|=(2697163081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268649313/1250000000 : ℝ)|^515 ≤ (6462437438489/50000000000000 : ℝ)^387
        have hw : |(-268649313/1250000000 : ℝ)|=(268649313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1399/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (449/4000 : ℝ) ^ (8239/2048 : ℝ) ≤ (15098990694742767/100000000000000000000 : ℝ) := by
    have hpowers : (449/4000 : ℝ)^8239 ≤ (15098990694742767/100000000000000000000 : ℝ)^2048 := by
      have hnat : (449 : ℕ)^8239*100000000000000000000^2048 ≤ 15098990694742767^2048*4000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        449 4000 15098990694742767 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (449/4000 : ℝ)) (X := (15098990694742767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1399/10000 : ℝ) ^ (8239/2048 : ℝ) ≤ (7323151814906417/20000000000000000000 : ℝ) := by
    have hpowers : (1399/10000 : ℝ)^8239 ≤ (7323151814906417/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1399 : ℕ)^8239*20000000000000000000^2048 ≤ 7323151814906417^2048*10000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 10000 7323151814906417 20000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/10000 : ℝ)) (X := (7323151814906417/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015098990694742767/50000000000000000000 : ℝ) ≤ (2500187639429161/2500000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50015098990694742767/50000000000000000000 : ℝ)^2048 ≤ (2500187639429161/2500000000000000 : ℝ)^8239 := by
      have hnat : (50015098990694742767 : ℕ)^2048*2500000000000000^8239 ≤ 2500187639429161^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015098990694742767 50000000000000000000 2500187639429161 2500000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500187639429161/2500000000000000 : ℝ)) (X := (50015098990694742767/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012928687442318713/25000000000000000000 : ℝ) ≤ (10001285243781673/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (25012928687442318713/25000000000000000000 : ℝ)^2048 ≤ (10001285243781673/10000000000000000 : ℝ)^8239 := by
      have hnat : (25012928687442318713 : ℕ)^2048*10000000000000000^8239 ≤ 10001285243781673^8239*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012928687442318713 25000000000000000000 10001285243781673 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001285243781673/10000000000000000 : ℝ)) (X := (25012928687442318713/25000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007323151814906417/10000000000000000000 : ℝ) ≤ (5000909964923351/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (10007323151814906417/10000000000000000000 : ℝ)^2048 ≤ (5000909964923351/5000000000000000 : ℝ)^8239 := by
      have hnat : (10007323151814906417 : ℕ)^2048*5000000000000000^8239 ≤ 5000909964923351^8239*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007323151814906417 10000000000000000000 5000909964923351 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000909964923351/5000000000000000 : ℝ)) (X := (10007323151814906417/10000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15098990694742767/100000000000000000000 : ℝ) ≤ ((2764007158992661961/2765000000000000000 : ℝ)+2*(534686065029/276500000000000 : ℝ)*(449/4000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (2764007158992661961/2765000000000000000 : ℝ)+2*(534686065029/276500000000000 : ℝ)*(449/4000 : ℝ)=(2500187639429161/2500000000000000 : ℝ) by norm_num, show 1+2*(15098990694742767/100000000000000000000 : ℝ)=(50015098990694742767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7323151814906417/20000000000000000000 : ℝ)+(15098990694742767/100000000000000000000 : ℝ) ≤ ((2764007158992661961/2765000000000000000 : ℝ)+(534686065029/276500000000000 : ℝ)*((1399/10000 : ℝ)+(449/4000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (2764007158992661961/2765000000000000000 : ℝ)+(534686065029/276500000000000 : ℝ)*((1399/10000 : ℝ)+(449/4000 : ℝ))=(10001285243781673/10000000000000000 : ℝ) by norm_num, show 1+(7323151814906417/20000000000000000000 : ℝ)+(15098990694742767/100000000000000000000 : ℝ)=(25012928687442318713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7323151814906417/20000000000000000000 : ℝ) ≤ ((2764007158992661961/2765000000000000000 : ℝ)+2*(534686065029/276500000000000 : ℝ)*(1399/10000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (2764007158992661961/2765000000000000000 : ℝ)+2*(534686065029/276500000000000 : ℝ)*(1399/10000 : ℝ)=(5000909964923351/5000000000000000 : ℝ) by norm_num, show 1+2*(7323151814906417/20000000000000000000 : ℝ)=(10007323151814906417/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2764007158992661961/2765000000000000000 : ℝ)*(X 1 0+X 2 0)+(534686065029/276500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (2764007158992661961/2765000000000000000 : ℝ)) (alpha := (534686065029/276500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2764007158992661961/2765000000000000000 : ℝ)*(X 0 1+X 2 1)+(534686065029/276500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (2764007158992661961/2765000000000000000 : ℝ)) (alpha := (534686065029/276500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2764007158992661961/2765000000000000000 : ℝ)*(X 0 2+X 1 2)+(534686065029/276500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (2764007158992661961/2765000000000000000 : ℝ)) (alpha := (534686065029/276500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276645493/1250000000 : ℝ)*X 0 0+(2697327223/5000000000 : ℝ)*X 0 1+(5264126919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s10_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267250479/500000000 : ℝ)*X 1 0+(-91175813/400000000 : ℝ)*X 1 1+(1052825413/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s10_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267250547/500000000 : ℝ)*X 2 0+(210565053/400000000 : ℝ)*X 2 1+(-1139697249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s10_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378233021/10000000000 : ℝ)*X 0 0+(2126348021/5000000000 : ℝ)*X 0 1+(563443181/1250000000 : ℝ)*X 0 2+(4378233021/10000000000 : ℝ)*X 1 0+(2126348021/5000000000 : ℝ)*X 1 1+(563443181/1250000000 : ℝ)*X 1 2+(4378233021/10000000000 : ℝ)*X 2 0+(2126348021/5000000000 : ℝ)*X 2 1+(563443181/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s10_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2213168597/10000000000 : ℝ)*X 0 0+(210578133/400000000 : ℝ)*X 0 1+(5394327201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s10_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312183117/10000000000 : ℝ)*X 1 0+(-107459767/500000000 : ℝ)*X 1 1+(539432623/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s10_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062436761/2000000000 : ℝ)*X 2 0+(2697163081/5000000000 : ℝ)*X 2 1+(-268649313/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s10_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29141537942924713239267/13825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112572149/50000000000000 : ℝ)*(base8) + (1380993/400000000000 : ℝ)*(base21) + (285128971/50000000000000 : ℝ)*(lower2) + (40454841/6250000000000 : ℝ)*(upper4) + (1448135587701743/25000000000000 : ℝ)*(major0) + (1448135587701743/25000000000000 : ℝ)*(major1) + (1448135587701743/25000000000000 : ℝ)*(major2) + (7661190639917109/100000000000000 : ℝ)*(sp0) + (383060427932149/5000000000000 : ℝ)*(sp1) + (7661212751491077/100000000000000 : ℝ)*(sp2) + (490482538181047/12500000000000 : ℝ)*(sp3) + (8365210311/25000000000000 : ℝ)*(sp4) + (15767259671/100000000000000 : ℝ)*(sp5) + (2807290831/25000000000000 : ℝ)*(sp6) + (490482538181047/12500000000000 : ℝ)*(f.failure) + (7661224325902651/100000000000000 : ℝ)*(f.sum) + (129574260510339/1728125000000000000000000000 : ℝ)*base66 + (330124373842718023/69125000000000000000000000000000 : ℝ)*base67 + (720883022059906977/69125000000000000000000000000000 : ℝ)*base70 + (402473857612406977/69125000000000000000000000000000 : ℝ)*base72 + (18621291367303/3456250000000000000000000000 : ℝ)*base74 + (45071138603218023/69125000000000000000000000000000 : ℝ)*base75 + (2876404194241031977/69125000000000000000000000000000 : ℝ)*base78 + (603089902061843023/69125000000000000000000000000000 : ℝ)*base79 + (43860614755381/6912500000000000000000000000 : ℝ)*base82 + (4514707/625000000000000000000 : ℝ)*base89 + (4514707/625000000000000000000 : ℝ)*base91 + (4514707/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1047_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_box_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041523937/5000000000 : ℝ)*x 0 + (5377619557/10000000000 : ℝ)*x 1 + (1344404893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041523937/5000000000 : ℝ)^515 ≤ (3099555930529/25000000000000 : ℝ)^387 := by
    have hnat : (1041523937 : ℕ)^515*25000000000000^387 ≤ 3099555930529^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041523937 5000000000 3099555930529 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377619557/10000000000 : ℝ)^515 ≤ (10950222011287/25000000000000 : ℝ)^387 := by
    have hnat : (5377619557 : ℕ)^515*25000000000000^387 ≤ 10950222011287^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377619557 10000000000 10950222011287 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344404893/2500000000 : ℝ)^515 ≤ (43800888207733/100000000000000 : ℝ)^387 := by
    have hnat : (1344404893 : ℕ)^515*100000000000000^387 ≤ 43800888207733^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344404893 2500000000 43800888207733 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041523937/5000000000 : ℝ), (5377619557/10000000000 : ℝ), (1344404893/2500000000 : ℝ)] ![(3099555930529/25000000000000 : ℝ), (10950222011287/25000000000000 : ℝ), (43800888207733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041523937/5000000000 : ℝ)|^515 ≤ (3099555930529/25000000000000 : ℝ)^387
        have hw : |(-1041523937/5000000000 : ℝ)|=(1041523937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377619557/10000000000 : ℝ)|^515 ≤ (10950222011287/25000000000000 : ℝ)^387
        have hw : |(5377619557/10000000000 : ℝ)|=(5377619557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344404893/2500000000 : ℝ)|^515 ≤ (43800888207733/100000000000000 : ℝ)^387
        have hw : |(1344404893/2500000000 : ℝ)|=(1344404893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2647493161/5000000000 : ℝ)*x 0 + (-2194858927/10000000000 : ℝ)*x 1 + (2688809829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647493161/5000000000 : ℝ)^515 ≤ (21453755260151/50000000000000 : ℝ)^387 := by
    have hnat : (2647493161 : ℕ)^515*50000000000000^387 ≤ 21453755260151^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647493161 5000000000 21453755260151 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194858927/10000000000 : ℝ)^515 ≤ (13291600325893/100000000000000 : ℝ)^387 := by
    have hnat : (2194858927 : ℕ)^515*100000000000000^387 ≤ 13291600325893^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194858927 10000000000 13291600325893 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688809829/5000000000 : ℝ)^515 ≤ (43800889139887/100000000000000 : ℝ)^387 := by
    have hnat : (2688809829 : ℕ)^515*100000000000000^387 ≤ 43800889139887^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688809829 5000000000 43800889139887 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647493161/5000000000 : ℝ), (-2194858927/10000000000 : ℝ), (2688809829/5000000000 : ℝ)] ![(21453755260151/50000000000000 : ℝ), (13291600325893/100000000000000 : ℝ), (43800889139887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647493161/5000000000 : ℝ)|^515 ≤ (21453755260151/50000000000000 : ℝ)^387
        have hw : |(2647493161/5000000000 : ℝ)|=(2647493161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194858927/10000000000 : ℝ)|^515 ≤ (13291600325893/100000000000000 : ℝ)^387
        have hw : |(-2194858927/10000000000 : ℝ)|=(2194858927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688809829/5000000000 : ℝ)|^515 ≤ (43800889139887/100000000000000 : ℝ)^387
        have hw : |(2688809829/5000000000 : ℝ)|=(2688809829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2647493347/5000000000 : ℝ)*x 0 + (1344404837/2500000000 : ℝ)*x 1 + (-1097429423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647493347/5000000000 : ℝ)^515 ≤ (4290751453181/10000000000000 : ℝ)^387 := by
    have hnat : (2647493347 : ℕ)^515*10000000000000^387 ≤ 4290751453181^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647493347 5000000000 4290751453181 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344404837/2500000000 : ℝ)^515 ≤ (43800885779797/100000000000000 : ℝ)^387 := by
    have hnat : (1344404837 : ℕ)^515*100000000000000^387 ≤ 43800885779797^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344404837 2500000000 43800885779797 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097429423/5000000000 : ℝ)^515 ≤ (830724979571/6250000000000 : ℝ)^387 := by
    have hnat : (1097429423 : ℕ)^515*6250000000000^387 ≤ 830724979571^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097429423 5000000000 830724979571 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647493347/5000000000 : ℝ), (1344404837/2500000000 : ℝ), (-1097429423/5000000000 : ℝ)] ![(4290751453181/10000000000000 : ℝ), (43800885779797/100000000000000 : ℝ), (830724979571/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647493347/5000000000 : ℝ)|^515 ≤ (4290751453181/10000000000000 : ℝ)^387
        have hw : |(2647493347/5000000000 : ℝ)|=(2647493347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344404837/2500000000 : ℝ)|^515 ≤ (43800885779797/100000000000000 : ℝ)^387
        have hw : |(1344404837/2500000000 : ℝ)|=(1344404837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097429423/5000000000 : ℝ)|^515 ≤ (830724979571/6250000000000 : ℝ)^387
        have hw : |(-1097429423/5000000000 : ℝ)|=(1097429423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (897366327/2000000000 : ℝ)*x 0 + (1081527569/2500000000 : ℝ)*x 1 + (4326110411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897366327/2000000000 : ℝ)^515 ≤ (34420650857849/100000000000000 : ℝ)^387 := by
    have hnat : (897366327 : ℕ)^515*100000000000000^387 ≤ 34420650857849^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897366327 2000000000 34420650857849 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081527569/2500000000 : ℝ)^515 ≤ (3278967388349/10000000000000 : ℝ)^387 := by
    have hnat : (1081527569 : ℕ)^515*10000000000000^387 ≤ 3278967388349^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081527569 2500000000 3278967388349 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326110411/10000000000 : ℝ)^515 ≤ (32789675245153/100000000000000 : ℝ)^387 := by
    have hnat : (4326110411 : ℕ)^515*100000000000000^387 ≤ 32789675245153^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326110411 10000000000 32789675245153 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897366327/2000000000 : ℝ), (1081527569/2500000000 : ℝ), (4326110411/10000000000 : ℝ)] ![(34420650857849/100000000000000 : ℝ), (3278967388349/10000000000000 : ℝ), (32789675245153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897366327/2000000000 : ℝ)|^515 ≤ (34420650857849/100000000000000 : ℝ)^387
        have hw : |(897366327/2000000000 : ℝ)|=(897366327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081527569/2500000000 : ℝ)|^515 ≤ (3278967388349/10000000000000 : ℝ)^387
        have hw : |(1081527569/2500000000 : ℝ)|=(1081527569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326110411/10000000000 : ℝ)|^515 ≤ (32789675245153/100000000000000 : ℝ)^387
        have hw : |(4326110411/10000000000 : ℝ)|=(4326110411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2344660043/10000000000 : ℝ)*x 0 + (5279805643/10000000000 : ℝ)*x 1 + (5279805379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2344660043/10000000000 : ℝ)^515 ≤ (2902446385143/20000000000000 : ℝ)^387 := by
    have hnat : (2344660043 : ℕ)^515*20000000000000^387 ≤ 2902446385143^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344660043 10000000000 2902446385143 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279805643/10000000000 : ℝ)^515 ≤ (42743885450677/100000000000000 : ℝ)^387 := by
    have hnat : (5279805643 : ℕ)^515*100000000000000^387 ≤ 42743885450677^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279805643 10000000000 42743885450677 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279805379/10000000000 : ℝ)^515 ≤ (21371941303251/50000000000000 : ℝ)^387 := by
    have hnat : (5279805379 : ℕ)^515*50000000000000^387 ≤ 21371941303251^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279805379 10000000000 21371941303251 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2344660043/10000000000 : ℝ), (5279805643/10000000000 : ℝ), (5279805379/10000000000 : ℝ)] ![(2902446385143/20000000000000 : ℝ), (42743885450677/100000000000000 : ℝ), (21371941303251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2344660043/10000000000 : ℝ)|^515 ≤ (2902446385143/20000000000000 : ℝ)^387
        have hw : |(-2344660043/10000000000 : ℝ)|=(2344660043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279805643/10000000000 : ℝ)|^515 ≤ (42743885450677/100000000000000 : ℝ)^387
        have hw : |(5279805643/10000000000 : ℝ)|=(5279805643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279805379/10000000000 : ℝ)|^515 ≤ (21371941303251/50000000000000 : ℝ)^387
        have hw : |(5279805379/10000000000 : ℝ)|=(5279805379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2682120847/5000000000 : ℝ)*x 0 + (-2233039971/10000000000 : ℝ)*x 1 + (5279805309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682120847/5000000000 : ℝ)^515 ≤ (8731189022517/20000000000000 : ℝ)^387 := by
    have hnat : (2682120847 : ℕ)^515*20000000000000^387 ≤ 8731189022517^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682120847 5000000000 8731189022517 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2233039971/10000000000 : ℝ)^515 ≤ (13600173033967/100000000000000 : ℝ)^387 := by
    have hnat : (2233039971 : ℕ)^515*100000000000000^387 ≤ 13600173033967^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233039971 10000000000 13600173033967 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279805309/10000000000 : ℝ)^515 ≤ (8548776370473/20000000000000 : ℝ)^387 := by
    have hnat : (5279805309 : ℕ)^515*20000000000000^387 ≤ 8548776370473^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279805309 10000000000 8548776370473 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682120847/5000000000 : ℝ), (-2233039971/10000000000 : ℝ), (5279805309/10000000000 : ℝ)] ![(8731189022517/20000000000000 : ℝ), (13600173033967/100000000000000 : ℝ), (8548776370473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682120847/5000000000 : ℝ)|^515 ≤ (8731189022517/20000000000000 : ℝ)^387
        have hw : |(2682120847/5000000000 : ℝ)|=(2682120847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2233039971/10000000000 : ℝ)|^515 ≤ (13600173033967/100000000000000 : ℝ)^387
        have hw : |(-2233039971/10000000000 : ℝ)|=(2233039971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279805309/10000000000 : ℝ)|^515 ≤ (8548776370473/20000000000000 : ℝ)^387
        have hw : |(5279805309/10000000000 : ℝ)|=(5279805309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5364241133/10000000000 : ℝ)*x 0 + (2639902919/5000000000 : ℝ)*x 1 + (-446608003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364241133/10000000000 : ℝ)^515 ≤ (8731187807383/20000000000000 : ℝ)^387 := by
    have hnat : (5364241133 : ℕ)^515*20000000000000^387 ≤ 8731187807383^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364241133 10000000000 8731187807383 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639902919/5000000000 : ℝ)^515 ≤ (41742077687/97656250000 : ℝ)^387 := by
    have hnat : (2639902919 : ℕ)^515*97656250000^387 ≤ 41742077687^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639902919 5000000000 41742077687 97656250000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446608003/2000000000 : ℝ)^515 ≤ (680008669529/5000000000000 : ℝ)^387 := by
    have hnat : (446608003 : ℕ)^515*5000000000000^387 ≤ 680008669529^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446608003 2000000000 680008669529 5000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364241133/10000000000 : ℝ), (2639902919/5000000000 : ℝ), (-446608003/2000000000 : ℝ)] ![(8731187807383/20000000000000 : ℝ), (41742077687/97656250000 : ℝ), (680008669529/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364241133/10000000000 : ℝ)|^515 ≤ (8731187807383/20000000000000 : ℝ)^387
        have hw : |(5364241133/10000000000 : ℝ)|=(5364241133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639902919/5000000000 : ℝ)|^515 ≤ (41742077687/97656250000 : ℝ)^387
        have hw : |(2639902919/5000000000 : ℝ)|=(2639902919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446608003/2000000000 : ℝ)|^515 ≤ (680008669529/5000000000000 : ℝ)^387
        have hw : |(-446608003/2000000000 : ℝ)|=(446608003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2134657019/5000000000 : ℝ)*x 0 + (4434847681/10000000000 : ℝ)*x 1 + (4434847363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134657019/5000000000 : ℝ)^515 ≤ (32218052302229/100000000000000 : ℝ)^387 := by
    have hnat : (2134657019 : ℕ)^515*100000000000000^387 ≤ 32218052302229^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134657019 5000000000 32218052302229 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4434847681/10000000000 : ℝ)^515 ≤ (8472743865139/25000000000000 : ℝ)^387 := by
    have hnat : (4434847681 : ℕ)^515*25000000000000^387 ≤ 8472743865139^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434847681 10000000000 8472743865139 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4434847363/10000000000 : ℝ)^515 ≤ (423637152833/1250000000000 : ℝ)^387 := by
    have hnat : (4434847363 : ℕ)^515*1250000000000^387 ≤ 423637152833^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434847363 10000000000 423637152833 1250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134657019/5000000000 : ℝ), (4434847681/10000000000 : ℝ), (4434847363/10000000000 : ℝ)] ![(32218052302229/100000000000000 : ℝ), (8472743865139/25000000000000 : ℝ), (423637152833/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134657019/5000000000 : ℝ)|^515 ≤ (32218052302229/100000000000000 : ℝ)^387
        have hw : |(2134657019/5000000000 : ℝ)|=(2134657019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4434847681/10000000000 : ℝ)|^515 ≤ (8472743865139/25000000000000 : ℝ)^387
        have hw : |(4434847681/10000000000 : ℝ)|=(4434847681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4434847363/10000000000 : ℝ)|^515 ≤ (423637152833/1250000000000 : ℝ)^387
        have hw : |(4434847363/10000000000 : ℝ)|=(4434847363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_8 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2290070481/10000000000 : ℝ)*x 0 + (162920953/312500000 : ℝ)*x 1 + (1077443349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2290070481/10000000000 : ℝ)^515 ≤ (3516084289377/25000000000000 : ℝ)^387 := by
    have hnat : (2290070481 : ℕ)^515*25000000000000^387 ≤ 3516084289377^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290070481 10000000000 3516084289377 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162920953/312500000 : ℝ)^515 ≤ (42030720195729/100000000000000 : ℝ)^387 := by
    have hnat : (162920953 : ℕ)^515*100000000000000^387 ≤ 42030720195729^387*312500000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162920953 312500000 42030720195729 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077443349/2000000000 : ℝ)^515 ≤ (4390494262831/10000000000000 : ℝ)^387 := by
    have hnat : (1077443349 : ℕ)^515*10000000000000^387 ≤ 4390494262831^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077443349 2000000000 4390494262831 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2290070481/10000000000 : ℝ), (162920953/312500000 : ℝ), (1077443349/2000000000 : ℝ)] ![(3516084289377/25000000000000 : ℝ), (42030720195729/100000000000000 : ℝ), (4390494262831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2290070481/10000000000 : ℝ)|^515 ≤ (3516084289377/25000000000000 : ℝ)^387
        have hw : |(-2290070481/10000000000 : ℝ)|=(2290070481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162920953/312500000 : ℝ)|^515 ≤ (42030720195729/100000000000000 : ℝ)^387
        have hw : |(162920953/312500000 : ℝ)|=(162920953/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077443349/2000000000 : ℝ)|^515 ≤ (4390494262831/10000000000000 : ℝ)^387
        have hw : |(1077443349/2000000000 : ℝ)|=(1077443349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_9 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5288187663/10000000000 : ℝ)*x 0 + (-273880199/1250000000 : ℝ)*x 1 + (1346804167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288187663/10000000000 : ℝ)^515 ≤ (42834211909361/100000000000000 : ℝ)^387 := by
    have hnat : (5288187663 : ℕ)^515*100000000000000^387 ≤ 42834211909361^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288187663 10000000000 42834211909361 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273880199/1250000000 : ℝ)^515 ≤ (1657605785327/12500000000000 : ℝ)^387 := by
    have hnat : (273880199 : ℕ)^515*12500000000000^387 ≤ 1657605785327^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273880199 1250000000 1657605785327 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346804167/2500000000 : ℝ)^515 ≤ (8780988358643/20000000000000 : ℝ)^387 := by
    have hnat : (1346804167 : ℕ)^515*20000000000000^387 ≤ 8780988358643^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346804167 2500000000 8780988358643 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288187663/10000000000 : ℝ), (-273880199/1250000000 : ℝ), (1346804167/2500000000 : ℝ)] ![(42834211909361/100000000000000 : ℝ), (1657605785327/12500000000000 : ℝ), (8780988358643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288187663/10000000000 : ℝ)|^515 ≤ (42834211909361/100000000000000 : ℝ)^387
        have hw : |(5288187663/10000000000 : ℝ)|=(5288187663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273880199/1250000000 : ℝ)|^515 ≤ (1657605785327/12500000000000 : ℝ)^387
        have hw : |(-273880199/1250000000 : ℝ)|=(273880199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346804167/2500000000 : ℝ)|^515 ≤ (8780988358643/20000000000000 : ℝ)^387
        have hw : |(1346804167/2500000000 : ℝ)|=(1346804167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_10 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1322046939/2500000000 : ℝ)*x 0 + (5387216693/10000000000 : ℝ)*x 1 + (-1095520717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322046939/2500000000 : ℝ)^515 ≤ (10708553227953/25000000000000 : ℝ)^387 := by
    have hnat : (1322046939 : ℕ)^515*25000000000000^387 ≤ 10708553227953^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322046939 2500000000 10708553227953 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387216693/10000000000 : ℝ)^515 ≤ (878098841287/2000000000000 : ℝ)^387 := by
    have hnat : (5387216693 : ℕ)^515*2000000000000^387 ≤ 878098841287^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387216693 10000000000 878098841287 2000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095520717/5000000000 : ℝ)^515 ≤ (3315211252517/25000000000000 : ℝ)^387 := by
    have hnat : (1095520717 : ℕ)^515*25000000000000^387 ≤ 3315211252517^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095520717 5000000000 3315211252517 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322046939/2500000000 : ℝ), (5387216693/10000000000 : ℝ), (-1095520717/5000000000 : ℝ)] ![(10708553227953/25000000000000 : ℝ), (878098841287/2000000000000 : ℝ), (3315211252517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322046939/2500000000 : ℝ)|^515 ≤ (10708553227953/25000000000000 : ℝ)^387
        have hw : |(1322046939/2500000000 : ℝ)|=(1322046939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387216693/10000000000 : ℝ)|^515 ≤ (878098841287/2000000000000 : ℝ)^387
        have hw : |(5387216693/10000000000 : ℝ)|=(5387216693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095520717/5000000000 : ℝ)|^515 ≤ (3315211252517/25000000000000 : ℝ)^387
        have hw : |(-1095520717/5000000000 : ℝ)|=(1095520717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_11 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4507900391/10000000000 : ℝ)*x 0 + (431543541/1000000000 : ℝ)*x 1 + (2157717763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4507900391/10000000000 : ℝ)^515 ≤ (34635904857371/100000000000000 : ℝ)^387 := by
    have hnat : (4507900391 : ℕ)^515*100000000000000^387 ≤ 34635904857371^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507900391 10000000000 34635904857371 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431543541/1000000000 : ℝ)^515 ≤ (16341023489239/50000000000000 : ℝ)^387 := by
    have hnat : (431543541 : ℕ)^515*50000000000000^387 ≤ 16341023489239^387*1000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431543541 1000000000 16341023489239 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157717763/5000000000 : ℝ)^515 ≤ (4085256018443/12500000000000 : ℝ)^387 := by
    have hnat : (2157717763 : ℕ)^515*12500000000000^387 ≤ 4085256018443^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157717763 5000000000 4085256018443 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4507900391/10000000000 : ℝ), (431543541/1000000000 : ℝ), (2157717763/5000000000 : ℝ)] ![(34635904857371/100000000000000 : ℝ), (16341023489239/50000000000000 : ℝ), (4085256018443/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4507900391/10000000000 : ℝ)|^515 ≤ (34635904857371/100000000000000 : ℝ)^387
        have hw : |(4507900391/10000000000 : ℝ)|=(4507900391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(431543541/1000000000 : ℝ)|^515 ≤ (16341023489239/50000000000000 : ℝ)^387
        have hw : |(431543541/1000000000 : ℝ)|=(431543541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2157717763/5000000000 : ℝ)|^515 ≤ (4085256018443/12500000000000 : ℝ)^387
        have hw : |(2157717763/5000000000 : ℝ)|=(2157717763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_12 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138018927/10000000000 : ℝ)*x 0 + (340162781/625000000 : ℝ)*x 1 + (2635907539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138018927/10000000000 : ℝ)^515 ≤ (2567102990741/20000000000000 : ℝ)^387 := by
    have hnat : (2138018927 : ℕ)^515*20000000000000^387 ≤ 2567102990741^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138018927 10000000000 2567102990741 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340162781/625000000 : ℝ)^515 ≤ (44506663489149/100000000000000 : ℝ)^387 := by
    have hnat : (340162781 : ℕ)^515*100000000000000^387 ≤ 44506663489149^387*625000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340162781 625000000 44506663489149 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635907539/5000000000 : ℝ)^515 ≤ (21328910770813/50000000000000 : ℝ)^387 := by
    have hnat : (2635907539 : ℕ)^515*50000000000000^387 ≤ 21328910770813^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635907539 5000000000 21328910770813 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138018927/10000000000 : ℝ), (340162781/625000000 : ℝ), (2635907539/5000000000 : ℝ)] ![(2567102990741/20000000000000 : ℝ), (44506663489149/100000000000000 : ℝ), (21328910770813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138018927/10000000000 : ℝ)|^515 ≤ (2567102990741/20000000000000 : ℝ)^387
        have hw : |(-2138018927/10000000000 : ℝ)|=(2138018927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340162781/625000000 : ℝ)|^515 ≤ (44506663489149/100000000000000 : ℝ)^387
        have hw : |(340162781/625000000 : ℝ)|=(340162781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635907539/5000000000 : ℝ)|^515 ≤ (21328910770813/50000000000000 : ℝ)^387
        have hw : |(2635907539/5000000000 : ℝ)|=(2635907539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_13 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5369896207/10000000000 : ℝ)*x 0 + (-2236099743/10000000000 : ℝ)*x 1 + (5271815661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369896207/10000000000 : ℝ)^515 ≤ (4371719456517/10000000000000 : ℝ)^387 := by
    have hnat : (5369896207 : ℕ)^515*10000000000000^387 ≤ 4371719456517^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369896207 10000000000 4371719456517 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236099743/10000000000 : ℝ)^515 ≤ (2724995520047/20000000000000 : ℝ)^387 := by
    have hnat : (2236099743 : ℕ)^515*20000000000000^387 ≤ 2724995520047^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236099743 10000000000 2724995520047 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271815661/10000000000 : ℝ)^515 ≤ (21328913909683/50000000000000 : ℝ)^387 := by
    have hnat : (5271815661 : ℕ)^515*50000000000000^387 ≤ 21328913909683^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271815661 10000000000 21328913909683 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369896207/10000000000 : ℝ), (-2236099743/10000000000 : ℝ), (5271815661/10000000000 : ℝ)] ![(4371719456517/10000000000000 : ℝ), (2724995520047/20000000000000 : ℝ), (21328913909683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369896207/10000000000 : ℝ)|^515 ≤ (4371719456517/10000000000000 : ℝ)^387
        have hw : |(5369896207/10000000000 : ℝ)|=(5369896207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2236099743/10000000000 : ℝ)|^515 ≤ (2724995520047/20000000000000 : ℝ)^387
        have hw : |(-2236099743/10000000000 : ℝ)|=(2236099743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271815661/10000000000 : ℝ)|^515 ≤ (21328913909683/50000000000000 : ℝ)^387
        have hw : |(5271815661/10000000000 : ℝ)|=(5271815661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_14 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1342474011/2500000000 : ℝ)*x 0 + (5271815803/10000000000 : ℝ)*x 1 + (-559024943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342474011/2500000000 : ℝ)^515 ≤ (43717192799253/100000000000000 : ℝ)^387 := by
    have hnat : (1342474011 : ℕ)^515*100000000000000^387 ≤ 43717192799253^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342474011 2500000000 43717192799253 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271815803/10000000000 : ℝ)^515 ≤ (42657829348421/100000000000000 : ℝ)^387 := by
    have hnat : (5271815803 : ℕ)^515*100000000000000^387 ≤ 42657829348421^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271815803 10000000000 42657829348421 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559024943/2500000000 : ℝ)^515 ≤ (13624977835381/100000000000000 : ℝ)^387 := by
    have hnat : (559024943 : ℕ)^515*100000000000000^387 ≤ 13624977835381^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559024943 2500000000 13624977835381 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342474011/2500000000 : ℝ), (5271815803/10000000000 : ℝ), (-559024943/2500000000 : ℝ)] ![(43717192799253/100000000000000 : ℝ), (42657829348421/100000000000000 : ℝ), (13624977835381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342474011/2500000000 : ℝ)|^515 ≤ (43717192799253/100000000000000 : ℝ)^387
        have hw : |(1342474011/2500000000 : ℝ)|=(1342474011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271815803/10000000000 : ℝ)|^515 ≤ (42657829348421/100000000000000 : ℝ)^387
        have hw : |(5271815803/10000000000 : ℝ)|=(5271815803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-559024943/2500000000 : ℝ)|^515 ≤ (13624977835381/100000000000000 : ℝ)^387
        have hw : |(-559024943/2500000000 : ℝ)|=(559024943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_box_15 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4251316493/10000000000 : ℝ)*x 0 + (4443724887/10000000000 : ℝ)*x 1 + (1110931101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251316493/10000000000 : ℝ)^515 ≤ (32037439905821/100000000000000 : ℝ)^387 := by
    have hnat : (4251316493 : ℕ)^515*100000000000000^387 ≤ 32037439905821^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251316493 10000000000 32037439905821 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4443724887/10000000000 : ℝ)^515 ≤ (8495320624703/25000000000000 : ℝ)^387 := by
    have hnat : (4443724887 : ℕ)^515*25000000000000^387 ≤ 8495320624703^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4443724887 10000000000 8495320624703 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110931101/2500000000 : ℝ)^515 ≤ (33981277583671/100000000000000 : ℝ)^387 := by
    have hnat : (1110931101 : ℕ)^515*100000000000000^387 ≤ 33981277583671^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110931101 2500000000 33981277583671 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251316493/10000000000 : ℝ), (4443724887/10000000000 : ℝ), (1110931101/2500000000 : ℝ)] ![(32037439905821/100000000000000 : ℝ), (8495320624703/25000000000000 : ℝ), (33981277583671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251316493/10000000000 : ℝ)|^515 ≤ (32037439905821/100000000000000 : ℝ)^387
        have hw : |(4251316493/10000000000 : ℝ)|=(4251316493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4443724887/10000000000 : ℝ)|^515 ≤ (8495320624703/25000000000000 : ℝ)^387
        have hw : |(4443724887/10000000000 : ℝ)|=(4443724887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1110931101/2500000000 : ℝ)|^515 ≤ (33981277583671/100000000000000 : ℝ)^387
        have hw : |(1110931101/2500000000 : ℝ)|=(1110931101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59227/100000 : ℝ) ∧ (9939/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82909/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5613/50000 : ℝ) ^ (8239/2048 : ℝ) ≤ (15104402779592487/100000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^8239 ≤ (15104402779592487/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5613 : ℕ)^8239*100000000000000000000^2048 ≤ 15104402779592487^2048*50000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 15104402779592487 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (15104402779592487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1399/10000 : ℝ) ^ (8239/2048 : ℝ) ≤ (7323151814906417/20000000000000000000 : ℝ) := by
    have hpowers : (1399/10000 : ℝ)^8239 ≤ (7323151814906417/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1399 : ℕ)^8239*20000000000000000000^2048 ≤ 7323151814906417^2048*10000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 10000 7323151814906417 20000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/10000 : ℝ)) (X := (7323151814906417/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015104402779592487/50000000000000000000 : ℝ) ≤ (2000150165343231/2000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50015104402779592487/50000000000000000000 : ℝ)^2048 ≤ (2000150165343231/2000000000000000 : ℝ)^8239 := by
      have hnat : (50015104402779592487 : ℕ)^2048*2000000000000000^8239 ≤ 2000150165343231^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015104402779592487 50000000000000000000 2000150165343231 2000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000150165343231/2000000000000000 : ℝ)) (X := (50015104402779592487/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012930040463531143/25000000000000000000 : ℝ) ≤ (625080336141231/625000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (25012930040463531143/25000000000000000000 : ℝ)^2048 ≤ (625080336141231/625000000000000 : ℝ)^8239 := by
      have hnat : (25012930040463531143 : ℕ)^2048*625000000000000^8239 ≤ 625080336141231^8239*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012930040463531143 25000000000000000000 625080336141231 625000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625080336141231/625000000000000 : ℝ)) (X := (25012930040463531143/25000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007323151814906417/10000000000000000000 : ℝ) ≤ (10001819929803237/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (10007323151814906417/10000000000000000000 : ℝ)^2048 ≤ (10001819929803237/10000000000000000 : ℝ)^8239 := by
      have hnat : (10007323151814906417 : ℕ)^2048*10000000000000000^8239 ≤ 10001819929803237^8239*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007323151814906417 10000000000000000000 10001819929803237 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001819929803237/10000000000000000 : ℝ)) (X := (10007323151814906417/10000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15104402779592487/100000000000000000000 : ℝ) ≤ ((431719898965435467/431875000000000000 : ℝ)+2*(534551543541/276400000000000 : ℝ)*(5613/50000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (431719898965435467/431875000000000000 : ℝ)+2*(534551543541/276400000000000 : ℝ)*(5613/50000 : ℝ)=(2000150165343231/2000000000000000 : ℝ) by norm_num, show 1+2*(15104402779592487/100000000000000000000 : ℝ)=(50015104402779592487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7323151814906417/20000000000000000000 : ℝ)+(15104402779592487/100000000000000000000 : ℝ) ≤ ((431719898965435467/431875000000000000 : ℝ)+(534551543541/276400000000000 : ℝ)*((1399/10000 : ℝ)+(5613/50000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (431719898965435467/431875000000000000 : ℝ)+(534551543541/276400000000000 : ℝ)*((1399/10000 : ℝ)+(5613/50000 : ℝ))=(625080336141231/625000000000000 : ℝ) by norm_num, show 1+(7323151814906417/20000000000000000000 : ℝ)+(15104402779592487/100000000000000000000 : ℝ)=(25012930040463531143/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7323151814906417/20000000000000000000 : ℝ) ≤ ((431719898965435467/431875000000000000 : ℝ)+2*(534551543541/276400000000000 : ℝ)*(1399/10000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (431719898965435467/431875000000000000 : ℝ)+2*(534551543541/276400000000000 : ℝ)*(1399/10000 : ℝ)=(10001819929803237/10000000000000000 : ℝ) by norm_num, show 1+2*(7323151814906417/20000000000000000000 : ℝ)=(10007323151814906417/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (431719898965435467/431875000000000000 : ℝ)*(X 1 0+X 2 0)+(534551543541/276400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (431719898965435467/431875000000000000 : ℝ)) (alpha := (534551543541/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (431719898965435467/431875000000000000 : ℝ)*(X 0 1+X 2 1)+(534551543541/276400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (431719898965435467/431875000000000000 : ℝ)) (alpha := (534551543541/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (431719898965435467/431875000000000000 : ℝ)*(X 0 2+X 1 2)+(534551543541/276400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (431719898965435467/431875000000000000 : ℝ)) (alpha := (534551543541/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1041523937/5000000000 : ℝ)*X 0 0+(5377619557/10000000000 : ℝ)*X 0 1+(1344404893/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647493161/5000000000 : ℝ)*X 1 0+(-2194858927/10000000000 : ℝ)*X 1 1+(2688809829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647493347/5000000000 : ℝ)*X 2 0+(1344404837/2500000000 : ℝ)*X 2 1+(-1097429423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((897366327/2000000000 : ℝ)*X 0 0+(1081527569/2500000000 : ℝ)*X 0 1+(4326110411/10000000000 : ℝ)*X 0 2+(897366327/2000000000 : ℝ)*X 1 0+(1081527569/2500000000 : ℝ)*X 1 1+(4326110411/10000000000 : ℝ)*X 1 2+(897366327/2000000000 : ℝ)*X 2 0+(1081527569/2500000000 : ℝ)*X 2 1+(4326110411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2344660043/10000000000 : ℝ)*X 0 0+(5279805643/10000000000 : ℝ)*X 0 1+(5279805379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682120847/5000000000 : ℝ)*X 1 0+(-2233039971/10000000000 : ℝ)*X 1 1+(5279805309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364241133/10000000000 : ℝ)*X 2 0+(2639902919/5000000000 : ℝ)*X 2 1+(-446608003/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2134657019/5000000000 : ℝ)*X 0 0+(4434847681/10000000000 : ℝ)*X 0 1+(4434847363/10000000000 : ℝ)*X 0 2+(2134657019/5000000000 : ℝ)*X 1 0+(4434847681/10000000000 : ℝ)*X 1 1+(4434847363/10000000000 : ℝ)*X 1 2+(2134657019/5000000000 : ℝ)*X 2 0+(4434847681/10000000000 : ℝ)*X 2 1+(4434847363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2290070481/10000000000 : ℝ)*X 0 0+(162920953/312500000 : ℝ)*X 0 1+(1077443349/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288187663/10000000000 : ℝ)*X 1 0+(-273880199/1250000000 : ℝ)*X 1 1+(1346804167/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322046939/2500000000 : ℝ)*X 2 0+(5387216693/10000000000 : ℝ)*X 2 1+(-1095520717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4507900391/10000000000 : ℝ)*X 0 0+(431543541/1000000000 : ℝ)*X 0 1+(2157717763/5000000000 : ℝ)*X 0 2+(4507900391/10000000000 : ℝ)*X 1 0+(431543541/1000000000 : ℝ)*X 1 1+(2157717763/5000000000 : ℝ)*X 1 2+(4507900391/10000000000 : ℝ)*X 2 0+(431543541/1000000000 : ℝ)*X 2 1+(2157717763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2138018927/10000000000 : ℝ)*X 0 0+(340162781/625000000 : ℝ)*X 0 1+(2635907539/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369896207/10000000000 : ℝ)*X 1 0+(-2236099743/10000000000 : ℝ)*X 1 1+(5271815661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342474011/2500000000 : ℝ)*X 2 0+(5271815803/10000000000 : ℝ)*X 2 1+(-559024943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4251316493/10000000000 : ℝ)*X 0 0+(4443724887/10000000000 : ℝ)*X 0 1+(1110931101/2500000000 : ℝ)*X 0 2+(4251316493/10000000000 : ℝ)*X 1 0+(4443724887/10000000000 : ℝ)*X 1 1+(1110931101/2500000000 : ℝ)*X 1 2+(4251316493/10000000000 : ℝ)*X 2 0+(4443724887/10000000000 : ℝ)*X 2 1+(1110931101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-1679482292902625326415596308429/2699218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (47995059/50000000000000 : ℝ)*(upper0) + (64796647/50000000000000 : ℝ)*(upper1) + (21700943/25000000000000 : ℝ)*(upper2) + (180056553/100000000000000 : ℝ)*(upper3) + (1920397460495691/50000000000000 : ℝ)*(major0) + (1920397460495691/50000000000000 : ℝ)*(major1) + (1920397460495691/50000000000000 : ℝ)*(major2) + (4404636303/50000000000000 : ℝ)*(sp1) + (7159926173/50000000000000 : ℝ)*(sp3) + (2550290469970077/50000000000000 : ℝ)*(sp4) + (1275143032666887/25000000000000 : ℝ)*(sp5) + (2550168160464699/50000000000000 : ℝ)*(sp6) + (650433733186047/25000000000000 : ℝ)*(sp7) + (48923802151/20000000000000 : ℝ)*(sp14) + (1300874626298267/50000000000000 : ℝ)*(f.failure) + (2550290469970077/50000000000000 : ℝ)*(f.sum) + (48521178678711/6910000000000000000000000000 : ℝ)*base65 + (396613376778007731/43187500000000000000000000000000 : ℝ)*base68 + (419707494436367269/43187500000000000000000000000000 : ℝ)*base69 + (78842399307492269/43187500000000000000000000000000 : ℝ)*base71 + (9115894337309/6910000000000000000000000000 : ℝ)*base74 + (17043970350492269/43187500000000000000000000000000 : ℝ)*base75 + (362375259331867269/43187500000000000000000000000000 : ℝ)*base77 + (414350386590320231/43187500000000000000000000000000 : ℝ)*base80 + (8941216212369/6910000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (25516473/2500000000000000000000 : ℝ)*base90 + (25516473/2500000000000000000000 : ℝ)*base92 + (25516473/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59227/100000 : ℝ) ≤ (4092743186838327548772994443/6910000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3553051/4000000000000 : ℝ)*(upper0) + (8802087/20000000000000 : ℝ)*(upper2) + (3198783/100000000000000 : ℝ)*(upper3) + (43804833/25000000000000 : ℝ)*(upper4) + (6294489/25000000000000 : ℝ)*(upper5) + (1951686729695481/50000000000000 : ℝ)*(major0) + (1951686729695481/50000000000000 : ℝ)*(major1) + (1951686729695481/50000000000000 : ℝ)*(major2) + (2571431978198727/50000000000000 : ℝ)*(sp0) + (1028571952346389/20000000000000 : ℝ)*(sp1) + (5142818279660503/100000000000000 : ℝ)*(sp2) + (264413986934617/10000000000000 : ℝ)*(sp3) + (4194665509/100000000000000 : ℝ)*(sp5) + (45676736951/100000000000000 : ℝ)*(sp10) + (264413986934617/10000000000000 : ℝ)*(f.failure) + (2571431978198727/50000000000000 : ℝ)*(f.sum) + (13833029875919/6910000000000000000000000000 : ℝ)*base66 + (121690516285135121/43187500000000000000000000000000 : ℝ)*base68 + (198464708732635121/43187500000000000000000000000000 : ℝ)*base70 + (59160349314364879/43187500000000000000000000000000 : ℝ)*base71 + (73692592146161/6910000000000000000000000000 : ℝ)*base73 + (51392581862802379/43187500000000000000000000000000 : ℝ)*base75 + (103801950759239879/43187500000000000000000000000000 : ℝ)*base77 + (1249140247623822621/43187500000000000000000000000000 : ℝ)*base80 + (29625236773959/6910000000000000000000000000 : ℝ)*base82 + (1322877/500000000000000000000 : ℝ)*base89 + (1322877/500000000000000000000 : ℝ)*base91 + (1322877/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (9939/12500 : ℝ) ≤ (1073139695039162122574068198953/1349609375000000000000000000000 : ℝ) := by norm_num
    linear_combination (859059/2000000000000 : ℝ)*(upper0) + (65627493/100000000000000 : ℝ)*(lower3) + (83286237/100000000000000 : ℝ)*(upper4) + (1092927394167621/25000000000000 : ℝ)*(major0) + (1092927394167621/25000000000000 : ℝ)*(major1) + (1092927394167621/25000000000000 : ℝ)*(major2) + (4536528951/12500000000000 : ℝ)*(sp1) + (40031041179/50000000000000 : ℝ)*(sp2) + (952708421/2500000000000 : ℝ)*(sp3) + (125868737/10000000000000 : ℝ)*(sp4) + (5755522831138379/100000000000000 : ℝ)*(sp8) + (5755487797594141/100000000000000 : ℝ)*(sp9) + (5755444027743391/100000000000000 : ℝ)*(sp10) + (370169001187817/12500000000000 : ℝ)*(sp11) + (185086882364961/6250000000000 : ℝ)*(f.failure) + (5755524089825749/100000000000000 : ℝ)*(f.sum) + (1317998081189/215937500000000000000000000 : ℝ)*base66 + (136438321051643639/21593750000000000000000000000000 : ℝ)*base67 + (136855247411112389/21593750000000000000000000000000 : ℝ)*base69 + (99767582863174889/21593750000000000000000000000000 : ℝ)*base71 + (3650823167001/3455000000000000000000000000 : ℝ)*base73 + (240553343883081139/21593750000000000000000000000000 : ℝ)*base75 + (155805160950706139/21593750000000000000000000000000 : ℝ)*base77 + (724710511232174889/21593750000000000000000000000000 : ℝ)*base79 + (16827456250409/3455000000000000000000000000 : ℝ)*base82 + (905541/312500000000000000000 : ℝ)*base89 + (905541/312500000000000000000 : ℝ)*base91 + (905541/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82909/100000 : ℝ) ≤ (-17902586834395049535498660091593/21593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18219309/25000000000000 : ℝ)*(lower0) + (90046829/50000000000000 : ℝ)*(upper3) + (40186463/100000000000000 : ℝ)*(upper5) + (2203072397487067/50000000000000 : ℝ)*(major0) + (2203072397487067/50000000000000 : ℝ)*(major1) + (2203072397487067/50000000000000 : ℝ)*(major2) + (4596577139/50000000000000 : ℝ)*(sp0) + (42196339197/25000000000000 : ℝ)*(sp5) + (118252852583/100000000000000 : ℝ)*(sp7) + (17231194491/100000000000000 : ℝ)*(sp8) + (2927591061464683/50000000000000 : ℝ)*(sp12) + (2927519880960673/50000000000000 : ℝ)*(sp13) + (2927604273639067/50000000000000 : ℝ)*(sp14) + (373074779375411/12500000000000 : ℝ)*(sp15) + (298471648785587/10000000000000 : ℝ)*(f.failure) + (2927604273639067/50000000000000 : ℝ)*(f.sum) + (5735202727417/6910000000000000000000000000 : ℝ)*base65 + (235173588679044953/43187500000000000000000000000000 : ℝ)*base67 + (256116505515732453/43187500000000000000000000000000 : ℝ)*base69 + (132610953404982453/43187500000000000000000000000000 : ℝ)*base71 + (34061382726017/6910000000000000000000000000 : ℝ)*base73 + (1086546233343919953/43187500000000000000000000000000 : ℝ)*base75 + (91105675543607453/43187500000000000000000000000000 : ℝ)*base77 + (1138977933298705047/43187500000000000000000000000000 : ℝ)*base80 + (23659813071217/6910000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6399553/500000000000000000000 : ℝ)*base90 + (6399553/500000000000000000000 : ℝ)*base92 + (6399553/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1047_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59227/100000 : ℝ) else (9939/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82909/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1047_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1047_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59227/100000 : ℝ) else (9939/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82909/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1047_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1047_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1047_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59227/100000 : ℝ) else (9939/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82909/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
