-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1175_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:58.189252+00:00
-- url     : https://prove2.me/submissions/282d3f0c-2f09-4d4b-99fa-6a376bf9f89f

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
theorem support_rectangle_w1175_s3_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073874557/5000000000 : ℝ)*x 0 + (5425861873/10000000000 : ℝ)*x 1 + (1308773193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073874557/5000000000 : ℝ)^523 ≤ (203860188139/1562500000000 : ℝ)^395 := by
    have hnat : (1073874557 : ℕ)^523*1562500000000^395 ≤ 203860188139^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073874557 5000000000 203860188139 1562500000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425861873/10000000000 : ℝ)^523 ≤ (44506470909033/100000000000000 : ℝ)^395 := by
    have hnat : (5425861873 : ℕ)^523*100000000000000^395 ≤ 44506470909033^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425861873 10000000000 44506470909033 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308773193/2500000000 : ℝ)^523 ≤ (8489295404979/20000000000000 : ℝ)^395 := by
    have hnat : (1308773193 : ℕ)^523*20000000000000^395 ≤ 8489295404979^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308773193 2500000000 8489295404979 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073874557/5000000000 : ℝ), (5425861873/10000000000 : ℝ), (1308773193/2500000000 : ℝ)] ![(203860188139/1562500000000 : ℝ), (44506470909033/100000000000000 : ℝ), (8489295404979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073874557/5000000000 : ℝ)|^523 ≤ (203860188139/1562500000000 : ℝ)^395
        have hw : |(-1073874557/5000000000 : ℝ)|=(1073874557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425861873/10000000000 : ℝ)|^523 ≤ (44506470909033/100000000000000 : ℝ)^395
        have hw : |(5425861873/10000000000 : ℝ)|=(5425861873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308773193/2500000000 : ℝ)|^523 ≤ (8489295404979/20000000000000 : ℝ)^395
        have hw : |(1308773193/2500000000 : ℝ)|=(1308773193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s3_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1070602179/2000000000 : ℝ)*x 0 + (-89807807/400000000 : ℝ)*x 1 + (209403703/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070602179/2000000000 : ℝ)^523 ≤ (21858491295637/50000000000000 : ℝ)^395 := by
    have hnat : (1070602179 : ℕ)^523*50000000000000^395 ≤ 21858491295637^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070602179 2000000000 21858491295637 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89807807/400000000 : ℝ)^523 ≤ (13836542481607/100000000000000 : ℝ)^395 := by
    have hnat : (89807807 : ℕ)^523*100000000000000^395 ≤ 13836542481607^395*400000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89807807 400000000 13836542481607 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209403703/400000000 : ℝ)^523 ≤ (42446474910003/100000000000000 : ℝ)^395 := by
    have hnat : (209403703 : ℕ)^523*100000000000000^395 ≤ 42446474910003^395*400000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209403703 400000000 42446474910003 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070602179/2000000000 : ℝ), (-89807807/400000000 : ℝ), (209403703/400000000 : ℝ)] ![(21858491295637/50000000000000 : ℝ), (13836542481607/100000000000000 : ℝ), (42446474910003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070602179/2000000000 : ℝ)|^523 ≤ (21858491295637/50000000000000 : ℝ)^395
        have hw : |(1070602179/2000000000 : ℝ)|=(1070602179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89807807/400000000 : ℝ)|^523 ≤ (13836542481607/100000000000000 : ℝ)^395
        have hw : |(-89807807/400000000 : ℝ)|=(89807807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209403703/400000000 : ℝ)|^523 ≤ (42446474910003/100000000000000 : ℝ)^395
        have hw : |(209403703/400000000 : ℝ)|=(209403703/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s3_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5353010981/10000000000 : ℝ)*x 0 + (5235092559/10000000000 : ℝ)*x 1 + (-1122597541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353010981/10000000000 : ℝ)^523 ≤ (8743396704243/20000000000000 : ℝ)^395 := by
    have hnat : (5353010981 : ℕ)^523*20000000000000^395 ≤ 8743396704243^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353010981 10000000000 8743396704243 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235092559/10000000000 : ℝ)^523 ≤ (10611618684559/25000000000000 : ℝ)^395 := by
    have hnat : (5235092559 : ℕ)^523*25000000000000^395 ≤ 10611618684559^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235092559 10000000000 10611618684559 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122597541/5000000000 : ℝ)^523 ≤ (3459135430687/25000000000000 : ℝ)^395 := by
    have hnat : (1122597541 : ℕ)^523*25000000000000^395 ≤ 3459135430687^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122597541 5000000000 3459135430687 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353010981/10000000000 : ℝ), (5235092559/10000000000 : ℝ), (-1122597541/5000000000 : ℝ)] ![(8743396704243/20000000000000 : ℝ), (10611618684559/25000000000000 : ℝ), (3459135430687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353010981/10000000000 : ℝ)|^523 ≤ (8743396704243/20000000000000 : ℝ)^395
        have hw : |(5353010981/10000000000 : ℝ)|=(5353010981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235092559/10000000000 : ℝ)|^523 ≤ (10611618684559/25000000000000 : ℝ)^395
        have hw : |(5235092559/10000000000 : ℝ)|=(5235092559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122597541/5000000000 : ℝ)|^523 ≤ (3459135430687/25000000000000 : ℝ)^395
        have hw : |(-1122597541/5000000000 : ℝ)|=(1122597541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s3_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2178994739/5000000000 : ℝ)*x 0 + (4171122743/10000000000 : ℝ)*x 1 + (35571181/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178994739/5000000000 : ℝ)^523 ≤ (6659270103711/20000000000000 : ℝ)^395 := by
    have hnat : (2178994739 : ℕ)^523*20000000000000^395 ≤ 6659270103711^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178994739 5000000000 6659270103711 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171122743/10000000000 : ℝ)^523 ≤ (7854810521559/25000000000000 : ℝ)^395 := by
    have hnat : (4171122743 : ℕ)^523*25000000000000^395 ≤ 7854810521559^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171122743 10000000000 7854810521559 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35571181/78125000 : ℝ)^523 ≤ (17642203687961/50000000000000 : ℝ)^395 := by
    have hnat : (35571181 : ℕ)^523*50000000000000^395 ≤ 17642203687961^395*78125000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35571181 78125000 17642203687961 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178994739/5000000000 : ℝ), (4171122743/10000000000 : ℝ), (35571181/78125000 : ℝ)] ![(6659270103711/20000000000000 : ℝ), (7854810521559/25000000000000 : ℝ), (17642203687961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178994739/5000000000 : ℝ)|^523 ≤ (6659270103711/20000000000000 : ℝ)^395
        have hw : |(2178994739/5000000000 : ℝ)|=(2178994739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171122743/10000000000 : ℝ)|^523 ≤ (7854810521559/25000000000000 : ℝ)^395
        have hw : |(4171122743/10000000000 : ℝ)|=(4171122743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35571181/78125000 : ℝ)|^523 ≤ (17642203687961/50000000000000 : ℝ)^395
        have hw : |(35571181/78125000 : ℝ)|=(35571181/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s3_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-268470699/1250000000 : ℝ)*x 0 + (130895407/250000000 : ℝ)*x 1 + (2712567237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268470699/1250000000 : ℝ)^523 ≤ (2609436915661/20000000000000 : ℝ)^395 := by
    have hnat : (268470699 : ℕ)^523*20000000000000^395 ≤ 2609436915661^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268470699 1250000000 2609436915661 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130895407/250000000 : ℝ)^523 ≤ (42454244411531/100000000000000 : ℝ)^395 := by
    have hnat : (130895407 : ℕ)^523*100000000000000^395 ≤ 42454244411531^395*250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130895407 250000000 42454244411531 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712567237/5000000000 : ℝ)^523 ≤ (11124642749119/25000000000000 : ℝ)^395 := by
    have hnat : (2712567237 : ℕ)^523*25000000000000^395 ≤ 11124642749119^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712567237 5000000000 11124642749119 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268470699/1250000000 : ℝ), (130895407/250000000 : ℝ), (2712567237/5000000000 : ℝ)] ![(2609436915661/20000000000000 : ℝ), (42454244411531/100000000000000 : ℝ), (11124642749119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268470699/1250000000 : ℝ)|^523 ≤ (2609436915661/20000000000000 : ℝ)^395
        have hw : |(-268470699/1250000000 : ℝ)|=(268470699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130895407/250000000 : ℝ)|^523 ≤ (42454244411531/100000000000000 : ℝ)^395
        have hw : |(130895407/250000000 : ℝ)|=(130895407/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712567237/5000000000 : ℝ)|^523 ≤ (11124642749119/25000000000000 : ℝ)^395
        have hw : |(2712567237/5000000000 : ℝ)|=(2712567237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s3_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652282493/5000000000 : ℝ)*x 0 + (-513788479/2500000000 : ℝ)*x 1 + (5425134329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652282493/5000000000 : ℝ)^523 ≤ (172775576487/400000000000 : ℝ)^395 := by
    have hnat : (2652282493 : ℕ)^523*400000000000^395 ≤ 172775576487^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652282493 5000000000 172775576487 400000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513788479/2500000000 : ℝ)^523 ≤ (12307536447449/100000000000000 : ℝ)^395 := by
    have hnat : (513788479 : ℕ)^523*100000000000000^395 ≤ 12307536447449^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513788479 2500000000 12307536447449 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425134329/10000000000 : ℝ)^523 ≤ (44498569421739/100000000000000 : ℝ)^395 := by
    have hnat : (5425134329 : ℕ)^523*100000000000000^395 ≤ 44498569421739^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425134329 10000000000 44498569421739 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652282493/5000000000 : ℝ), (-513788479/2500000000 : ℝ), (5425134329/10000000000 : ℝ)] ![(172775576487/400000000000 : ℝ), (12307536447449/100000000000000 : ℝ), (44498569421739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652282493/5000000000 : ℝ)|^523 ≤ (172775576487/400000000000 : ℝ)^395
        have hw : |(2652282493/5000000000 : ℝ)|=(2652282493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513788479/2500000000 : ℝ)|^523 ≤ (12307536447449/100000000000000 : ℝ)^395
        have hw : |(-513788479/2500000000 : ℝ)|=(513788479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425134329/10000000000 : ℝ)|^523 ≤ (44498569421739/100000000000000 : ℝ)^395
        have hw : |(5425134329/10000000000 : ℝ)|=(5425134329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s3_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1326141541/2500000000 : ℝ)*x 0 + (5425133249/10000000000 : ℝ)*x 1 + (-16055889/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326141541/2500000000 : ℝ)^523 ≤ (21596953411149/50000000000000 : ℝ)^395 := by
    have hnat : (1326141541 : ℕ)^523*50000000000000^395 ≤ 21596953411149^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326141541 2500000000 21596953411149 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425133249/10000000000 : ℝ)^523 ≤ (44498557692661/100000000000000 : ℝ)^395 := by
    have hnat : (5425133249 : ℕ)^523*100000000000000^395 ≤ 44498557692661^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425133249 10000000000 44498557692661 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16055889/78125000 : ℝ)^523 ≤ (384610483257/3125000000000 : ℝ)^395 := by
    have hnat : (16055889 : ℕ)^523*3125000000000^395 ≤ 384610483257^395*78125000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16055889 78125000 384610483257 3125000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326141541/2500000000 : ℝ), (5425133249/10000000000 : ℝ), (-16055889/78125000 : ℝ)] ![(21596953411149/50000000000000 : ℝ), (44498557692661/100000000000000 : ℝ), (384610483257/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326141541/2500000000 : ℝ)|^523 ≤ (21596953411149/50000000000000 : ℝ)^395
        have hw : |(1326141541/2500000000 : ℝ)|=(1326141541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425133249/10000000000 : ℝ)|^523 ≤ (44498557692661/100000000000000 : ℝ)^395
        have hw : |(5425133249/10000000000 : ℝ)|=(5425133249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16055889/78125000 : ℝ)|^523 ≤ (384610483257/3125000000000 : ℝ)^395
        have hw : |(-16055889/78125000 : ℝ)|=(16055889/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s3_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (871604439/2000000000 : ℝ)*x 0 + (2275831387/5000000000 : ℝ)*x 1 + (417257951/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871604439/2000000000 : ℝ)^523 ≤ (16648340744439/50000000000000 : ℝ)^395 := by
    have hnat : (871604439 : ℕ)^523*50000000000000^395 ≤ 16648340744439^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871604439 2000000000 16648340744439 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275831387/5000000000 : ℝ)^523 ≤ (35269546531171/100000000000000 : ℝ)^395 := by
    have hnat : (2275831387 : ℕ)^523*100000000000000^395 ≤ 35269546531171^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275831387 5000000000 35269546531171 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417257951/1000000000 : ℝ)^523 ≤ (31433771965169/100000000000000 : ℝ)^395 := by
    have hnat : (417257951 : ℕ)^523*100000000000000^395 ≤ 31433771965169^395*1000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417257951 1000000000 31433771965169 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871604439/2000000000 : ℝ), (2275831387/5000000000 : ℝ), (417257951/1000000000 : ℝ)] ![(16648340744439/50000000000000 : ℝ), (35269546531171/100000000000000 : ℝ), (31433771965169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871604439/2000000000 : ℝ)|^523 ≤ (16648340744439/50000000000000 : ℝ)^395
        have hw : |(871604439/2000000000 : ℝ)|=(871604439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2275831387/5000000000 : ℝ)|^523 ≤ (35269546531171/100000000000000 : ℝ)^395
        have hw : |(2275831387/5000000000 : ℝ)|=(2275831387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417257951/1000000000 : ℝ)|^523 ≤ (31433771965169/100000000000000 : ℝ)^395
        have hw : |(417257951/1000000000 : ℝ)|=(417257951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8203/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10731/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8203/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8203/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8203/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8203/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8203/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8203/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9217/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (588685500478491/10000000000000000000 : ℝ) := by
    have hpowers : (9217/100000 : ℝ)^8367 ≤ (588685500478491/10000000000000000000 : ℝ)^2048 := by
      have hnat : (9217 : ℕ)^8367*10000000000000000000^2048 ≤ 588685500478491^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9217 100000 588685500478491 10000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9217/100000 : ℝ)) (X := (588685500478491/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8203/50000 : ℝ) ^ (8367/2048 : ℝ) ≤ (31038693173325909/50000000000000000000 : ℝ) := by
    have hpowers : (8203/50000 : ℝ)^8367 ≤ (31038693173325909/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8203 : ℕ)^8367*50000000000000000000^2048 ≤ 31038693173325909^2048*50000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8203 50000 31038693173325909 50000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8203/50000 : ℝ)) (X := (31038693173325909/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000588685500478491/5000000000000000000 : ℝ) ≤ (10000288173612379/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (5000588685500478491/5000000000000000000 : ℝ)^2048 ≤ (10000288173612379/10000000000000000 : ℝ)^8367 := by
      have hnat : (5000588685500478491 : ℕ)^2048*10000000000000000^8367 ≤ 10000288173612379^8367*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000588685500478491 5000000000000000000 10000288173612379 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000288173612379/10000000000000000 : ℝ)) (X := (5000588685500478491/5000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12508495530168929591/12500000000000000000 : ℝ) ≤ (5000831570803033/5000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (12508495530168929591/12500000000000000000 : ℝ)^2048 ≤ (5000831570803033/5000000000000000 : ℝ)^8367 := by
      have hnat : (12508495530168929591 : ℕ)^2048*5000000000000000^8367 ≤ 5000831570803033^8367*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508495530168929591 12500000000000000000 5000831570803033 5000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000831570803033/5000000000000000 : ℝ)) (X := (12508495530168929591/12500000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25031038693173325909/25000000000000000000 : ℝ) ≤ (10003038109599753/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (25031038693173325909/25000000000000000000 : ℝ)^2048 ≤ (10003038109599753/10000000000000000 : ℝ)^8367 := by
      have hnat : (25031038693173325909 : ℕ)^2048*10000000000000000^8367 ≤ 10003038109599753^8367*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25031038693173325909 25000000000000000000 10003038109599753 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003038109599753/10000000000000000 : ℝ)) (X := (25031038693173325909/25000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(588685500478491/10000000000000000000 : ℝ) ≤ ((5528209655392597421/5530000000000000000 : ℝ)+2*(1374967993687/718900000000000 : ℝ)*(9217/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (5528209655392597421/5530000000000000000 : ℝ)+2*(1374967993687/718900000000000 : ℝ)*(9217/100000 : ℝ)=(10000288173612379/10000000000000000 : ℝ) by norm_num, show 1+2*(588685500478491/10000000000000000000 : ℝ)=(5000588685500478491/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31038693173325909/50000000000000000000 : ℝ)+(588685500478491/10000000000000000000 : ℝ) ≤ ((5528209655392597421/5530000000000000000 : ℝ)+(1374967993687/718900000000000 : ℝ)*((8203/50000 : ℝ)+(9217/100000 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (5528209655392597421/5530000000000000000 : ℝ)+(1374967993687/718900000000000 : ℝ)*((8203/50000 : ℝ)+(9217/100000 : ℝ))=(5000831570803033/5000000000000000 : ℝ) by norm_num, show 1+(31038693173325909/50000000000000000000 : ℝ)+(588685500478491/10000000000000000000 : ℝ)=(12508495530168929591/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31038693173325909/50000000000000000000 : ℝ) ≤ ((5528209655392597421/5530000000000000000 : ℝ)+2*(1374967993687/718900000000000 : ℝ)*(8203/50000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (5528209655392597421/5530000000000000000 : ℝ)+2*(1374967993687/718900000000000 : ℝ)*(8203/50000 : ℝ)=(10003038109599753/10000000000000000 : ℝ) by norm_num, show 1+2*(31038693173325909/50000000000000000000 : ℝ)=(25031038693173325909/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5528209655392597421/5530000000000000000 : ℝ)*(X 1 0+X 2 0)+(1374967993687/718900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (9217/100000 : ℝ)) (hi := (8203/50000 : ℝ)) (c := (5528209655392597421/5530000000000000000 : ℝ)) (alpha := (1374967993687/718900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5528209655392597421/5530000000000000000 : ℝ)*(X 0 1+X 2 1)+(1374967993687/718900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (9217/100000 : ℝ)) (hi := (8203/50000 : ℝ)) (c := (5528209655392597421/5530000000000000000 : ℝ)) (alpha := (1374967993687/718900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5528209655392597421/5530000000000000000 : ℝ)*(X 0 2+X 1 2)+(1374967993687/718900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (9217/100000 : ℝ)) (hi := (8203/50000 : ℝ)) (c := (5528209655392597421/5530000000000000000 : ℝ)) (alpha := (1374967993687/718900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1073874557/5000000000 : ℝ)*X 0 0+(5425861873/10000000000 : ℝ)*X 0 1+(1308773193/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070602179/2000000000 : ℝ)*X 1 0+(-89807807/400000000 : ℝ)*X 1 1+(209403703/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353010981/10000000000 : ℝ)*X 2 0+(5235092559/10000000000 : ℝ)*X 2 1+(-1122597541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178994739/5000000000 : ℝ)*X 0 0+(4171122743/10000000000 : ℝ)*X 0 1+(35571181/78125000 : ℝ)*X 0 2+(2178994739/5000000000 : ℝ)*X 1 0+(4171122743/10000000000 : ℝ)*X 1 1+(35571181/78125000 : ℝ)*X 1 2+(2178994739/5000000000 : ℝ)*X 2 0+(4171122743/10000000000 : ℝ)*X 2 1+(35571181/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268470699/1250000000 : ℝ)*X 0 0+(130895407/250000000 : ℝ)*X 0 1+(2712567237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652282493/5000000000 : ℝ)*X 1 0+(-513788479/2500000000 : ℝ)*X 1 1+(5425134329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326141541/2500000000 : ℝ)*X 2 0+(5425133249/10000000000 : ℝ)*X 2 1+(-16055889/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871604439/2000000000 : ℝ)*X 0 0+(2275831387/5000000000 : ℝ)*X 0 1+(417257951/1000000000 : ℝ)*X 0 2+(871604439/2000000000 : ℝ)*X 1 0+(2275831387/5000000000 : ℝ)*X 1 1+(417257951/1000000000 : ℝ)*X 1 2+(871604439/2000000000 : ℝ)*X 2 0+(2275831387/5000000000 : ℝ)*X 2 1+(417257951/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (669110589298645727470800651/256750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (788787279/100000000000000 : ℝ)*(base19) + (798587921/100000000000000 : ℝ)*(base23) + (39834559/100000000000000 : ℝ)*(lower2) + (3711141/10000000000000 : ℝ)*(upper3) + (24501729/25000000000000 : ℝ)*(upper5) + (1964962983827703/50000000000000 : ℝ)*(major0) + (1964962983827703/50000000000000 : ℝ)*(major1) + (1964962983827703/50000000000000 : ℝ)*(major2) + (655243494874307/12500000000000 : ℝ)*(sp0) + (5241959560740643/100000000000000 : ℝ)*(sp1) + (5241959550940001/100000000000000 : ℝ)*(sp2) + (2617886044706739/100000000000000 : ℝ)*(sp3) + (6195266733/50000000000000 : ℝ)*(sp4) + (545420687/10000000000000 : ℝ)*(sp7) + (2617891498913609/100000000000000 : ℝ)*(f.failure) + (2620980174763961/50000000000000 : ℝ)*(f.sum) + (37224933591049/17972500000000000000000000000 : ℝ)*base66 + (47706495564486398481/3594500000000000000000000000000000 : ℝ)*base68 + (5932974378800101519/3594500000000000000000000000000000 : ℝ)*base69 + (22992339543750398481/3594500000000000000000000000000000 : ℝ)*base72 + (16688960129409/17972500000000000000000000000 : ℝ)*base74 + (12143934376150398481/3594500000000000000000000000000000 : ℝ)*base76 + (20224889320877601519/3594500000000000000000000000000000 : ℝ)*base77 + (66736317707135898481/3594500000000000000000000000000000 : ℝ)*base80 + (12118057161159/4493125000000000000000000000 : ℝ)*base81 + (14431573/2000000000000000000000 : ℝ)*base89 + (14431573/2000000000000000000000 : ℝ)*base91 + (14431573/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14837471988547040623579349829/1797250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486173859/50000000000000 : ℝ)*(base19) + (280969349/12500000000000 : ℝ)*(base23) + (115782801/100000000000000 : ℝ)*(upper3) + (178549/2500000000000 : ℝ)*(lower4) + (79725519/100000000000000 : ℝ)*(upper5) + (3960033781216609/100000000000000 : ℝ)*(major0) + (3960033781216609/100000000000000 : ℝ)*(major1) + (3960033781216609/100000000000000 : ℝ)*(major2) + (6642289851/50000000000000 : ℝ)*(sp1) + (11511131367/50000000000000 : ℝ)*(sp2) + (1320529922020907/25000000000000 : ℝ)*(sp4) + (330131589447263/6250000000000 : ℝ)*(sp5) + (2641047209033051/50000000000000 : ℝ)*(sp6) + (2637947599161159/100000000000000 : ℝ)*(sp7) + (2637947599161159/100000000000000 : ℝ)*(f.failure) + (1320529922020907/25000000000000 : ℝ)*(f.sum) + (32008743952011/17972500000000000000000000000 : ℝ)*base66 + (29132317260669250057/7189000000000000000000000000000000 : ℝ)*base67 + (19503479530885250057/7189000000000000000000000000000000 : ℝ)*base69 + (30218923992516250057/7189000000000000000000000000000000 : ℝ)*base71 + (325256778152777/35945000000000000000000000000 : ℝ)*base74 + (1059831181604749943/7189000000000000000000000000000000 : ℝ)*base76 + (10100734636160250057/7189000000000000000000000000000000 : ℝ)*base77 + (66065388776373250057/7189000000000000000000000000000000 : ℝ)*base79 + (58396512649127/35945000000000000000000000000 : ℝ)*base82 + (4131077/2000000000000000000000 : ℝ)*base90 + (4131077/2000000000000000000000 : ℝ)*base92 + (4131077/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1175_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8203/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10731/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1175_s4_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-430098903/2000000000 : ℝ)*x 0 + (5400355077/10000000000 : ℝ)*x 1 + (5258802729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430098903/2000000000 : ℝ)^523 ≤ (3267284663699/25000000000000 : ℝ)^395 := by
    have hnat : (430098903 : ℕ)^523*25000000000000^395 ≤ 3267284663699^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430098903 2000000000 3267284663699 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400355077/10000000000 : ℝ)^523 ≤ (44229659708941/100000000000000 : ℝ)^395 := by
    have hnat : (5400355077 : ℕ)^523*100000000000000^395 ≤ 44229659708941^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400355077 10000000000 44229659708941 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258802729/10000000000 : ℝ)^523 ≤ (21350600809919/50000000000000 : ℝ)^395 := by
    have hnat : (5258802729 : ℕ)^523*50000000000000^395 ≤ 21350600809919^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258802729 10000000000 21350600809919 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430098903/2000000000 : ℝ), (5400355077/10000000000 : ℝ), (5258802729/10000000000 : ℝ)] ![(3267284663699/25000000000000 : ℝ), (44229659708941/100000000000000 : ℝ), (21350600809919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430098903/2000000000 : ℝ)|^523 ≤ (3267284663699/25000000000000 : ℝ)^395
        have hw : |(-430098903/2000000000 : ℝ)|=(430098903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400355077/10000000000 : ℝ)|^523 ≤ (44229659708941/100000000000000 : ℝ)^395
        have hw : |(5400355077/10000000000 : ℝ)|=(5400355077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258802729/10000000000 : ℝ)|^523 ≤ (21350600809919/50000000000000 : ℝ)^395
        have hw : |(5258802729/10000000000 : ℝ)|=(5258802729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s4_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5346621017/10000000000 : ℝ)*x 0 + (-2222405961/10000000000 : ℝ)*x 1 + (2629401533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346621017/10000000000 : ℝ)^523 ≤ (43647900546527/100000000000000 : ℝ)^395 := by
    have hnat : (5346621017 : ℕ)^523*100000000000000^395 ≤ 43647900546527^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346621017 10000000000 43647900546527 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222405961/10000000000 : ℝ)^523 ≤ (1365089419209/10000000000000 : ℝ)^395 := by
    have hnat : (2222405961 : ℕ)^523*10000000000000^395 ≤ 1365089419209^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222405961 10000000000 1365089419209 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629401533/5000000000 : ℝ)^523 ≤ (42701205242999/100000000000000 : ℝ)^395 := by
    have hnat : (2629401533 : ℕ)^523*100000000000000^395 ≤ 42701205242999^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629401533 5000000000 42701205242999 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346621017/10000000000 : ℝ), (-2222405961/10000000000 : ℝ), (2629401533/5000000000 : ℝ)] ![(43647900546527/100000000000000 : ℝ), (1365089419209/10000000000000 : ℝ), (42701205242999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346621017/10000000000 : ℝ)|^523 ≤ (43647900546527/100000000000000 : ℝ)^395
        have hw : |(5346621017/10000000000 : ℝ)|=(5346621017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2222405961/10000000000 : ℝ)|^523 ≤ (1365089419209/10000000000000 : ℝ)^395
        have hw : |(-2222405961/10000000000 : ℝ)|=(2222405961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629401533/5000000000 : ℝ)|^523 ≤ (42701205242999/100000000000000 : ℝ)^395
        have hw : |(2629401533/5000000000 : ℝ)|=(2629401533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s4_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5346620911/10000000000 : ℝ)*x 0 + (164337611/312500000 : ℝ)*x 1 + (-111120273/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346620911/10000000000 : ℝ)^523 ≤ (8729579880153/20000000000000 : ℝ)^395 := by
    have hnat : (5346620911 : ℕ)^523*20000000000000^395 ≤ 8729579880153^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346620911 10000000000 8729579880153 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164337611/312500000 : ℝ)^523 ≤ (42701210468093/100000000000000 : ℝ)^395 := by
    have hnat : (164337611 : ℕ)^523*100000000000000^395 ≤ 42701210468093^395*312500000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164337611 312500000 42701210468093 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111120273/500000000 : ℝ)^523 ≤ (13650890117537/100000000000000 : ℝ)^395 := by
    have hnat : (111120273 : ℕ)^523*100000000000000^395 ≤ 13650890117537^395*500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111120273 500000000 13650890117537 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346620911/10000000000 : ℝ), (164337611/312500000 : ℝ), (-111120273/500000000 : ℝ)] ![(8729579880153/20000000000000 : ℝ), (42701210468093/100000000000000 : ℝ), (13650890117537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346620911/10000000000 : ℝ)|^523 ≤ (8729579880153/20000000000000 : ℝ)^395
        have hw : |(5346620911/10000000000 : ℝ)|=(5346620911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164337611/312500000 : ℝ)|^523 ≤ (42701210468093/100000000000000 : ℝ)^395
        have hw : |(164337611/312500000 : ℝ)|=(164337611/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111120273/500000000 : ℝ)|^523 ≤ (13650890117537/100000000000000 : ℝ)^395
        have hw : |(-111120273/500000000 : ℝ)|=(111120273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s4_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (871926401/2000000000 : ℝ)*x 0 + (2110092939/5000000000 : ℝ)*x 1 + (562953013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871926401/2000000000 : ℝ)^523 ≤ (16656483787329/50000000000000 : ℝ)^395 := by
    have hnat : (871926401 : ℕ)^523*50000000000000^395 ≤ 16656483787329^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871926401 2000000000 16656483787329 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110092939/5000000000 : ℝ)^523 ≤ (7977375772417/25000000000000 : ℝ)^395 := by
    have hnat : (2110092939 : ℕ)^523*25000000000000^395 ≤ 7977375772417^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110092939 5000000000 7977375772417 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562953013/1250000000 : ℝ)^523 ≤ (8694382329589/25000000000000 : ℝ)^395 := by
    have hnat : (562953013 : ℕ)^523*25000000000000^395 ≤ 8694382329589^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562953013 1250000000 8694382329589 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871926401/2000000000 : ℝ), (2110092939/5000000000 : ℝ), (562953013/1250000000 : ℝ)] ![(16656483787329/50000000000000 : ℝ), (7977375772417/25000000000000 : ℝ), (8694382329589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871926401/2000000000 : ℝ)|^523 ≤ (16656483787329/50000000000000 : ℝ)^395
        have hw : |(871926401/2000000000 : ℝ)|=(871926401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110092939/5000000000 : ℝ)|^523 ≤ (7977375772417/25000000000000 : ℝ)^395
        have hw : |(2110092939/5000000000 : ℝ)|=(2110092939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562953013/1250000000 : ℝ)|^523 ≤ (8694382329589/25000000000000 : ℝ)^395
        have hw : |(562953013/1250000000 : ℝ)|=(562953013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s4_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075250613/5000000000 : ℝ)*x 0 + (1051840429/2000000000 : ℝ)*x 1 + (337497131/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075250613/5000000000 : ℝ)^523 ≤ (1633649081957/12500000000000 : ℝ)^395 := by
    have hnat : (1075250613 : ℕ)^523*12500000000000^395 ≤ 1633649081957^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075250613 5000000000 1633649081957 12500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051840429/2000000000 : ℝ)^523 ≤ (21352747941287/50000000000000 : ℝ)^395 := by
    have hnat : (1051840429 : ℕ)^523*50000000000000^395 ≤ 21352747941287^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051840429 2000000000 21352747941287 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337497131/625000000 : ℝ)^523 ≤ (11056327864887/25000000000000 : ℝ)^395 := by
    have hnat : (337497131 : ℕ)^523*25000000000000^395 ≤ 11056327864887^395*625000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337497131 625000000 11056327864887 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075250613/5000000000 : ℝ), (1051840429/2000000000 : ℝ), (337497131/625000000 : ℝ)] ![(1633649081957/12500000000000 : ℝ), (21352747941287/50000000000000 : ℝ), (11056327864887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075250613/5000000000 : ℝ)|^523 ≤ (1633649081957/12500000000000 : ℝ)^395
        have hw : |(-1075250613/5000000000 : ℝ)|=(1075250613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051840429/2000000000 : ℝ)|^523 ≤ (21352747941287/50000000000000 : ℝ)^395
        have hw : |(1051840429/2000000000 : ℝ)|=(1051840429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337497131/625000000 : ℝ)|^523 ≤ (11056327864887/25000000000000 : ℝ)^395
        have hw : |(337497131/625000000 : ℝ)|=(337497131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s4_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2655336947/5000000000 : ℝ)*x 0 + (-208125447/1000000000 : ℝ)*x 1 + (5399954157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655336947/5000000000 : ℝ)^523 ≤ (8651953859019/20000000000000 : ℝ)^395 := by
    have hnat : (2655336947 : ℕ)^523*20000000000000^395 ≤ 8651953859019^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655336947 5000000000 8651953859019 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208125447/1000000000 : ℝ)^523 ≤ (12514918562901/100000000000000 : ℝ)^395 := by
    have hnat : (208125447 : ℕ)^523*100000000000000^395 ≤ 12514918562901^395*1000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208125447 1000000000 12514918562901 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399954157/10000000000 : ℝ)^523 ≤ (1769012484841/4000000000000 : ℝ)^395 := by
    have hnat : (5399954157 : ℕ)^523*4000000000000^395 ≤ 1769012484841^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399954157 10000000000 1769012484841 4000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655336947/5000000000 : ℝ), (-208125447/1000000000 : ℝ), (5399954157/10000000000 : ℝ)] ![(8651953859019/20000000000000 : ℝ), (12514918562901/100000000000000 : ℝ), (1769012484841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655336947/5000000000 : ℝ)|^523 ≤ (8651953859019/20000000000000 : ℝ)^395
        have hw : |(2655336947/5000000000 : ℝ)|=(2655336947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208125447/1000000000 : ℝ)|^523 ≤ (12514918562901/100000000000000 : ℝ)^395
        have hw : |(-208125447/1000000000 : ℝ)|=(208125447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399954157/10000000000 : ℝ)|^523 ≤ (1769012484841/4000000000000 : ℝ)^395
        have hw : |(5399954157/10000000000 : ℝ)|=(5399954157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s4_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5310673927/10000000000 : ℝ)*x 0 + (1079990803/2000000000 : ℝ)*x 1 + (-2081254619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310673927/10000000000 : ℝ)^523 ≤ (5407471206377/12500000000000 : ℝ)^395 := by
    have hnat : (5310673927 : ℕ)^523*12500000000000^395 ≤ 5407471206377^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310673927 10000000000 5407471206377 12500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079990803/2000000000 : ℝ)^523 ≤ (5528163822649/12500000000000 : ℝ)^395 := by
    have hnat : (1079990803 : ℕ)^523*12500000000000^395 ≤ 5528163822649^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079990803 2000000000 5528163822649 12500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081254619/10000000000 : ℝ)^523 ≤ (12514919749199/100000000000000 : ℝ)^395 := by
    have hnat : (2081254619 : ℕ)^523*100000000000000^395 ≤ 12514919749199^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081254619 10000000000 12514919749199 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310673927/10000000000 : ℝ), (1079990803/2000000000 : ℝ), (-2081254619/10000000000 : ℝ)] ![(5407471206377/12500000000000 : ℝ), (5528163822649/12500000000000 : ℝ), (12514919749199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310673927/10000000000 : ℝ)|^523 ≤ (5407471206377/12500000000000 : ℝ)^395
        have hw : |(5310673927/10000000000 : ℝ)|=(5310673927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079990803/2000000000 : ℝ)|^523 ≤ (5528163822649/12500000000000 : ℝ)^395
        have hw : |(1079990803/2000000000 : ℝ)|=(1079990803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081254619/10000000000 : ℝ)|^523 ≤ (12514919749199/100000000000000 : ℝ)^395
        have hw : |(-2081254619/10000000000 : ℝ)|=(2081254619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s4_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (871928973/2000000000 : ℝ)*x 0 + (4502824733/10000000000 : ℝ)*x 1 + (4220989221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871928973/2000000000 : ℝ)^523 ≤ (33313097684233/100000000000000 : ℝ)^395 := by
    have hnat : (871928973 : ℕ)^523*100000000000000^395 ≤ 33313097684233^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871928973 2000000000 33313097684233 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502824733/10000000000 : ℝ)^523 ≤ (34769356401477/100000000000000 : ℝ)^395 := by
    have hnat : (4502824733 : ℕ)^523*100000000000000^395 ≤ 34769356401477^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502824733 10000000000 34769356401477 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4220989221/10000000000 : ℝ)^523 ≤ (7979386473311/25000000000000 : ℝ)^395 := by
    have hnat : (4220989221 : ℕ)^523*25000000000000^395 ≤ 7979386473311^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220989221 10000000000 7979386473311 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871928973/2000000000 : ℝ), (4502824733/10000000000 : ℝ), (4220989221/10000000000 : ℝ)] ![(33313097684233/100000000000000 : ℝ), (34769356401477/100000000000000 : ℝ), (7979386473311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871928973/2000000000 : ℝ)|^523 ≤ (33313097684233/100000000000000 : ℝ)^395
        have hw : |(871928973/2000000000 : ℝ)|=(871928973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502824733/10000000000 : ℝ)|^523 ≤ (34769356401477/100000000000000 : ℝ)^395
        have hw : |(4502824733/10000000000 : ℝ)|=(4502824733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4220989221/10000000000 : ℝ)|^523 ≤ (7979386473311/25000000000000 : ℝ)^395
        have hw : |(4220989221/10000000000 : ℝ)|=(4220989221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10731/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10731/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10731/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10731/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10731/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10731/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10731/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (10957960773305483/100000000000000000000 : ℝ) := by
    have hpowers : (10731/100000 : ℝ)^8367 ≤ (10957960773305483/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10731 : ℕ)^8367*100000000000000000000^2048 ≤ 10957960773305483^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10731 100000 10957960773305483 100000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10731/100000 : ℝ)) (X := (10957960773305483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (8367/2048 : ℝ) ≤ (8078596503232767/20000000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^8367 ≤ (8078596503232767/20000000000000000000 : ℝ)^2048 := by
      have hnat : (923 : ℕ)^8367*20000000000000000000^2048 ≤ 8078596503232767^2048*6250^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 8078596503232767 20000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (8078596503232767/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010957960773305483/50000000000000000000 : ℝ) ≤ (10000536394087771/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50010957960773305483/50000000000000000000 : ℝ)^2048 ≤ (10000536394087771/10000000000000000 : ℝ)^8367 := by
      have hnat : (50010957960773305483 : ℕ)^2048*10000000000000000^8367 ≤ 10000536394087771^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010957960773305483 50000000000000000000 10000536394087771 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000536394087771/10000000000000000 : ℝ)) (X := (50010957960773305483/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025675471644734659/50000000000000000000 : ℝ) ≤ (10001256679159201/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50025675471644734659/50000000000000000000 : ℝ)^2048 ≤ (10001256679159201/10000000000000000 : ℝ)^8367 := by
      have hnat : (50025675471644734659 : ℕ)^2048*10000000000000000^8367 ≤ 10001256679159201^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025675471644734659 50000000000000000000 10001256679159201 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001256679159201/10000000000000000 : ℝ)) (X := (50025675471644734659/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008078596503232767/10000000000000000000 : ℝ) ≤ (10001976964230631/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (10008078596503232767/10000000000000000000 : ℝ)^2048 ≤ (10001976964230631/10000000000000000 : ℝ)^8367 := by
      have hnat : (10008078596503232767 : ℕ)^2048*10000000000000000^8367 ≤ 10001976964230631^8367*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008078596503232767 10000000000000000000 10001976964230631 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001976964230631/10000000000000000 : ℝ)) (X := (10008078596503232767/10000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10957960773305483/100000000000000000000 : ℝ) ≤ ((40356706664729300867/40370000000000000000 : ℝ)+2*(72028507143/40370000000000 : ℝ)*(10731/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (40356706664729300867/40370000000000000000 : ℝ)+2*(72028507143/40370000000000 : ℝ)*(10731/100000 : ℝ)=(10000536394087771/10000000000000000 : ℝ) by norm_num, show 1+2*(10957960773305483/100000000000000000000 : ℝ)=(50010957960773305483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8078596503232767/20000000000000000000 : ℝ)+(10957960773305483/100000000000000000000 : ℝ) ≤ ((40356706664729300867/40370000000000000000 : ℝ)+(72028507143/40370000000000 : ℝ)*((923/6250 : ℝ)+(10731/100000 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (40356706664729300867/40370000000000000000 : ℝ)+(72028507143/40370000000000 : ℝ)*((923/6250 : ℝ)+(10731/100000 : ℝ))=(10001256679159201/10000000000000000 : ℝ) by norm_num, show 1+(8078596503232767/20000000000000000000 : ℝ)+(10957960773305483/100000000000000000000 : ℝ)=(50025675471644734659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8078596503232767/20000000000000000000 : ℝ) ≤ ((40356706664729300867/40370000000000000000 : ℝ)+2*(72028507143/40370000000000 : ℝ)*(923/6250 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (40356706664729300867/40370000000000000000 : ℝ)+2*(72028507143/40370000000000 : ℝ)*(923/6250 : ℝ)=(10001976964230631/10000000000000000 : ℝ) by norm_num, show 1+2*(8078596503232767/20000000000000000000 : ℝ)=(10008078596503232767/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40356706664729300867/40370000000000000000 : ℝ)*(X 1 0+X 2 0)+(72028507143/40370000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (10731/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (40356706664729300867/40370000000000000000 : ℝ)) (alpha := (72028507143/40370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40356706664729300867/40370000000000000000 : ℝ)*(X 0 1+X 2 1)+(72028507143/40370000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (10731/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (40356706664729300867/40370000000000000000 : ℝ)) (alpha := (72028507143/40370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40356706664729300867/40370000000000000000 : ℝ)*(X 0 2+X 1 2)+(72028507143/40370000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (10731/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (40356706664729300867/40370000000000000000 : ℝ)) (alpha := (72028507143/40370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430098903/2000000000 : ℝ)*X 0 0+(5400355077/10000000000 : ℝ)*X 0 1+(5258802729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346621017/10000000000 : ℝ)*X 1 0+(-2222405961/10000000000 : ℝ)*X 1 1+(2629401533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346620911/10000000000 : ℝ)*X 2 0+(164337611/312500000 : ℝ)*X 2 1+(-111120273/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871926401/2000000000 : ℝ)*X 0 0+(2110092939/5000000000 : ℝ)*X 0 1+(562953013/1250000000 : ℝ)*X 0 2+(871926401/2000000000 : ℝ)*X 1 0+(2110092939/5000000000 : ℝ)*X 1 1+(562953013/1250000000 : ℝ)*X 1 2+(871926401/2000000000 : ℝ)*X 2 0+(2110092939/5000000000 : ℝ)*X 2 1+(562953013/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1075250613/5000000000 : ℝ)*X 0 0+(1051840429/2000000000 : ℝ)*X 0 1+(337497131/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655336947/5000000000 : ℝ)*X 1 0+(-208125447/1000000000 : ℝ)*X 1 1+(5399954157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310673927/10000000000 : ℝ)*X 2 0+(1079990803/2000000000 : ℝ)*X 2 1+(-2081254619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871928973/2000000000 : ℝ)*X 0 0+(4502824733/10000000000 : ℝ)*X 0 1+(4220989221/10000000000 : ℝ)*X 0 2+(871928973/2000000000 : ℝ)*X 1 0+(4502824733/10000000000 : ℝ)*X 1 1+(4220989221/10000000000 : ℝ)*X 1 2+(871928973/2000000000 : ℝ)*X 2 0+(4502824733/10000000000 : ℝ)*X 2 1+(4220989221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5607700266713806349481/4037000000000000000000000000 : ℝ) := by norm_num
    linear_combination (781830143/100000000000000 : ℝ)*(base19) + (306075457/50000000000000 : ℝ)*(base23) + (41230937/100000000000000 : ℝ)*(lower2) + (450665957/100000000000000 : ℝ)*(upper5) + (5296371754128281/100000000000000 : ℝ)*(major0) + (5296371754128281/100000000000000 : ℝ)*(major1) + (5296371754128281/100000000000000 : ℝ)*(major2) + (1766138470888603/25000000000000 : ℝ)*(sp0) + (6899019755619/97656250000 : ℝ)*(sp1) + (7064603463887231/100000000000000 : ℝ)*(sp2) + (882031650205799/25000000000000 : ℝ)*(sp3) + (50192483733/100000000000000 : ℝ)*(sp4) + (7064454147/100000000000000 : ℝ)*(sp5) + (3196273169/25000000000000 : ℝ)*(sp7) + (110254355809871/3125000000000 : ℝ)*(f.failure) + (1412920815207629/20000000000000 : ℝ)*(f.sum) + (1991463707817/1009250000000000000000000000 : ℝ)*base66 + (109722553098200219/11000000000000000000000000000000 : ℝ)*base68 + (21564274100799781/11000000000000000000000000000000 : ℝ)*base69 + (37342422033200219/11000000000000000000000000000000 : ℝ)*base72 + (2843441279141/1009250000000000000000000000 : ℝ)*base74 + (308506414651799781/11000000000000000000000000000000 : ℝ)*base75 + (55594845785799781/11000000000000000000000000000000 : ℝ)*base77 + (76602515631200219/11000000000000000000000000000000 : ℝ)*base80 + (2049992918437/2018500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (99013/62500000000000000000 : ℝ)*base90 + (99013/62500000000000000000 : ℝ)*base92 + (99013/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3618759211958612044283286519/2018500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1056335357/100000000000000 : ℝ)*(base19) + (42687673/3125000000000 : ℝ)*(base23) + (80352571/50000000000000 : ℝ)*(upper2) + (30760851/20000000000000 : ℝ)*(upper5) + (5326433385822881/100000000000000 : ℝ)*(major0) + (5326433385822881/100000000000000 : ℝ)*(major1) + (5326433385822881/100000000000000 : ℝ)*(major2) + (280923193/25000000000000 : ℝ)*(sp0) + (1206860283/3125000000000 : ℝ)*(sp1) + (1325631933/4000000000000 : ℝ)*(sp2) + (1776175216435761/25000000000000 : ℝ)*(sp4) + (7104662313571403/100000000000000 : ℝ)*(sp5) + (1420933496526391/20000000000000 : ℝ)*(sp6) + (1774082361225033/50000000000000 : ℝ)*(sp7) + (1774082361225033/50000000000000 : ℝ)*(f.failure) + (888087748679477/12500000000000 : ℝ)*(f.sum) + (669519280997/504625000000000000000000000 : ℝ)*base66 + (28895001158394381/11000000000000000000000000000000 : ℝ)*base67 + (30253430802394381/11000000000000000000000000000000 : ℝ)*base69 + (142770109183605619/11000000000000000000000000000000 : ℝ)*base72 + (1125655759171/2018500000000000000000000000 : ℝ)*base73 + (32095106297394381/11000000000000000000000000000000 : ℝ)*base75 + (45590478569605619/11000000000000000000000000000000 : ℝ)*base78 + (188250165247394381/11000000000000000000000000000000 : ℝ)*base79 + (6306627041851/4037000000000000000000000000 : ℝ)*base82 + (7103701/1000000000000000000000 : ℝ)*base89 + (7103701/1000000000000000000000 : ℝ)*base91 + (7103701/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1175_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1175_s5_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151063419/10000000000 : ℝ)*x 0 + (5394058169/10000000000 : ℝ)*x 1 + (2632362991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151063419/10000000000 : ℝ)^523 ≤ (1307371660243/10000000000000 : ℝ)^395 := by
    have hnat : (2151063419 : ℕ)^523*10000000000000^395 ≤ 1307371660243^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151063419 10000000000 1307371660243 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394058169/10000000000 : ℝ)^523 ≤ (22080693970809/50000000000000 : ℝ)^395 := by
    have hnat : (5394058169 : ℕ)^523*50000000000000^395 ≤ 22080693970809^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394058169 10000000000 22080693970809 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632362991/5000000000 : ℝ)^523 ≤ (21382447721897/50000000000000 : ℝ)^395 := by
    have hnat : (2632362991 : ℕ)^523*50000000000000^395 ≤ 21382447721897^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632362991 5000000000 21382447721897 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151063419/10000000000 : ℝ), (5394058169/10000000000 : ℝ), (2632362991/5000000000 : ℝ)] ![(1307371660243/10000000000000 : ℝ), (22080693970809/50000000000000 : ℝ), (21382447721897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151063419/10000000000 : ℝ)|^523 ≤ (1307371660243/10000000000000 : ℝ)^395
        have hw : |(-2151063419/10000000000 : ℝ)|=(2151063419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394058169/10000000000 : ℝ)|^523 ≤ (22080693970809/50000000000000 : ℝ)^395
        have hw : |(5394058169/10000000000 : ℝ)|=(5394058169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632362991/5000000000 : ℝ)|^523 ≤ (21382447721897/50000000000000 : ℝ)^395
        have hw : |(2632362991/5000000000 : ℝ)|=(2632362991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s5_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345036873/10000000000 : ℝ)*x 0 + (-2216677659/10000000000 : ℝ)*x 1 + (5264725983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345036873/10000000000 : ℝ)^523 ≤ (43630778236471/100000000000000 : ℝ)^395 := by
    have hnat : (5345036873 : ℕ)^523*100000000000000^395 ≤ 43630778236471^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345036873 10000000000 43630778236471 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216677659/10000000000 : ℝ)^523 ≤ (3401081572009/25000000000000 : ℝ)^395 := by
    have hnat : (2216677659 : ℕ)^523*25000000000000^395 ≤ 3401081572009^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216677659 10000000000 3401081572009 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264725983/10000000000 : ℝ)^523 ≤ (42764895454549/100000000000000 : ℝ)^395 := by
    have hnat : (5264725983 : ℕ)^523*100000000000000^395 ≤ 42764895454549^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264725983 10000000000 42764895454549 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345036873/10000000000 : ℝ), (-2216677659/10000000000 : ℝ), (5264725983/10000000000 : ℝ)] ![(43630778236471/100000000000000 : ℝ), (3401081572009/25000000000000 : ℝ), (42764895454549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345036873/10000000000 : ℝ)|^523 ≤ (43630778236471/100000000000000 : ℝ)^395
        have hw : |(5345036873/10000000000 : ℝ)|=(5345036873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216677659/10000000000 : ℝ)|^523 ≤ (3401081572009/25000000000000 : ℝ)^395
        have hw : |(-2216677659/10000000000 : ℝ)|=(2216677659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264725983/10000000000 : ℝ)|^523 ≤ (42764895454549/100000000000000 : ℝ)^395
        have hw : |(5264725983/10000000000 : ℝ)|=(5264725983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s5_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345036871/10000000000 : ℝ)*x 0 + (2632362991/5000000000 : ℝ)*x 1 + (-2216677663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345036871/10000000000 : ℝ)^523 ≤ (8726155642971/20000000000000 : ℝ)^395 := by
    have hnat : (5345036871 : ℕ)^523*20000000000000^395 ≤ 8726155642971^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345036871 10000000000 8726155642971 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632362991/5000000000 : ℝ)^523 ≤ (21382447721897/50000000000000 : ℝ)^395 := by
    have hnat : (2632362991 : ℕ)^523*50000000000000^395 ≤ 21382447721897^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632362991 5000000000 21382447721897 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216677663/10000000000 : ℝ)^523 ≤ (680216316027/5000000000000 : ℝ)^395 := by
    have hnat : (2216677663 : ℕ)^523*5000000000000^395 ≤ 680216316027^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216677663 10000000000 680216316027 5000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345036871/10000000000 : ℝ), (2632362991/5000000000 : ℝ), (-2216677663/10000000000 : ℝ)] ![(8726155642971/20000000000000 : ℝ), (21382447721897/50000000000000 : ℝ), (680216316027/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345036871/10000000000 : ℝ)|^523 ≤ (8726155642971/20000000000000 : ℝ)^395
        have hw : |(5345036871/10000000000 : ℝ)|=(5345036871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632362991/5000000000 : ℝ)|^523 ≤ (21382447721897/50000000000000 : ℝ)^395
        have hw : |(2632362991/5000000000 : ℝ)|=(2632362991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2216677663/10000000000 : ℝ)|^523 ≤ (680216316027/5000000000000 : ℝ)^395
        have hw : |(-2216677663/10000000000 : ℝ)|=(2216677663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s5_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1089990961/2500000000 : ℝ)*x 0 + (4232377581/10000000000 : ℝ)*x 1 + (1122836787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089990961/2500000000 : ℝ)^523 ≤ (33316324957487/100000000000000 : ℝ)^395 := by
    have hnat : (1089990961 : ℕ)^523*100000000000000^395 ≤ 33316324957487^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089990961 2500000000 33316324957487 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232377581/10000000000 : ℝ)^523 ≤ (8007903926177/25000000000000 : ℝ)^395 := by
    have hnat : (4232377581 : ℕ)^523*25000000000000^395 ≤ 8007903926177^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232377581 10000000000 8007903926177 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122836787/2500000000 : ℝ)^523 ≤ (17326029658609/50000000000000 : ℝ)^395 := by
    have hnat : (1122836787 : ℕ)^523*50000000000000^395 ≤ 17326029658609^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122836787 2500000000 17326029658609 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089990961/2500000000 : ℝ), (4232377581/10000000000 : ℝ), (1122836787/2500000000 : ℝ)] ![(33316324957487/100000000000000 : ℝ), (8007903926177/25000000000000 : ℝ), (17326029658609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089990961/2500000000 : ℝ)|^523 ≤ (33316324957487/100000000000000 : ℝ)^395
        have hw : |(1089990961/2500000000 : ℝ)|=(1089990961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232377581/10000000000 : ℝ)|^523 ≤ (8007903926177/25000000000000 : ℝ)^395
        have hw : |(4232377581/10000000000 : ℝ)|=(4232377581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122836787/2500000000 : ℝ)|^523 ≤ (17326029658609/50000000000000 : ℝ)^395
        have hw : |(1122836787/2500000000 : ℝ)|=(1122836787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s5_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151068681/10000000000 : ℝ)*x 0 + (5265059529/10000000000 : ℝ)*x 1 + (5393723321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151068681/10000000000 : ℝ)^523 ≤ (3268439736841/25000000000000 : ℝ)^395 := by
    have hnat : (2151068681 : ℕ)^523*25000000000000^395 ≤ 3268439736841^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151068681 10000000000 3268439736841 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265059529/10000000000 : ℝ)^523 ≤ (21384241413343/50000000000000 : ℝ)^395 := by
    have hnat : (5265059529 : ℕ)^523*50000000000000^395 ≤ 21384241413343^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265059529 10000000000 21384241413343 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393723321/10000000000 : ℝ)^523 ≤ (176631032823/400000000000 : ℝ)^395 := by
    have hnat : (5393723321 : ℕ)^523*400000000000^395 ≤ 176631032823^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393723321 10000000000 176631032823 400000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151068681/10000000000 : ℝ), (5265059529/10000000000 : ℝ), (5393723321/10000000000 : ℝ)] ![(3268439736841/25000000000000 : ℝ), (21384241413343/50000000000000 : ℝ), (176631032823/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151068681/10000000000 : ℝ)|^523 ≤ (3268439736841/25000000000000 : ℝ)^395
        have hw : |(-2151068681/10000000000 : ℝ)|=(2151068681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265059529/10000000000 : ℝ)|^523 ≤ (21384241413343/50000000000000 : ℝ)^395
        have hw : |(5265059529/10000000000 : ℝ)|=(5265059529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393723321/10000000000 : ℝ)|^523 ≤ (176631032823/400000000000 : ℝ)^395
        have hw : |(5393723321/10000000000 : ℝ)|=(5393723321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s5_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656095923/5000000000 : ℝ)*x 0 + (-260959967/1250000000 : ℝ)*x 1 + (2696861639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656095923/5000000000 : ℝ)^523 ≤ (21638070941071/50000000000000 : ℝ)^395 := by
    have hnat : (2656095923 : ℕ)^523*50000000000000^395 ≤ 21638070941071^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656095923 5000000000 21638070941071 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260959967/1250000000 : ℝ)^523 ≤ (6283050182947/50000000000000 : ℝ)^395 := by
    have hnat : (260959967 : ℕ)^523*50000000000000^395 ≤ 6283050182947^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260959967 1250000000 6283050182947 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696861639/5000000000 : ℝ)^523 ≤ (44157757739637/100000000000000 : ℝ)^395 := by
    have hnat : (2696861639 : ℕ)^523*100000000000000^395 ≤ 44157757739637^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696861639 5000000000 44157757739637 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656095923/5000000000 : ℝ), (-260959967/1250000000 : ℝ), (2696861639/5000000000 : ℝ)] ![(21638070941071/50000000000000 : ℝ), (6283050182947/50000000000000 : ℝ), (44157757739637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656095923/5000000000 : ℝ)|^523 ≤ (21638070941071/50000000000000 : ℝ)^395
        have hw : |(2656095923/5000000000 : ℝ)|=(2656095923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260959967/1250000000 : ℝ)|^523 ≤ (6283050182947/50000000000000 : ℝ)^395
        have hw : |(-260959967/1250000000 : ℝ)|=(260959967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696861639/5000000000 : ℝ)|^523 ≤ (44157757739637/100000000000000 : ℝ)^395
        have hw : |(2696861639/5000000000 : ℝ)|=(2696861639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s5_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312191263/10000000000 : ℝ)*x 0 + (1348430923/2500000000 : ℝ)*x 1 + (-2087679961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312191263/10000000000 : ℝ)^523 ≤ (4327613559363/10000000000000 : ℝ)^395 := by
    have hnat : (5312191263 : ℕ)^523*10000000000000^395 ≤ 4327613559363^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312191263 10000000000 4327613559363 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348430923/2500000000 : ℝ)^523 ≤ (44157762227331/100000000000000 : ℝ)^395 := by
    have hnat : (1348430923 : ℕ)^523*100000000000000^395 ≤ 44157762227331^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348430923 2500000000 44157762227331 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087679961/10000000000 : ℝ)^523 ≤ (6283051079537/50000000000000 : ℝ)^395 := by
    have hnat : (2087679961 : ℕ)^523*50000000000000^395 ≤ 6283051079537^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087679961 10000000000 6283051079537 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312191263/10000000000 : ℝ), (1348430923/2500000000 : ℝ), (-2087679961/10000000000 : ℝ)] ![(4327613559363/10000000000000 : ℝ), (44157762227331/100000000000000 : ℝ), (6283051079537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312191263/10000000000 : ℝ)|^523 ≤ (4327613559363/10000000000000 : ℝ)^395
        have hw : |(5312191263/10000000000 : ℝ)|=(5312191263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348430923/2500000000 : ℝ)|^523 ≤ (44157762227331/100000000000000 : ℝ)^395
        have hw : |(1348430923/2500000000 : ℝ)|=(1348430923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087679961/10000000000 : ℝ)|^523 ≤ (6283051079537/50000000000000 : ℝ)^395
        have hw : |(-2087679961/10000000000 : ℝ)|=(2087679961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s5_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4359974381/10000000000 : ℝ)*x 0 + (224533963/500000000 : ℝ)*x 1 + (169321911/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359974381/10000000000 : ℝ)^523 ≤ (33316431566997/100000000000000 : ℝ)^395 := by
    have hnat : (4359974381 : ℕ)^523*100000000000000^395 ≤ 33316431566997^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359974381 10000000000 33316431566997 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224533963/500000000 : ℝ)^523 ≤ (34645236712749/100000000000000 : ℝ)^395 := by
    have hnat : (224533963 : ℕ)^523*100000000000000^395 ≤ 34645236712749^395*500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224533963 500000000 34645236712749 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169321911/400000000 : ℝ)^523 ≤ (3203833170507/10000000000000 : ℝ)^395 := by
    have hnat : (169321911 : ℕ)^523*10000000000000^395 ≤ 3203833170507^395*400000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169321911 400000000 3203833170507 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359974381/10000000000 : ℝ), (224533963/500000000 : ℝ), (169321911/400000000 : ℝ)] ![(33316431566997/100000000000000 : ℝ), (34645236712749/100000000000000 : ℝ), (3203833170507/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359974381/10000000000 : ℝ)|^523 ≤ (33316431566997/100000000000000 : ℝ)^395
        have hw : |(4359974381/10000000000 : ℝ)|=(4359974381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224533963/500000000 : ℝ)|^523 ≤ (34645236712749/100000000000000 : ℝ)^395
        have hw : |(224533963/500000000 : ℝ)|=(224533963/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169321911/400000000 : ℝ)|^523 ≤ (3203833170507/10000000000000 : ℝ)^395
        have hw : |(169321911/400000000 : ℝ)|=(169321911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11237/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (1653447284390703/12500000000000000000 : ℝ) := by
    have hpowers : (11237/100000 : ℝ)^8367 ≤ (1653447284390703/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11237 : ℕ)^8367*12500000000000000000^2048 ≤ 1653447284390703^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11237 100000 1653447284390703 12500000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11237/100000 : ℝ)) (X := (1653447284390703/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8367/2048 : ℝ) ≤ (4343804884122317/12500000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8367 ≤ (4343804884122317/12500000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8367*12500000000000000000^2048 ≤ 4343804884122317^2048*50000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 4343804884122317 12500000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (4343804884122317/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251653447284390703/6250000000000000000 : ℝ) ≤ (1250080935145417/1250000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (6251653447284390703/6250000000000000000 : ℝ)^2048 ≤ (1250080935145417/1250000000000000 : ℝ)^8367 := by
      have hnat : (6251653447284390703 : ℕ)^2048*1250000000000000^8367 ≤ 1250080935145417^8367*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251653447284390703 6250000000000000000 1250080935145417 1250000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250080935145417/1250000000000000 : ℝ)) (X := (6251653447284390703/6250000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (625299862608425651/625000000000000000 : ℝ) ≤ (10001174150624553/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (625299862608425651/625000000000000000 : ℝ)^2048 ≤ (10001174150624553/10000000000000000 : ℝ)^8367 := by
      have hnat : (625299862608425651 : ℕ)^2048*10000000000000000^8367 ≤ 10001174150624553^8367*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625299862608425651 625000000000000000 10001174150624553 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001174150624553/10000000000000000 : ℝ)) (X := (625299862608425651/625000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254343804884122317/6250000000000000000 : ℝ) ≤ (1000170082008577/1000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (6254343804884122317/6250000000000000000 : ℝ)^2048 ≤ (1000170082008577/1000000000000000 : ℝ)^8367 := by
      have hnat : (6254343804884122317 : ℕ)^2048*1000000000000000^8367 ≤ 1000170082008577^8367*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254343804884122317 6250000000000000000 1000170082008577 1000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000170082008577/1000000000000000 : ℝ)) (X := (6254343804884122317/6250000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1653447284390703/12500000000000000000 : ℝ) ≤ ((14980052065787563567/14985000000000000000 : ℝ)+2*(526669461217/299700000000000 : ℝ)*(11237/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (14980052065787563567/14985000000000000000 : ℝ)+2*(526669461217/299700000000000 : ℝ)*(11237/100000 : ℝ)=(1250080935145417/1250000000000000 : ℝ) by norm_num, show 1+2*(1653447284390703/12500000000000000000 : ℝ)=(6251653447284390703/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4343804884122317/12500000000000000000 : ℝ)+(1653447284390703/12500000000000000000 : ℝ) ≤ ((14980052065787563567/14985000000000000000 : ℝ)+(526669461217/299700000000000 : ℝ)*((7117/50000 : ℝ)+(11237/100000 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (14980052065787563567/14985000000000000000 : ℝ)+(526669461217/299700000000000 : ℝ)*((7117/50000 : ℝ)+(11237/100000 : ℝ))=(10001174150624553/10000000000000000 : ℝ) by norm_num, show 1+(4343804884122317/12500000000000000000 : ℝ)+(1653447284390703/12500000000000000000 : ℝ)=(625299862608425651/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4343804884122317/12500000000000000000 : ℝ) ≤ ((14980052065787563567/14985000000000000000 : ℝ)+2*(526669461217/299700000000000 : ℝ)*(7117/50000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (14980052065787563567/14985000000000000000 : ℝ)+2*(526669461217/299700000000000 : ℝ)*(7117/50000 : ℝ)=(1000170082008577/1000000000000000 : ℝ) by norm_num, show 1+2*(4343804884122317/12500000000000000000 : ℝ)=(6254343804884122317/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14980052065787563567/14985000000000000000 : ℝ)*(X 1 0+X 2 0)+(526669461217/299700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14980052065787563567/14985000000000000000 : ℝ)) (alpha := (526669461217/299700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14980052065787563567/14985000000000000000 : ℝ)*(X 0 1+X 2 1)+(526669461217/299700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14980052065787563567/14985000000000000000 : ℝ)) (alpha := (526669461217/299700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14980052065787563567/14985000000000000000 : ℝ)*(X 0 2+X 1 2)+(526669461217/299700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14980052065787563567/14985000000000000000 : ℝ)) (alpha := (526669461217/299700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2151063419/10000000000 : ℝ)*X 0 0+(5394058169/10000000000 : ℝ)*X 0 1+(2632362991/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345036873/10000000000 : ℝ)*X 1 0+(-2216677659/10000000000 : ℝ)*X 1 1+(5264725983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345036871/10000000000 : ℝ)*X 2 0+(2632362991/5000000000 : ℝ)*X 2 1+(-2216677663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089990961/2500000000 : ℝ)*X 0 0+(4232377581/10000000000 : ℝ)*X 0 1+(1122836787/2500000000 : ℝ)*X 0 2+(1089990961/2500000000 : ℝ)*X 1 0+(4232377581/10000000000 : ℝ)*X 1 1+(1122836787/2500000000 : ℝ)*X 1 2+(1089990961/2500000000 : ℝ)*X 2 0+(4232377581/10000000000 : ℝ)*X 2 1+(1122836787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151068681/10000000000 : ℝ)*X 0 0+(5265059529/10000000000 : ℝ)*X 0 1+(5393723321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656095923/5000000000 : ℝ)*X 1 0+(-260959967/1250000000 : ℝ)*X 1 1+(2696861639/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312191263/10000000000 : ℝ)*X 2 0+(1348430923/2500000000 : ℝ)*X 2 1+(-2087679961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359974381/10000000000 : ℝ)*X 0 0+(224533963/500000000 : ℝ)*X 0 1+(169321911/400000000 : ℝ)*X 0 2+(4359974381/10000000000 : ℝ)*X 1 0+(224533963/500000000 : ℝ)*X 1 1+(169321911/400000000 : ℝ)*X 1 2+(4359974381/10000000000 : ℝ)*X 2 0+(224533963/500000000 : ℝ)*X 2 1+(169321911/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57747406060134311113054519/12487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113167987/12500000000000 : ℝ)*(base19) + (417197183/50000000000000 : ℝ)*(base23) + (36376371/100000000000000 : ℝ)*(lower2) + (30709987/25000000000000 : ℝ)*(upper3) + (65588591/100000000000000 : ℝ)*(upper5) + (579677949298657/10000000000000 : ℝ)*(major0) + (579677949298657/10000000000000 : ℝ)*(major1) + (579677949298657/10000000000000 : ℝ)*(major2) + (7732052712224957/100000000000000 : ℝ)*(sp0) + (1933018894447589/25000000000000 : ℝ)*(sp1) + (1546415129747977/20000000000000 : ℝ)*(sp2) + (386146919321737/10000000000000 : ℝ)*(sp3) + (11885454647/50000000000000 : ℝ)*(sp4) + (6577737137/50000000000000 : ℝ)*(sp7) + (965370587172911/25000000000000 : ℝ)*(f.failure) + (1933019120783563/25000000000000 : ℝ)*(f.sum) + (13881078666569/2997000000000000000000000000 : ℝ)*base65 + (370058178532885609/16650000000000000000000000000000 : ℝ)*base68 + (132733304119735609/16650000000000000000000000000000 : ℝ)*base70 + (465755984816335609/16650000000000000000000000000000 : ℝ)*base72 + (704331899761/749250000000000000000000000 : ℝ)*base74 + (127175829910264391/16650000000000000000000000000000 : ℝ)*base75 + (254792210548885609/16650000000000000000000000000000 : ℝ)*base78 + (391341970286035609/16650000000000000000000000000000 : ℝ)*base80 + (3147086756797/2997000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (819133/500000000000000000000 : ℝ)*base90 + (819133/500000000000000000000 : ℝ)*base92 + (819133/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162830091644380695115787/187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1886745707/100000000000000 : ℝ)*(base19) + (958352307/100000000000000 : ℝ)*(base23) + (13531809/10000000000000 : ℝ)*(upper3) + (9686869/100000000000000 : ℝ)*(lower4) + (7274133/20000000000000 : ℝ)*(upper5) + (1456711253594871/25000000000000 : ℝ)*(major0) + (1456711253594871/25000000000000 : ℝ)*(major1) + (1456711253594871/25000000000000 : ℝ)*(major2) + (54291744609/100000000000000 : ℝ)*(sp1) + (7828879231/20000000000000 : ℝ)*(sp2) + (485761232718213/6250000000000 : ℝ)*(sp4) + (1943030886250273/25000000000000 : ℝ)*(sp5) + (3886069810371473/50000000000000 : ℝ)*(sp6) + (3881510276319979/100000000000000 : ℝ)*(sp7) + (3881510276319979/100000000000000 : ℝ)*(f.failure) + (485761232718213/6250000000000 : ℝ)*(f.sum) + (1044369704363/135000000000000000000000000 : ℝ)*base65 + (5523374839371857/375000000000000000000000000000 : ℝ)*base68 + (1378897459746857/375000000000000000000000000000 : ℝ)*base70 + (4260734507871857/375000000000000000000000000000 : ℝ)*base72 + (994202577653/135000000000000000000000000 : ℝ)*base73 + (3998485930371857/375000000000000000000000000000 : ℝ)*base76 + (1721327625621857/375000000000000000000000000000 : ℝ)*base78 + (7987668218121857/375000000000000000000000000000 : ℝ)*base80 + (258324604729/67500000000000000000000000 : ℝ)*base81 + (12544463/2000000000000000000000 : ℝ)*base89 + (12544463/2000000000000000000000 : ℝ)*base91 + (12544463/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1175_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1175_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8203/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1175_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1175_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1175_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8203/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1175_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
