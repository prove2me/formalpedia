-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1646_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:58.466222+00:00
-- url     : https://prove2.me/submissions/33bc1588-d956-4145-89b6-64326a2aadce

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
theorem support_rectangle_w1646_s3_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-808828353/5000000000 : ℝ)*x 0 + (5448803937/10000000000 : ℝ)*x 1 + (647945971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808828353/5000000000 : ℝ)^4903 ≤ (1250126024577/12500000000000 : ℝ)^3879 := by
    have hnat : (808828353 : ℕ)^4903*12500000000000^3879 ≤ 1250126024577^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808828353 5000000000 1250126024577 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448803937/10000000000 : ℝ)^4903 ≤ (46418221846279/100000000000000 : ℝ)^3879 := by
    have hnat : (5448803937 : ℕ)^4903*100000000000000^3879 ≤ 46418221846279^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448803937 10000000000 46418221846279 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647945971/1250000000 : ℝ)^4903 ≤ (10895192484877/25000000000000 : ℝ)^3879 := by
    have hnat : (647945971 : ℕ)^4903*25000000000000^3879 ≤ 10895192484877^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647945971 1250000000 10895192484877 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-808828353/5000000000 : ℝ), (5448803937/10000000000 : ℝ), (647945971/1250000000 : ℝ)] ![(1250126024577/12500000000000 : ℝ), (46418221846279/100000000000000 : ℝ), (10895192484877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-808828353/5000000000 : ℝ)|^4903 ≤ (1250126024577/12500000000000 : ℝ)^3879
        have hw : |(-808828353/5000000000 : ℝ)|=(808828353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448803937/10000000000 : ℝ)|^4903 ≤ (46418221846279/100000000000000 : ℝ)^3879
        have hw : |(5448803937/10000000000 : ℝ)|=(5448803937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647945971/1250000000 : ℝ)|^4903 ≤ (10895192484877/25000000000000 : ℝ)^3879
        have hw : |(647945971/1250000000 : ℝ)|=(647945971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s3_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668545981/1250000000 : ℝ)*x 0 + (-109638871/625000000 : ℝ)*x 1 + (2591783869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668545981/1250000000 : ℝ)^4903 ≤ (45339383241623/100000000000000 : ℝ)^3879 := by
    have hnat : (668545981 : ℕ)^4903*100000000000000^3879 ≤ 45339383241623^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668545981 1250000000 45339383241623 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109638871/625000000 : ℝ)^4903 ≤ (276996178133/2500000000000 : ℝ)^3879 := by
    have hnat : (109638871 : ℕ)^4903*2500000000000^3879 ≤ 276996178133^3879*625000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109638871 625000000 276996178133 2500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591783869/5000000000 : ℝ)^4903 ≤ (435807696207/1000000000000 : ℝ)^3879 := by
    have hnat : (2591783869 : ℕ)^4903*1000000000000^3879 ≤ 435807696207^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591783869 5000000000 435807696207 1000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668545981/1250000000 : ℝ), (-109638871/625000000 : ℝ), (2591783869/5000000000 : ℝ)] ![(45339383241623/100000000000000 : ℝ), (276996178133/2500000000000 : ℝ), (435807696207/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668545981/1250000000 : ℝ)|^4903 ≤ (45339383241623/100000000000000 : ℝ)^3879
        have hw : |(668545981/1250000000 : ℝ)|=(668545981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109638871/625000000 : ℝ)|^4903 ≤ (276996178133/2500000000000 : ℝ)^3879
        have hw : |(-109638871/625000000 : ℝ)|=(109638871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591783869/5000000000 : ℝ)|^4903 ≤ (435807696207/1000000000000 : ℝ)^3879
        have hw : |(2591783869/5000000000 : ℝ)|=(2591783869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s3_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534836783/1000000000 : ℝ)*x 0 + (5183567713/10000000000 : ℝ)*x 1 + (-1754221993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534836783/1000000000 : ℝ)^4903 ≤ (45339383048751/100000000000000 : ℝ)^3879 := by
    have hnat : (534836783 : ℕ)^4903*100000000000000^3879 ≤ 45339383048751^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534836783 1000000000 45339383048751 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183567713/10000000000 : ℝ)^4903 ≤ (21790384677513/50000000000000 : ℝ)^3879 := by
    have hnat : (5183567713 : ℕ)^4903*50000000000000^3879 ≤ 21790384677513^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183567713 10000000000 21790384677513 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1754221993/10000000000 : ℝ)^4903 ≤ (11079847580377/100000000000000 : ℝ)^3879 := by
    have hnat : (1754221993 : ℕ)^4903*100000000000000^3879 ≤ 11079847580377^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754221993 10000000000 11079847580377 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534836783/1000000000 : ℝ), (5183567713/10000000000 : ℝ), (-1754221993/10000000000 : ℝ)] ![(45339383048751/100000000000000 : ℝ), (21790384677513/50000000000000 : ℝ), (11079847580377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534836783/1000000000 : ℝ)|^4903 ≤ (45339383048751/100000000000000 : ℝ)^3879
        have hw : |(534836783/1000000000 : ℝ)|=(534836783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183567713/10000000000 : ℝ)|^4903 ≤ (21790384677513/50000000000000 : ℝ)^3879
        have hw : |(5183567713/10000000000 : ℝ)|=(5183567713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1754221993/10000000000 : ℝ)|^4903 ≤ (11079847580377/100000000000000 : ℝ)^3879
        have hw : |(-1754221993/10000000000 : ℝ)|=(1754221993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s3_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130743511/312500000 : ℝ)*x 0 + (481570643/1250000000 : ℝ)*x 1 + (4535341097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130743511/312500000 : ℝ)^4903 ≤ (33240695124307/100000000000000 : ℝ)^3879 := by
    have hnat : (130743511 : ℕ)^4903*100000000000000^3879 ≤ 33240695124307^3879*312500000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130743511 312500000 33240695124307 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481570643/1250000000 : ℝ)^4903 ≤ (14974901465667/50000000000000 : ℝ)^3879 := by
    have hnat : (481570643 : ℕ)^4903*50000000000000^3879 ≤ 14974901465667^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481570643 1250000000 14974901465667 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535341097/10000000000 : ℝ)^4903 ≤ (18404750961987/50000000000000 : ℝ)^3879 := by
    have hnat : (4535341097 : ℕ)^4903*50000000000000^3879 ≤ 18404750961987^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535341097 10000000000 18404750961987 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130743511/312500000 : ℝ), (481570643/1250000000 : ℝ), (4535341097/10000000000 : ℝ)] ![(33240695124307/100000000000000 : ℝ), (14974901465667/50000000000000 : ℝ), (18404750961987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130743511/312500000 : ℝ)|^4903 ≤ (33240695124307/100000000000000 : ℝ)^3879
        have hw : |(130743511/312500000 : ℝ)|=(130743511/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481570643/1250000000 : ℝ)|^4903 ≤ (14974901465667/50000000000000 : ℝ)^3879
        have hw : |(481570643/1250000000 : ℝ)|=(481570643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535341097/10000000000 : ℝ)|^4903 ≤ (18404750961987/50000000000000 : ℝ)^3879
        have hw : |(4535341097/10000000000 : ℝ)|=(4535341097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s3_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-808860879/5000000000 : ℝ)*x 0 + (518557253/1000000000 : ℝ)*x 1 + (2723389001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808860879/5000000000 : ℝ)^4903 ≤ (625094784139/6250000000000 : ℝ)^3879 := by
    have hnat : (808860879 : ℕ)^4903*6250000000000^3879 ≤ 625094784139^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808860879 5000000000 625094784139 6250000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518557253/1000000000 : ℝ)^4903 ≤ (43602075512607/100000000000000 : ℝ)^3879 := by
    have hnat : (518557253 : ℕ)^4903*100000000000000^3879 ≤ 43602075512607^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518557253 1000000000 43602075512607 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723389001/5000000000 : ℝ)^4903 ≤ (1855856317237/4000000000000 : ℝ)^3879 := by
    have hnat : (2723389001 : ℕ)^4903*4000000000000^3879 ≤ 1855856317237^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723389001 5000000000 1855856317237 4000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-808860879/5000000000 : ℝ), (518557253/1000000000 : ℝ), (2723389001/5000000000 : ℝ)] ![(625094784139/6250000000000 : ℝ), (43602075512607/100000000000000 : ℝ), (1855856317237/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-808860879/5000000000 : ℝ)|^4903 ≤ (625094784139/6250000000000 : ℝ)^3879
        have hw : |(-808860879/5000000000 : ℝ)|=(808860879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518557253/1000000000 : ℝ)|^4903 ≤ (43602075512607/100000000000000 : ℝ)^3879
        have hw : |(518557253/1000000000 : ℝ)|=(518557253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723389001/5000000000 : ℝ)|^4903 ≤ (1855856317237/4000000000000 : ℝ)^3879
        have hw : |(2723389001/5000000000 : ℝ)|=(2723389001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s3_5 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277543103/10000000000 : ℝ)*x 0 + (-1491011831/10000000000 : ℝ)*x 1 + (5446777709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277543103/10000000000 : ℝ)^4903 ≤ (44581819423551/100000000000000 : ℝ)^3879 := by
    have hnat : (5277543103 : ℕ)^4903*100000000000000^3879 ≤ 44581819423551^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277543103 10000000000 44581819423551 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1491011831/10000000000 : ℝ)^4903 ≤ (9021775782209/100000000000000 : ℝ)^3879 := by
    have hnat : (1491011831 : ℕ)^4903*100000000000000^3879 ≤ 9021775782209^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491011831 10000000000 9021775782209 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446777709/10000000000 : ℝ)^4903 ≤ (46396404776251/100000000000000 : ℝ)^3879 := by
    have hnat : (5446777709 : ℕ)^4903*100000000000000^3879 ≤ 46396404776251^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446777709 10000000000 46396404776251 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277543103/10000000000 : ℝ), (-1491011831/10000000000 : ℝ), (5446777709/10000000000 : ℝ)] ![(44581819423551/100000000000000 : ℝ), (9021775782209/100000000000000 : ℝ), (46396404776251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277543103/10000000000 : ℝ)|^4903 ≤ (44581819423551/100000000000000 : ℝ)^3879
        have hw : |(5277543103/10000000000 : ℝ)|=(5277543103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1491011831/10000000000 : ℝ)|^4903 ≤ (9021775782209/100000000000000 : ℝ)^3879
        have hw : |(-1491011831/10000000000 : ℝ)|=(1491011831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446777709/10000000000 : ℝ)|^4903 ≤ (46396404776251/100000000000000 : ℝ)^3879
        have hw : |(5446777709/10000000000 : ℝ)|=(5446777709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s3_6 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277543213/10000000000 : ℝ)*x 0 + (1089355533/2000000000 : ℝ)*x 1 + (-74550587/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277543213/10000000000 : ℝ)^4903 ≤ (5572727574759/12500000000000 : ℝ)^3879 := by
    have hnat : (5277543213 : ℕ)^4903*12500000000000^3879 ≤ 5572727574759^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277543213 10000000000 5572727574759 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089355533/2000000000 : ℝ)^4903 ≤ (2899775268907/6250000000000 : ℝ)^3879 := by
    have hnat : (1089355533 : ℕ)^4903*6250000000000^3879 ≤ 2899775268907^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089355533 2000000000 2899775268907 6250000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74550587/500000000 : ℝ)^4903 ≤ (9021775086233/100000000000000 : ℝ)^3879 := by
    have hnat : (74550587 : ℕ)^4903*100000000000000^3879 ≤ 9021775086233^3879*500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74550587 500000000 9021775086233 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277543213/10000000000 : ℝ), (1089355533/2000000000 : ℝ), (-74550587/500000000 : ℝ)] ![(5572727574759/12500000000000 : ℝ), (2899775268907/6250000000000 : ℝ), (9021775086233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277543213/10000000000 : ℝ)|^4903 ≤ (5572727574759/12500000000000 : ℝ)^3879
        have hw : |(5277543213/10000000000 : ℝ)|=(5277543213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089355533/2000000000 : ℝ)|^4903 ≤ (2899775268907/6250000000000 : ℝ)^3879
        have hw : |(1089355533/2000000000 : ℝ)|=(1089355533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74550587/500000000 : ℝ)|^4903 ≤ (9021775086233/100000000000000 : ℝ)^3879
        have hw : |(-74550587/500000000 : ℝ)|=(74550587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s3_7 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418396051/1000000000 : ℝ)*x 0 + (4530178783/10000000000 : ℝ)*x 1 + (3857781067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418396051/1000000000 : ℝ)^4903 ≤ (8310595965237/25000000000000 : ℝ)^3879 := by
    have hnat : (418396051 : ℕ)^4903*25000000000000^3879 ≤ 8310595965237^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418396051 1000000000 8310595965237 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530178783/10000000000 : ℝ)^4903 ≤ (36756551280149/100000000000000 : ℝ)^3879 := by
    have hnat : (4530178783 : ℕ)^4903*100000000000000^3879 ≤ 36756551280149^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530178783 10000000000 36756551280149 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3857781067/10000000000 : ℝ)^4903 ≤ (1875066552999/6250000000000 : ℝ)^3879 := by
    have hnat : (3857781067 : ℕ)^4903*6250000000000^3879 ≤ 1875066552999^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3857781067 10000000000 1875066552999 6250000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418396051/1000000000 : ℝ), (4530178783/10000000000 : ℝ), (3857781067/10000000000 : ℝ)] ![(8310595965237/25000000000000 : ℝ), (36756551280149/100000000000000 : ℝ), (1875066552999/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418396051/1000000000 : ℝ)|^4903 ≤ (8310595965237/25000000000000 : ℝ)^3879
        have hw : |(418396051/1000000000 : ℝ)|=(418396051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530178783/10000000000 : ℝ)|^4903 ≤ (36756551280149/100000000000000 : ℝ)^3879
        have hw : |(4530178783/10000000000 : ℝ)|=(4530178783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3857781067/10000000000 : ℝ)|^4903 ≤ (1875066552999/6250000000000 : ℝ)^3879
        have hw : |(3857781067/10000000000 : ℝ)|=(3857781067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2661/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16281/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (423/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (423/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (423/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (423/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (423/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (423/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (423/4000 : ℝ) ^ (4899/1024 : ℝ) ≤ (2147741428104611/100000000000000000000 : ℝ) := by
    have hpowers : (423/4000 : ℝ)^4899 ≤ (2147741428104611/100000000000000000000 : ℝ)^1024 := by
      have hnat : (423 : ℕ)^4899*100000000000000000000^1024 ≤ 2147741428104611^1024*4000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        423 4000 2147741428104611 100000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (423/4000 : ℝ)) (X := (2147741428104611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16359/100000 : ℝ) ^ (4899/1024 : ℝ) ≤ (4329233736285139/25000000000000000000 : ℝ) := by
    have hpowers : (16359/100000 : ℝ)^4899 ≤ (4329233736285139/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16359 : ℕ)^4899*25000000000000000000^1024 ≤ 4329233736285139^1024*100000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16359 100000 4329233736285139 25000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16359/100000 : ℝ)) (X := (4329233736285139/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002147741428104611/50000000000000000000 : ℝ) ≤ (5000044891811829/5000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (50002147741428104611/50000000000000000000 : ℝ)^1024 ≤ (5000044891811829/5000000000000000 : ℝ)^4899 := by
      have hnat : (50002147741428104611 : ℕ)^1024*5000000000000000^4899 ≤ 5000044891811829^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002147741428104611 50000000000000000000 5000044891811829 5000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000044891811829/5000000000000000 : ℝ)) (X := (50002147741428104611/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019464676373245167/100000000000000000000 : ℝ) ≤ (2000081364745539/2000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (100019464676373245167/100000000000000000000 : ℝ)^1024 ≤ (2000081364745539/2000000000000000 : ℝ)^4899 := by
      have hnat : (100019464676373245167 : ℕ)^1024*2000000000000000^4899 ≤ 2000081364745539^4899*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019464676373245167 100000000000000000000 2000081364745539 2000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000081364745539/2000000000000000 : ℝ)) (X := (100019464676373245167/100000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504329233736285139/12500000000000000000 : ℝ) ≤ (2500180965957933/2500000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (12504329233736285139/12500000000000000000 : ℝ)^1024 ≤ (2500180965957933/2500000000000000 : ℝ)^4899 := by
      have hnat : (12504329233736285139 : ℕ)^1024*2500000000000000^4899 ≤ 2500180965957933^4899*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504329233736285139 12500000000000000000 2500180965957933 2500000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500180965957933/2500000000000000 : ℝ)) (X := (12504329233736285139/12500000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2147741428104611/100000000000000000000 : ℝ) ≤ ((9638968985046475887/9640000000000000000 : ℝ)+2*(105680034679/192800000000000 : ℝ)*(423/4000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (9638968985046475887/9640000000000000000 : ℝ)+2*(105680034679/192800000000000 : ℝ)*(423/4000 : ℝ)=(5000044891811829/5000000000000000 : ℝ) by norm_num, show 1+2*(2147741428104611/100000000000000000000 : ℝ)=(50002147741428104611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4329233736285139/25000000000000000000 : ℝ)+(2147741428104611/100000000000000000000 : ℝ) ≤ ((9638968985046475887/9640000000000000000 : ℝ)+(105680034679/192800000000000 : ℝ)*((16359/100000 : ℝ)+(423/4000 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (9638968985046475887/9640000000000000000 : ℝ)+(105680034679/192800000000000 : ℝ)*((16359/100000 : ℝ)+(423/4000 : ℝ))=(2000081364745539/2000000000000000 : ℝ) by norm_num, show 1+(4329233736285139/25000000000000000000 : ℝ)+(2147741428104611/100000000000000000000 : ℝ)=(100019464676373245167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4329233736285139/25000000000000000000 : ℝ) ≤ ((9638968985046475887/9640000000000000000 : ℝ)+2*(105680034679/192800000000000 : ℝ)*(16359/100000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (9638968985046475887/9640000000000000000 : ℝ)+2*(105680034679/192800000000000 : ℝ)*(16359/100000 : ℝ)=(2500180965957933/2500000000000000 : ℝ) by norm_num, show 1+2*(4329233736285139/25000000000000000000 : ℝ)=(12504329233736285139/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9638968985046475887/9640000000000000000 : ℝ)*(X 1 0+X 2 0)+(105680034679/192800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (423/4000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (9638968985046475887/9640000000000000000 : ℝ)) (alpha := (105680034679/192800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9638968985046475887/9640000000000000000 : ℝ)*(X 0 1+X 2 1)+(105680034679/192800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (423/4000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (9638968985046475887/9640000000000000000 : ℝ)) (alpha := (105680034679/192800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9638968985046475887/9640000000000000000 : ℝ)*(X 0 2+X 1 2)+(105680034679/192800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (423/4000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (9638968985046475887/9640000000000000000 : ℝ)) (alpha := (105680034679/192800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-808828353/5000000000 : ℝ)*X 0 0+(5448803937/10000000000 : ℝ)*X 0 1+(647945971/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668545981/1250000000 : ℝ)*X 1 0+(-109638871/625000000 : ℝ)*X 1 1+(2591783869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534836783/1000000000 : ℝ)*X 2 0+(5183567713/10000000000 : ℝ)*X 2 1+(-1754221993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((130743511/312500000 : ℝ)*X 0 0+(481570643/1250000000 : ℝ)*X 0 1+(4535341097/10000000000 : ℝ)*X 0 2+(130743511/312500000 : ℝ)*X 1 0+(481570643/1250000000 : ℝ)*X 1 1+(4535341097/10000000000 : ℝ)*X 1 2+(130743511/312500000 : ℝ)*X 2 0+(481570643/1250000000 : ℝ)*X 2 1+(4535341097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-808860879/5000000000 : ℝ)*X 0 0+(518557253/1000000000 : ℝ)*X 0 1+(2723389001/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277543103/10000000000 : ℝ)*X 1 0+(-1491011831/10000000000 : ℝ)*X 1 1+(5446777709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277543213/10000000000 : ℝ)*X 2 0+(1089355533/2000000000 : ℝ)*X 2 1+(-74550587/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((418396051/1000000000 : ℝ)*X 0 0+(4530178783/10000000000 : ℝ)*X 0 1+(3857781067/10000000000 : ℝ)*X 0 2+(418396051/1000000000 : ℝ)*X 1 0+(4530178783/10000000000 : ℝ)*X 1 1+(3857781067/10000000000 : ℝ)*X 1 2+(418396051/1000000000 : ℝ)*X 2 0+(4530178783/10000000000 : ℝ)*X 2 1+(3857781067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78273656216448359964485193/6025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2046484077/100000000000000 : ℝ)*(base19) + (380305457/20000000000000 : ℝ)*(base23) + (17685433/25000000000000 : ℝ)*(lower2) + (21146187/6250000000000 : ℝ)*(upper3) + (196445187/100000000000000 : ℝ)*(upper5) + (65436314614613/2500000000000 : ℝ)*(major0) + (65436314614613/2500000000000 : ℝ)*(major1) + (65436314614613/2500000000000 : ℝ)*(major2) + (377025102604699/10000000000000 : ℝ)*(sp0) + (471284142965149/12500000000000 : ℝ)*(sp1) + (117821040271187/3125000000000 : ℝ)*(sp2) + (146461863679623/10000000000000 : ℝ)*(sp3) + (12082079139/50000000000000 : ℝ)*(sp4) + (5454559131/50000000000000 : ℝ)*(sp7) + (366157386478623/25000000000000 : ℝ)*(f.failure) + (3770275190205269/100000000000000 : ℝ)*(f.sum) + (66680414529/241000000000000000000000000 : ℝ)*base66 + (89603541773913269/24100000000000000000000000000000 : ℝ)*base68 + (66613055779686731/24100000000000000000000000000000 : ℝ)*base69 + (158755025229913269/24100000000000000000000000000000 : ℝ)*base72 + (486294103287/241000000000000000000000000 : ℝ)*base74 + (98329388382313269/24100000000000000000000000000000 : ℝ)*base76 + (315063284916313269/24100000000000000000000000000000 : ℝ)*base78 + (106194647464113269/24100000000000000000000000000000 : ℝ)*base80 + (283080959199/48200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (73513/156250000000000000000 : ℝ)*base89 + (73513/156250000000000000000 : ℝ)*base91 + (73513/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (202983753814827745815386259/30125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (686070531/50000000000000 : ℝ)*(base19) + (1714153817/100000000000000 : ℝ)*(base23) + (9057697/12500000000000 : ℝ)*(upper3) + (141108773/100000000000000 : ℝ)*(lower4) + (347477291/100000000000000 : ℝ)*(upper5) + (166113160910427/6250000000000 : ℝ)*(major0) + (166113160910427/6250000000000 : ℝ)*(major1) + (166113160910427/6250000000000 : ℝ)*(major2) + (16721721459/100000000000000 : ℝ)*(sp1) + (3267469069/20000000000000 : ℝ)*(sp2) + (1914204270910201/50000000000000 : ℝ)*(sp4) + (95709761198947/2500000000000 : ℝ)*(sp5) + (95709762258031/2500000000000 : ℝ)*(sp6) + (148721238271159/10000000000000 : ℝ)*(sp7) + (148721238271159/10000000000000 : ℝ)*(f.failure) + (1914204270910201/50000000000000 : ℝ)*(f.sum) + (618878822927/602500000000000000000000000 : ℝ)*base66 + (492164655911523749/60250000000000000000000000000000 : ℝ)*base67 + (2939999845523749/60250000000000000000000000000000 : ℝ)*base69 + (360668383706023749/60250000000000000000000000000000 : ℝ)*base71 + (6655565229/75312500000000000000000000 : ℝ)*base74 + (1123518310901023749/60250000000000000000000000000000 : ℝ)*base75 + (445365206926523749/60250000000000000000000000000000 : ℝ)*base77 + (349059246030273749/60250000000000000000000000000000 : ℝ)*base79 + (2854062899859/1205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (259471/62500000000000000000 : ℝ)*base90 + (259471/62500000000000000000 : ℝ)*base92 + (259471/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1646_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1646_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1646_s4_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-323541473/2000000000 : ℝ)*x 0 + (5448552653/10000000000 : ℝ)*x 1 + (518378513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323541473/2000000000 : ℝ)^4903 ≤ (5000702035747/50000000000000 : ℝ)^3879 := by
    have hnat : (323541473 : ℕ)^4903*50000000000000^3879 ≤ 5000702035747^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323541473 2000000000 5000702035747 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448552653/10000000000 : ℝ)^4903 ≤ (23207758035809/50000000000000 : ℝ)^3879 := by
    have hnat : (5448552653 : ℕ)^4903*50000000000000^3879 ≤ 23207758035809^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448552653 10000000000 23207758035809 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518378513/1000000000 : ℝ)^4903 ≤ (43583079845241/100000000000000 : ℝ)^3879 := by
    have hnat : (518378513 : ℕ)^4903*100000000000000^3879 ≤ 43583079845241^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518378513 1000000000 43583079845241 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-323541473/2000000000 : ℝ), (5448552653/10000000000 : ℝ), (518378513/1000000000 : ℝ)] ![(5000702035747/50000000000000 : ℝ), (23207758035809/50000000000000 : ℝ), (43583079845241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-323541473/2000000000 : ℝ)|^4903 ≤ (5000702035747/50000000000000 : ℝ)^3879
        have hw : |(-323541473/2000000000 : ℝ)|=(323541473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448552653/10000000000 : ℝ)|^4903 ≤ (23207758035809/50000000000000 : ℝ)^3879
        have hw : |(5448552653/10000000000 : ℝ)|=(5448552653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518378513/1000000000 : ℝ)|^4903 ≤ (43583079845241/100000000000000 : ℝ)^3879
        have hw : |(518378513/1000000000 : ℝ)|=(518378513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s4_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069659899/2000000000 : ℝ)*x 0 + (-35080483/200000000 : ℝ)*x 1 + (129594631/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069659899/2000000000 : ℝ)^4903 ≤ (45338650833251/100000000000000 : ℝ)^3879 := by
    have hnat : (1069659899 : ℕ)^4903*100000000000000^3879 ≤ 45338650833251^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069659899 2000000000 45338650833251 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35080483/200000000 : ℝ)^4903 ≤ (5539134065753/50000000000000 : ℝ)^3879 := by
    have hnat : (35080483 : ℕ)^4903*50000000000000^3879 ≤ 5539134065753^3879*200000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35080483 200000000 5539134065753 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129594631/250000000 : ℝ)^4903 ≤ (21791540507109/50000000000000 : ℝ)^3879 := by
    have hnat : (129594631 : ℕ)^4903*50000000000000^3879 ≤ 21791540507109^3879*250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129594631 250000000 21791540507109 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069659899/2000000000 : ℝ), (-35080483/200000000 : ℝ), (129594631/250000000 : ℝ)] ![(45338650833251/100000000000000 : ℝ), (5539134065753/50000000000000 : ℝ), (21791540507109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069659899/2000000000 : ℝ)|^4903 ≤ (45338650833251/100000000000000 : ℝ)^3879
        have hw : |(1069659899/2000000000 : ℝ)|=(1069659899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35080483/200000000 : ℝ)|^4903 ≤ (5539134065753/50000000000000 : ℝ)^3879
        have hw : |(-35080483/200000000 : ℝ)|=(35080483/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129594631/250000000 : ℝ)|^4903 ≤ (21791540507109/50000000000000 : ℝ)^3879
        have hw : |(129594631/250000000 : ℝ)|=(129594631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s4_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337074883/2500000000 : ℝ)*x 0 + (5183785061/10000000000 : ℝ)*x 1 + (-87701217/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337074883/2500000000 : ℝ)^4903 ≤ (45338651229709/100000000000000 : ℝ)^3879 := by
    have hnat : (1337074883 : ℕ)^4903*100000000000000^3879 ≤ 45338651229709^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337074883 2500000000 45338651229709 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183785061/10000000000 : ℝ)^4903 ≤ (21791539555987/50000000000000 : ℝ)^3879 := by
    have hnat : (5183785061 : ℕ)^4903*50000000000000^3879 ≤ 21791539555987^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183785061 10000000000 21791539555987 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87701217/500000000 : ℝ)^4903 ≤ (11078269648319/100000000000000 : ℝ)^3879 := by
    have hnat : (87701217 : ℕ)^4903*100000000000000^3879 ≤ 11078269648319^3879*500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87701217 500000000 11078269648319 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337074883/2500000000 : ℝ), (5183785061/10000000000 : ℝ), (-87701217/500000000 : ℝ)] ![(45338651229709/100000000000000 : ℝ), (21791539555987/50000000000000 : ℝ), (11078269648319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337074883/2500000000 : ℝ)|^4903 ≤ (45338651229709/100000000000000 : ℝ)^3879
        have hw : |(1337074883/2500000000 : ℝ)|=(1337074883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183785061/10000000000 : ℝ)|^4903 ≤ (21791539555987/50000000000000 : ℝ)^3879
        have hw : |(5183785061/10000000000 : ℝ)|=(5183785061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87701217/500000000 : ℝ)|^4903 ≤ (11078269648319/100000000000000 : ℝ)^3879
        have hw : |(-87701217/500000000 : ℝ)|=(87701217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s4_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183824757/10000000000 : ℝ)*x 0 + (3853164901/10000000000 : ℝ)*x 1 + (28342093/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183824757/10000000000 : ℝ)^4903 ≤ (33241020552039/100000000000000 : ℝ)^3879 := by
    have hnat : (4183824757 : ℕ)^4903*100000000000000^3879 ≤ 33241020552039^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183824757 10000000000 33241020552039 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3853164901/10000000000 : ℝ)^4903 ≤ (29955696391341/100000000000000 : ℝ)^3879 := by
    have hnat : (3853164901 : ℕ)^4903*100000000000000^3879 ≤ 29955696391341^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3853164901 10000000000 29955696391341 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28342093/62500000 : ℝ)^4903 ≤ (1840164151933/5000000000000 : ℝ)^3879 := by
    have hnat : (28342093 : ℕ)^4903*5000000000000^3879 ≤ 1840164151933^3879*62500000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28342093 62500000 1840164151933 5000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183824757/10000000000 : ℝ), (3853164901/10000000000 : ℝ), (28342093/62500000 : ℝ)] ![(33241020552039/100000000000000 : ℝ), (29955696391341/100000000000000 : ℝ), (1840164151933/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183824757/10000000000 : ℝ)|^4903 ≤ (33241020552039/100000000000000 : ℝ)^3879
        have hw : |(4183824757/10000000000 : ℝ)|=(4183824757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3853164901/10000000000 : ℝ)|^4903 ≤ (29955696391341/100000000000000 : ℝ)^3879
        have hw : |(3853164901/10000000000 : ℝ)|=(3853164901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28342093/62500000 : ℝ)|^4903 ≤ (1840164151933/5000000000000 : ℝ)^3879
        have hw : |(28342093/62500000 : ℝ)|=(28342093/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s4_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1617772021/10000000000 : ℝ)*x 0 + (518578313/1000000000 : ℝ)*x 1 + (10637761/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1617772021/10000000000 : ℝ)^4903 ≤ (2500477332679/25000000000000 : ℝ)^3879 := by
    have hnat : (1617772021 : ℕ)^4903*25000000000000^3879 ≤ 2500477332679^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617772021 10000000000 2500477332679 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518578313/1000000000 : ℝ)^4903 ≤ (43604313786649/100000000000000 : ℝ)^3879 := by
    have hnat : (518578313 : ℕ)^4903*100000000000000^3879 ≤ 43604313786649^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518578313 1000000000 43604313786649 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10637761/19531250 : ℝ)^4903 ≤ (23196888431337/50000000000000 : ℝ)^3879 := by
    have hnat : (10637761 : ℕ)^4903*50000000000000^3879 ≤ 23196888431337^3879*19531250^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10637761 19531250 23196888431337 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1617772021/10000000000 : ℝ), (518578313/1000000000 : ℝ), (10637761/19531250 : ℝ)] ![(2500477332679/25000000000000 : ℝ), (43604313786649/100000000000000 : ℝ), (23196888431337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1617772021/10000000000 : ℝ)|^4903 ≤ (2500477332679/25000000000000 : ℝ)^3879
        have hw : |(-1617772021/10000000000 : ℝ)|=(1617772021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518578313/1000000000 : ℝ)|^4903 ≤ (43604313786649/100000000000000 : ℝ)^3879
        have hw : |(518578313/1000000000 : ℝ)|=(518578313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10637761/19531250 : ℝ)|^4903 ≤ (23196888431337/50000000000000 : ℝ)^3879
        have hw : |(10637761/19531250 : ℝ)|=(10637761/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s4_5 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277600133/10000000000 : ℝ)*x 0 + (-149127581/1000000000 : ℝ)*x 1 + (5446533633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277600133/10000000000 : ℝ)^4903 ≤ (11145607090047/25000000000000 : ℝ)^3879 := by
    have hnat : (5277600133 : ℕ)^4903*25000000000000^3879 ≤ 11145607090047^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277600133 10000000000 11145607090047 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149127581/1000000000 : ℝ)^4903 ≤ (9023794764833/100000000000000 : ℝ)^3879 := by
    have hnat : (149127581 : ℕ)^4903*100000000000000^3879 ≤ 9023794764833^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149127581 1000000000 9023794764833 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446533633/10000000000 : ℝ)^4903 ≤ (289961105459/625000000000 : ℝ)^3879 := by
    have hnat : (5446533633 : ℕ)^4903*625000000000^3879 ≤ 289961105459^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446533633 10000000000 289961105459 625000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277600133/10000000000 : ℝ), (-149127581/1000000000 : ℝ), (5446533633/10000000000 : ℝ)] ![(11145607090047/25000000000000 : ℝ), (9023794764833/100000000000000 : ℝ), (289961105459/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277600133/10000000000 : ℝ)|^4903 ≤ (11145607090047/25000000000000 : ℝ)^3879
        have hw : |(5277600133/10000000000 : ℝ)|=(5277600133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149127581/1000000000 : ℝ)|^4903 ≤ (9023794764833/100000000000000 : ℝ)^3879
        have hw : |(-149127581/1000000000 : ℝ)|=(149127581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446533633/10000000000 : ℝ)|^4903 ≤ (289961105459/625000000000 : ℝ)^3879
        have hw : |(5446533633/10000000000 : ℝ)|=(5446533633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s4_6 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277600133/10000000000 : ℝ)*x 0 + (5446533633/10000000000 : ℝ)*x 1 + (-149127581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277600133/10000000000 : ℝ)^4903 ≤ (11145607090047/25000000000000 : ℝ)^3879 := by
    have hnat : (5277600133 : ℕ)^4903*25000000000000^3879 ≤ 11145607090047^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277600133 10000000000 11145607090047 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446533633/10000000000 : ℝ)^4903 ≤ (289961105459/625000000000 : ℝ)^3879 := by
    have hnat : (5446533633 : ℕ)^4903*625000000000^3879 ≤ 289961105459^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446533633 10000000000 289961105459 625000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149127581/1000000000 : ℝ)^4903 ≤ (9023794764833/100000000000000 : ℝ)^3879 := by
    have hnat : (149127581 : ℕ)^4903*100000000000000^3879 ≤ 9023794764833^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149127581 1000000000 9023794764833 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277600133/10000000000 : ℝ), (5446533633/10000000000 : ℝ), (-149127581/1000000000 : ℝ)] ![(11145607090047/25000000000000 : ℝ), (289961105459/625000000000 : ℝ), (9023794764833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277600133/10000000000 : ℝ)|^4903 ≤ (11145607090047/25000000000000 : ℝ)^3879
        have hw : |(5277600133/10000000000 : ℝ)|=(5277600133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446533633/10000000000 : ℝ)|^4903 ≤ (289961105459/625000000000 : ℝ)^3879
        have hw : |(5446533633/10000000000 : ℝ)|=(5446533633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-149127581/1000000000 : ℝ)|^4903 ≤ (9023794764833/100000000000000 : ℝ)^3879
        have hw : |(-149127581/1000000000 : ℝ)|=(149127581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s4_7 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209199569/500000000 : ℝ)*x 0 + (2264795591/5000000000 : ℝ)*x 1 + (771672513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209199569/500000000 : ℝ)^4903 ≤ (8310673469173/25000000000000 : ℝ)^3879 := by
    have hnat : (209199569 : ℕ)^4903*25000000000000^3879 ≤ 8310673469173^3879*500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209199569 500000000 8310673469173 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264795591/5000000000 : ℝ)^4903 ≤ (36750525176199/100000000000000 : ℝ)^3879 := by
    have hnat : (2264795591 : ℕ)^4903*100000000000000^3879 ≤ 36750525176199^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264795591 5000000000 36750525176199 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771672513/2000000000 : ℝ)^4903 ≤ (30006780924999/100000000000000 : ℝ)^3879 := by
    have hnat : (771672513 : ℕ)^4903*100000000000000^3879 ≤ 30006780924999^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771672513 2000000000 30006780924999 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209199569/500000000 : ℝ), (2264795591/5000000000 : ℝ), (771672513/2000000000 : ℝ)] ![(8310673469173/25000000000000 : ℝ), (36750525176199/100000000000000 : ℝ), (30006780924999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209199569/500000000 : ℝ)|^4903 ≤ (8310673469173/25000000000000 : ℝ)^3879
        have hw : |(209199569/500000000 : ℝ)|=(209199569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264795591/5000000000 : ℝ)|^4903 ≤ (36750525176199/100000000000000 : ℝ)^3879
        have hw : |(2264795591/5000000000 : ℝ)|=(2264795591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(771672513/2000000000 : ℝ)|^4903 ≤ (30006780924999/100000000000000 : ℝ)^3879
        have hw : |(771672513/2000000000 : ℝ)|=(771672513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10649/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4069/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2661/25000 : ℝ) ^ (4899/1024 : ℝ) ≤ (553904470043697/25000000000000000000 : ℝ) := by
    have hpowers : (2661/25000 : ℝ)^4899 ≤ (553904470043697/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2661 : ℕ)^4899*25000000000000000000^1024 ≤ 553904470043697^1024*25000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2661 25000 553904470043697 25000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2661/25000 : ℝ)) (X := (553904470043697/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16281/100000 : ℝ) ^ (4899/1024 : ℝ) ≤ (16925465346587583/100000000000000000000 : ℝ) := by
    have hpowers : (16281/100000 : ℝ)^4899 ≤ (16925465346587583/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16281 : ℕ)^4899*100000000000000000000^1024 ≤ 16925465346587583^1024*100000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16281 100000 16925465346587583 100000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16281/100000 : ℝ)) (X := (16925465346587583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500553904470043697/12500000000000000000 : ℝ) ≤ (10000092621063469/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (12500553904470043697/12500000000000000000 : ℝ)^1024 ≤ (10000092621063469/10000000000000000 : ℝ)^4899 := by
      have hnat : (12500553904470043697 : ℕ)^1024*10000000000000000^4899 ≤ 10000092621063469^4899*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500553904470043697 12500000000000000000 10000092621063469 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000092621063469/10000000000000000 : ℝ)) (X := (12500553904470043697/12500000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019141083226762371/100000000000000000000 : ℝ) ≤ (78128125476121/78125000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (100019141083226762371/100000000000000000000 : ℝ)^1024 ≤ (78128125476121/78125000000000 : ℝ)^4899 := by
      have hnat : (100019141083226762371 : ℕ)^1024*78125000000000^4899 ≤ 78128125476121^4899*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019141083226762371 100000000000000000000 78128125476121 78125000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78128125476121/78125000000000 : ℝ)) (X := (100019141083226762371/100000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016925465346587583/50000000000000000000 : ℝ) ≤ (10000707500823507/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (50016925465346587583/50000000000000000000 : ℝ)^1024 ≤ (10000707500823507/10000000000000000 : ℝ)^4899 := by
      have hnat : (50016925465346587583 : ℕ)^1024*10000000000000000^4899 ≤ 10000707500823507^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016925465346587583 50000000000000000000 10000707500823507 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000707500823507/10000000000000000 : ℝ)) (X := (50016925465346587583/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(553904470043697/25000000000000000000 : ℝ) ≤ ((18787992441589643427/18790000000000000000 : ℝ)+2*(307439880019/563700000000000 : ℝ)*(2661/25000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (18787992441589643427/18790000000000000000 : ℝ)+2*(307439880019/563700000000000 : ℝ)*(2661/25000 : ℝ)=(10000092621063469/10000000000000000 : ℝ) by norm_num, show 1+2*(553904470043697/25000000000000000000 : ℝ)=(12500553904470043697/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16925465346587583/100000000000000000000 : ℝ)+(553904470043697/25000000000000000000 : ℝ) ≤ ((18787992441589643427/18790000000000000000 : ℝ)+(307439880019/563700000000000 : ℝ)*((16281/100000 : ℝ)+(2661/25000 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (18787992441589643427/18790000000000000000 : ℝ)+(307439880019/563700000000000 : ℝ)*((16281/100000 : ℝ)+(2661/25000 : ℝ))=(78128125476121/78125000000000 : ℝ) by norm_num, show 1+(16925465346587583/100000000000000000000 : ℝ)+(553904470043697/25000000000000000000 : ℝ)=(100019141083226762371/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16925465346587583/100000000000000000000 : ℝ) ≤ ((18787992441589643427/18790000000000000000 : ℝ)+2*(307439880019/563700000000000 : ℝ)*(16281/100000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (18787992441589643427/18790000000000000000 : ℝ)+2*(307439880019/563700000000000 : ℝ)*(16281/100000 : ℝ)=(10000707500823507/10000000000000000 : ℝ) by norm_num, show 1+2*(16925465346587583/100000000000000000000 : ℝ)=(50016925465346587583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18787992441589643427/18790000000000000000 : ℝ)*(X 1 0+X 2 0)+(307439880019/563700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (18787992441589643427/18790000000000000000 : ℝ)) (alpha := (307439880019/563700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18787992441589643427/18790000000000000000 : ℝ)*(X 0 1+X 2 1)+(307439880019/563700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (18787992441589643427/18790000000000000000 : ℝ)) (alpha := (307439880019/563700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18787992441589643427/18790000000000000000 : ℝ)*(X 0 2+X 1 2)+(307439880019/563700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (18787992441589643427/18790000000000000000 : ℝ)) (alpha := (307439880019/563700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-323541473/2000000000 : ℝ)*X 0 0+(5448552653/10000000000 : ℝ)*X 0 1+(518378513/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069659899/2000000000 : ℝ)*X 1 0+(-35080483/200000000 : ℝ)*X 1 1+(129594631/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337074883/2500000000 : ℝ)*X 2 0+(5183785061/10000000000 : ℝ)*X 2 1+(-87701217/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183824757/10000000000 : ℝ)*X 0 0+(3853164901/10000000000 : ℝ)*X 0 1+(28342093/62500000 : ℝ)*X 0 2+(4183824757/10000000000 : ℝ)*X 1 0+(3853164901/10000000000 : ℝ)*X 1 1+(28342093/62500000 : ℝ)*X 1 2+(4183824757/10000000000 : ℝ)*X 2 0+(3853164901/10000000000 : ℝ)*X 2 1+(28342093/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1617772021/10000000000 : ℝ)*X 0 0+(518578313/1000000000 : ℝ)*X 0 1+(10637761/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277600133/10000000000 : ℝ)*X 1 0+(-149127581/1000000000 : ℝ)*X 1 1+(5446533633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277600133/10000000000 : ℝ)*X 2 0+(5446533633/10000000000 : ℝ)*X 2 1+(-149127581/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((209199569/500000000 : ℝ)*X 0 0+(2264795591/5000000000 : ℝ)*X 0 1+(771672513/2000000000 : ℝ)*X 0 2+(209199569/500000000 : ℝ)*X 1 0+(2264795591/5000000000 : ℝ)*X 1 1+(771672513/2000000000 : ℝ)*X 1 2+(209199569/500000000 : ℝ)*X 2 0+(2264795591/5000000000 : ℝ)*X 2 1+(771672513/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5567720973136977878547103/587187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (744506559/50000000000000 : ℝ)*(base19) + (1469584681/100000000000000 : ℝ)*(base23) + (12182789/50000000000000 : ℝ)*(lower2) + (55189791/20000000000000 : ℝ)*(upper3) + (3041471/3125000000000 : ℝ)*(upper5) + (3277598064767/125000000000 : ℝ)*(major0) + (3277598064767/125000000000 : ℝ)*(major1) + (3277598064767/125000000000 : ℝ)*(major2) + (3776920205004563/100000000000000 : ℝ)*(sp0) + (3776937088620059/100000000000000 : ℝ)*(sp1) + (236058569253031/6250000000000 : ℝ)*(sp2) + (293441712164203/20000000000000 : ℝ)*(sp3) + (9186314307/50000000000000 : ℝ)*(sp4) + (2362276453/25000000000000 : ℝ)*(sp7) + (733609004963413/50000000000000 : ℝ)*(f.failure) + (1888469288816589/50000000000000 : ℝ)*(f.sum) + (5932018917191/2818500000000000000000000000 : ℝ)*base66 + (119199726934497973/7046250000000000000000000000000 : ℝ)*base68 + (74391520164522973/7046250000000000000000000000000 : ℝ)*base70 + (81988884871490473/7046250000000000000000000000000 : ℝ)*base72 + (14296907557667/5637000000000000000000000000 : ℝ)*base73 + (103661888733665473/7046250000000000000000000000000 : ℝ)*base76 + (31210321472589223/7046250000000000000000000000000 : ℝ)*base78 + (52831667500359223/7046250000000000000000000000000 : ℝ)*base80 + (145471642309/56370000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (971997/312500000000000000000 : ℝ)*base90 + (971997/312500000000000000000 : ℝ)*base92 + (971997/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50260580535901415469513/4697500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1581056749/100000000000000 : ℝ)*(base19) + (10685923/625000000000 : ℝ)*(base23) + (123924451/25000000000000 : ℝ)*(lower1) + (224614563/100000000000000 : ℝ)*(upper3) + (57948313/100000000000000 : ℝ)*(lower4) + (55413013/25000000000000 : ℝ)*(upper5) + (1331215468058367/50000000000000 : ℝ)*(major0) + (1331215468058367/50000000000000 : ℝ)*(major1) + (1331215468058367/50000000000000 : ℝ)*(major2) + (28202831/2000000000000 : ℝ)*(sp2) + (958765937409/25000000000 : ℝ)*(sp4) + (3835062168579251/100000000000000 : ℝ)*(sp5) + (383506062974677/10000000000000 : ℝ)*(sp6) + (372449441487431/25000000000000 : ℝ)*(sp7) + (372449441487431/25000000000000 : ℝ)*(f.failure) + (958765937409/25000000000 : ℝ)*(f.sum) + (12940001916791/4697500000000000000000000000 : ℝ)*base65 + (13605683608817003709/939500000000000000000000000000000 : ℝ)*base67 + (9789294705516996291/939500000000000000000000000000000 : ℝ)*base70 + (7311497970784503709/939500000000000000000000000000000 : ℝ)*base71 + (5697873960241/1174375000000000000000000000 : ℝ)*base74 + (126888102027095496291/939500000000000000000000000000000 : ℝ)*base76 + (7277466361281996291/939500000000000000000000000000000 : ℝ)*base78 + (2873944256397003709/939500000000000000000000000000000 : ℝ)*base79 + (23168263065609/4697500000000000000000000000 : ℝ)*base82 + (1046761/156250000000000000000 : ℝ)*base89 + (1046761/156250000000000000000 : ℝ)*base91 + (1046761/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1646_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1646_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1646_s5_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348295243/10000000000 : ℝ)*x 0 + (5183799631/10000000000 : ℝ)*x 1 + (-17540107/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348295243/10000000000 : ℝ)^4903 ≤ (45338605272781/100000000000000 : ℝ)^3879 := by
    have hnat : (5348295243 : ℕ)^4903*100000000000000^3879 ≤ 45338605272781^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348295243 10000000000 45338605272781 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183799631/10000000000 : ℝ)^4903 ≤ (21791616974131/50000000000000 : ℝ)^3879 := by
    have hnat : (5183799631 : ℕ)^4903*50000000000000^3879 ≤ 21791616974131^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183799631 10000000000 21791616974131 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17540107/100000000 : ℝ)^4903 ≤ (5539080378613/50000000000000 : ℝ)^3879 := by
    have hnat : (17540107 : ℕ)^4903*50000000000000^3879 ≤ 5539080378613^3879*100000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17540107 100000000 5539080378613 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348295243/10000000000 : ℝ), (5183799631/10000000000 : ℝ), (-17540107/100000000 : ℝ)] ![(45338605272781/100000000000000 : ℝ), (21791616974131/50000000000000 : ℝ), (5539080378613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348295243/10000000000 : ℝ)|^4903 ≤ (45338605272781/100000000000000 : ℝ)^3879
        have hw : |(5348295243/10000000000 : ℝ)|=(5348295243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183799631/10000000000 : ℝ)|^4903 ≤ (21791616974131/50000000000000 : ℝ)^3879
        have hw : |(5183799631/10000000000 : ℝ)|=(5183799631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17540107/100000000 : ℝ)|^4903 ≤ (5539080378613/50000000000000 : ℝ)^3879
        have hw : |(-17540107/100000000 : ℝ)|=(17540107/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s5_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-202221847/1250000000 : ℝ)*x 0 + (1296449327/2500000000 : ℝ)*x 1 + (5446517637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202221847/1250000000 : ℝ)^4903 ≤ (10001930859991/100000000000000 : ℝ)^3879 := by
    have hnat : (202221847 : ℕ)^4903*100000000000000^3879 ≤ 10001930859991^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202221847 1250000000 10001930859991 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296449327/2500000000 : ℝ)^4903 ≤ (5450558059057/12500000000000 : ℝ)^3879 := by
    have hnat : (1296449327 : ℕ)^4903*12500000000000^3879 ≤ 5450558059057^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296449327 2500000000 5450558059057 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446517637/10000000000 : ℝ)^4903 ≤ (23196802324877/50000000000000 : ℝ)^3879 := by
    have hnat : (5446517637 : ℕ)^4903*50000000000000^3879 ≤ 23196802324877^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446517637 10000000000 23196802324877 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202221847/1250000000 : ℝ), (1296449327/2500000000 : ℝ), (5446517637/10000000000 : ℝ)] ![(10001930859991/100000000000000 : ℝ), (5450558059057/12500000000000 : ℝ), (23196802324877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202221847/1250000000 : ℝ)|^4903 ≤ (10001930859991/100000000000000 : ℝ)^3879
        have hw : |(-202221847/1250000000 : ℝ)|=(202221847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296449327/2500000000 : ℝ)|^4903 ≤ (5450558059057/12500000000000 : ℝ)^3879
        have hw : |(1296449327/2500000000 : ℝ)|=(1296449327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446517637/10000000000 : ℝ)|^4903 ≤ (23196802324877/50000000000000 : ℝ)^3879
        have hw : |(5446517637/10000000000 : ℝ)|=(5446517637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s5_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277604109/10000000000 : ℝ)*x 0 + (-298258543/2000000000 : ℝ)*x 1 + (68081471/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277604109/10000000000 : ℝ)^4903 ≤ (4458247081391/10000000000000 : ℝ)^3879 := by
    have hnat : (5277604109 : ℕ)^4903*10000000000000^3879 ≤ 4458247081391^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277604109 10000000000 4458247081391 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298258543/2000000000 : ℝ)^4903 ≤ (9023924062049/100000000000000 : ℝ)^3879 := by
    have hnat : (298258543 : ℕ)^4903*100000000000000^3879 ≤ 9023924062049^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298258543 2000000000 9023924062049 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68081471/125000000 : ℝ)^4903 ≤ (46393605112721/100000000000000 : ℝ)^3879 := by
    have hnat : (68081471 : ℕ)^4903*100000000000000^3879 ≤ 46393605112721^3879*125000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68081471 125000000 46393605112721 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277604109/10000000000 : ℝ), (-298258543/2000000000 : ℝ), (68081471/125000000 : ℝ)] ![(4458247081391/10000000000000 : ℝ), (9023924062049/100000000000000 : ℝ), (46393605112721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277604109/10000000000 : ℝ)|^4903 ≤ (4458247081391/10000000000000 : ℝ)^3879
        have hw : |(5277604109/10000000000 : ℝ)|=(5277604109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-298258543/2000000000 : ℝ)|^4903 ≤ (9023924062049/100000000000000 : ℝ)^3879
        have hw : |(-298258543/2000000000 : ℝ)|=(298258543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68081471/125000000 : ℝ)|^4903 ≤ (46393605112721/100000000000000 : ℝ)^3879
        have hw : |(68081471/125000000 : ℝ)|=(68081471/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s5_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105552083/200000000 : ℝ)*x 0 + (1361629407/2500000000 : ℝ)*x 1 + (-1491292731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105552083/200000000 : ℝ)^4903 ≤ (44582471251687/100000000000000 : ℝ)^3879 := by
    have hnat : (105552083 : ℕ)^4903*100000000000000^3879 ≤ 44582471251687^3879*200000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105552083 200000000 44582471251687 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361629407/2500000000 : ℝ)^4903 ≤ (23196802276427/50000000000000 : ℝ)^3879 := by
    have hnat : (1361629407 : ℕ)^4903*50000000000000^3879 ≤ 23196802276427^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361629407 2500000000 23196802276427 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491292731/10000000000 : ℝ)^4903 ≤ (360956967377/4000000000000 : ℝ)^3879 := by
    have hnat : (1491292731 : ℕ)^4903*4000000000000^3879 ≤ 360956967377^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491292731 10000000000 360956967377 4000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105552083/200000000 : ℝ), (1361629407/2500000000 : ℝ), (-1491292731/10000000000 : ℝ)] ![(44582471251687/100000000000000 : ℝ), (23196802276427/50000000000000 : ℝ), (360956967377/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105552083/200000000 : ℝ)|^4903 ≤ (44582471251687/100000000000000 : ℝ)^3879
        have hw : |(105552083/200000000 : ℝ)|=(105552083/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361629407/2500000000 : ℝ)|^4903 ≤ (23196802276427/50000000000000 : ℝ)^3879
        have hw : |(1361629407/2500000000 : ℝ)|=(1361629407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1491292731/10000000000 : ℝ)|^4903 ≤ (360956967377/4000000000000 : ℝ)^3879
        have hw : |(-1491292731/10000000000 : ℝ)|=(1491292731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s5_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183993457/10000000000 : ℝ)*x 0 + (2264776087/5000000000 : ℝ)*x 1 + (3858401139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183993457/10000000000 : ℝ)^4903 ≤ (33242714735239/100000000000000 : ℝ)^3879 := by
    have hnat : (4183993457 : ℕ)^4903*100000000000000^3879 ≤ 33242714735239^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183993457 10000000000 33242714735239 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264776087/5000000000 : ℝ)^4903 ≤ (36750125139489/100000000000000 : ℝ)^3879 := by
    have hnat : (2264776087 : ℕ)^4903*100000000000000^3879 ≤ 36750125139489^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264776087 5000000000 36750125139489 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3858401139/10000000000 : ℝ)^4903 ≤ (30007160112257/100000000000000 : ℝ)^3879 := by
    have hnat : (3858401139 : ℕ)^4903*100000000000000^3879 ≤ 30007160112257^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858401139 10000000000 30007160112257 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183993457/10000000000 : ℝ), (2264776087/5000000000 : ℝ), (3858401139/10000000000 : ℝ)] ![(33242714735239/100000000000000 : ℝ), (36750125139489/100000000000000 : ℝ), (30007160112257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183993457/10000000000 : ℝ)|^4903 ≤ (33242714735239/100000000000000 : ℝ)^3879
        have hw : |(4183993457/10000000000 : ℝ)|=(4183993457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264776087/5000000000 : ℝ)|^4903 ≤ (36750125139489/100000000000000 : ℝ)^3879
        have hw : |(2264776087/5000000000 : ℝ)|=(2264776087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3858401139/10000000000 : ℝ)|^4903 ≤ (30007160112257/100000000000000 : ℝ)^3879
        have hw : |(3858401139/10000000000 : ℝ)|=(3858401139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10649/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (651/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4069/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10649/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4069/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10649/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4069/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10649/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4069/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10649/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4069/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10649/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4069/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10649/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10649/100000 : ℝ) ^ (4899/1024 : ℝ) ≤ (444120319686881/20000000000000000000 : ℝ) := by
    have hpowers : (10649/100000 : ℝ)^4899 ≤ (444120319686881/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10649 : ℕ)^4899*20000000000000000000^1024 ≤ 444120319686881^1024*100000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10649 100000 444120319686881 20000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10649/100000 : ℝ)) (X := (444120319686881/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4069/25000 : ℝ) ^ (4899/1024 : ℝ) ≤ (8450306005883013/50000000000000000000 : ℝ) := by
    have hpowers : (4069/25000 : ℝ)^4899 ≤ (8450306005883013/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4069 : ℕ)^4899*50000000000000000000^1024 ≤ 8450306005883013^1024*25000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4069 25000 8450306005883013 50000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4069/25000 : ℝ)) (X := (8450306005883013/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000444120319686881/10000000000000000000 : ℝ) ≤ (10000092829397759/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (10000444120319686881/10000000000000000000 : ℝ)^1024 ≤ (10000092829397759/10000000000000000 : ℝ)^4899 := by
      have hnat : (10000444120319686881 : ℕ)^1024*10000000000000000^4899 ≤ 10000092829397759^4899*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000444120319686881 10000000000000000000 10000092829397759 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000092829397759/10000000000000000 : ℝ)) (X := (10000444120319686881/10000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019121213610200431/100000000000000000000 : ℝ) ≤ (1000039964568713/1000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (100019121213610200431/100000000000000000000 : ℝ)^1024 ≤ (1000039964568713/1000000000000000 : ℝ)^4899 := by
      have hnat : (100019121213610200431 : ℕ)^1024*1000000000000000^4899 ≤ 1000039964568713^4899*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019121213610200431 100000000000000000000 1000039964568713 1000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000039964568713/1000000000000000 : ℝ)) (X := (100019121213610200431/100000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008450306005883013/25000000000000000000 : ℝ) ≤ (10000706461976501/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (25008450306005883013/25000000000000000000 : ℝ)^1024 ≤ (10000706461976501/10000000000000000 : ℝ)^4899 := by
      have hnat : (25008450306005883013 : ℕ)^1024*10000000000000000^4899 ≤ 10000706461976501^4899*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008450306005883013 25000000000000000000 10000706461976501 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706461976501/10000000000000000 : ℝ)) (X := (25008450306005883013/25000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(444120319686881/20000000000000000000 : ℝ) ≤ ((11252797555538033267/11254000000000000000 : ℝ)+2*(306816289371/562700000000000 : ℝ)*(10649/100000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (11252797555538033267/11254000000000000000 : ℝ)+2*(306816289371/562700000000000 : ℝ)*(10649/100000 : ℝ)=(10000092829397759/10000000000000000 : ℝ) by norm_num, show 1+2*(444120319686881/20000000000000000000 : ℝ)=(10000444120319686881/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8450306005883013/50000000000000000000 : ℝ)+(444120319686881/20000000000000000000 : ℝ) ≤ ((11252797555538033267/11254000000000000000 : ℝ)+(306816289371/562700000000000 : ℝ)*((4069/25000 : ℝ)+(10649/100000 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (11252797555538033267/11254000000000000000 : ℝ)+(306816289371/562700000000000 : ℝ)*((4069/25000 : ℝ)+(10649/100000 : ℝ))=(1000039964568713/1000000000000000 : ℝ) by norm_num, show 1+(8450306005883013/50000000000000000000 : ℝ)+(444120319686881/20000000000000000000 : ℝ)=(100019121213610200431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8450306005883013/50000000000000000000 : ℝ) ≤ ((11252797555538033267/11254000000000000000 : ℝ)+2*(306816289371/562700000000000 : ℝ)*(4069/25000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (11252797555538033267/11254000000000000000 : ℝ)+2*(306816289371/562700000000000 : ℝ)*(4069/25000 : ℝ)=(10000706461976501/10000000000000000 : ℝ) by norm_num, show 1+2*(8450306005883013/50000000000000000000 : ℝ)=(25008450306005883013/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11252797555538033267/11254000000000000000 : ℝ)*(X 1 0+X 2 0)+(306816289371/562700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (4069/25000 : ℝ)) (c := (11252797555538033267/11254000000000000000 : ℝ)) (alpha := (306816289371/562700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11252797555538033267/11254000000000000000 : ℝ)*(X 0 1+X 2 1)+(306816289371/562700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (4069/25000 : ℝ)) (c := (11252797555538033267/11254000000000000000 : ℝ)) (alpha := (306816289371/562700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11252797555538033267/11254000000000000000 : ℝ)*(X 0 2+X 1 2)+(306816289371/562700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (4069/25000 : ℝ)) (c := (11252797555538033267/11254000000000000000 : ℝ)) (alpha := (306816289371/562700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348295243/10000000000 : ℝ)*X 2 0+(5183799631/10000000000 : ℝ)*X 2 1+(-17540107/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s5_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-202221847/1250000000 : ℝ)*X 0 0+(1296449327/2500000000 : ℝ)*X 0 1+(5446517637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5277604109/10000000000 : ℝ)*X 1 0+(-298258543/2000000000 : ℝ)*X 1 1+(68081471/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((105552083/200000000 : ℝ)*X 2 0+(1361629407/2500000000 : ℝ)*X 2 1+(-1491292731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4183993457/10000000000 : ℝ)*X 0 0+(2264776087/5000000000 : ℝ)*X 0 1+(3858401139/10000000000 : ℝ)*X 0 2+(4183993457/10000000000 : ℝ)*X 1 0+(2264776087/5000000000 : ℝ)*X 1 1+(3858401139/10000000000 : ℝ)*X 1 2+(4183993457/10000000000 : ℝ)*X 2 0+(2264776087/5000000000 : ℝ)*X 2 1+(3858401139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4577274072504031780509/1406750000000000000000000000 : ℝ) := by norm_num
    linear_combination (479126877/100000000000000 : ℝ)*(base19) + (266646183/50000000000000 : ℝ)*(base23) + (79856629/50000000000000 : ℝ)*(lower1) + (9368631/12500000000000 : ℝ)*(upper3) + (2656243/25000000000000 : ℝ)*(lower4) + (771297/1250000000000 : ℝ)*(upper5) + (133137411361417/5000000000000 : ℝ)*(major0) + (133137411361417/5000000000000 : ℝ)*(major1) + (133137411361417/5000000000000 : ℝ)*(major2) + (158138427/50000000000000 : ℝ)*(sp0) + (1917760517844961/50000000000000 : ℝ)*(sp1) + (958880139140761/25000000000000 : ℝ)*(sp2) + (1917760093060351/50000000000000 : ℝ)*(sp3) + (297995062061391/20000000000000 : ℝ)*(sp4) + (297995062061391/20000000000000 : ℝ)*(f.failure) + (1917760517844961/50000000000000 : ℝ)*(f.sum) + (15308925181027/5627000000000000000000000000 : ℝ)*base65 + (1013610672135020661/56270000000000000000000000000000 : ℝ)*base68 + (20548878240469339/56270000000000000000000000000000 : ℝ)*base69 + (718118774012029339/56270000000000000000000000000000 : ℝ)*base71 + (11644908757671/2813500000000000000000000000 : ℝ)*base74 + (5749628088869150661/56270000000000000000000000000000 : ℝ)*base76 + (129497113620990661/56270000000000000000000000000000 : ℝ)*base78 + (448990355287399339/56270000000000000000000000000000 : ℝ)*base79 + (11360133393113/5627000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (461479/125000000000000000000 : ℝ)*base90 + (461479/125000000000000000000 : ℝ)*base92 + (461479/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1646_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (651/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1646_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1646_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (651/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1646_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1646_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1646_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (651/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1646_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
