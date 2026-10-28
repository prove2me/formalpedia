-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:57.860753+00:00
-- url     : https://prove2.me/submissions/0924f7cb-bf69-416e-9ded-dbe874e13c35

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
theorem support_rectangle_w1238_s0_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-930897479/5000000000 : ℝ)*x 0 + (6032407241/10000000000 : ℝ)*x 1 + (299530769/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930897479/5000000000 : ℝ)^8431 ≤ (5428224932211/50000000000000 : ℝ)^6383 := by
    have hnat : (930897479 : ℕ)^8431*50000000000000^6383 ≤ 5428224932211^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930897479 5000000000 5428224932211 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6032407241/10000000000 : ℝ)^8431 ≤ (5129329301343/10000000000000 : ℝ)^6383 := by
    have hnat : (6032407241 : ℕ)^8431*10000000000000^6383 ≤ 5129329301343^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032407241 10000000000 5129329301343 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299530769/625000000 : ℝ)^8431 ≤ (295705133667/781250000000 : ℝ)^6383 := by
    have hnat : (299530769 : ℕ)^8431*781250000000^6383 ≤ 295705133667^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299530769 625000000 295705133667 781250000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-930897479/5000000000 : ℝ), (6032407241/10000000000 : ℝ), (299530769/625000000 : ℝ)] ![(5428224932211/50000000000000 : ℝ), (5129329301343/10000000000000 : ℝ), (295705133667/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-930897479/5000000000 : ℝ)|^8431 ≤ (5428224932211/50000000000000 : ℝ)^6383
        have hw : |(-930897479/5000000000 : ℝ)|=(930897479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6032407241/10000000000 : ℝ)|^8431 ≤ (5129329301343/10000000000000 : ℝ)^6383
        have hw : |(6032407241/10000000000 : ℝ)|=(6032407241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299530769/625000000 : ℝ)|^8431 ≤ (295705133667/781250000000 : ℝ)^6383
        have hw : |(299530769/625000000 : ℝ)|=(299530769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s0_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755692419/5000000000 : ℝ)*x 0 + (-160670749/625000000 : ℝ)*x 1 + (2396246127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755692419/5000000000 : ℝ)^8431 ≤ (5690542508889/12500000000000 : ℝ)^6383 := by
    have hnat : (2755692419 : ℕ)^8431*12500000000000^6383 ≤ 5690542508889^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755692419 5000000000 5690542508889 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160670749/625000000 : ℝ)^8431 ≤ (16625403326613/100000000000000 : ℝ)^6383 := by
    have hnat : (160670749 : ℕ)^8431*100000000000000^6383 ≤ 16625403326613^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160670749 625000000 16625403326613 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2396246127/5000000000 : ℝ)^8431 ≤ (37850256587783/100000000000000 : ℝ)^6383 := by
    have hnat : (2396246127 : ℕ)^8431*100000000000000^6383 ≤ 37850256587783^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396246127 5000000000 37850256587783 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755692419/5000000000 : ℝ), (-160670749/625000000 : ℝ), (2396246127/5000000000 : ℝ)] ![(5690542508889/12500000000000 : ℝ), (16625403326613/100000000000000 : ℝ), (37850256587783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755692419/5000000000 : ℝ)|^8431 ≤ (5690542508889/12500000000000 : ℝ)^6383
        have hw : |(2755692419/5000000000 : ℝ)|=(2755692419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-160670749/625000000 : ℝ)|^8431 ≤ (16625403326613/100000000000000 : ℝ)^6383
        have hw : |(-160670749/625000000 : ℝ)|=(160670749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2396246127/5000000000 : ℝ)|^8431 ≤ (37850256587783/100000000000000 : ℝ)^6383
        have hw : |(2396246127/5000000000 : ℝ)|=(2396246127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s0_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (86115387/156250000 : ℝ)*x 0 + (191699693/400000000 : ℝ)*x 1 + (-1285365993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86115387/156250000 : ℝ)^8431 ≤ (45524339307391/100000000000000 : ℝ)^6383 := by
    have hnat : (86115387 : ℕ)^8431*100000000000000^6383 ≤ 45524339307391^6383*156250000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86115387 156250000 45524339307391 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191699693/400000000 : ℝ)^8431 ≤ (7570051465689/20000000000000 : ℝ)^6383 := by
    have hnat : (191699693 : ℕ)^8431*20000000000000^6383 ≤ 7570051465689^6383*400000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191699693 400000000 7570051465689 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285365993/5000000000 : ℝ)^8431 ≤ (8312701671849/50000000000000 : ℝ)^6383 := by
    have hnat : (1285365993 : ℕ)^8431*50000000000000^6383 ≤ 8312701671849^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285365993 5000000000 8312701671849 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86115387/156250000 : ℝ), (191699693/400000000 : ℝ), (-1285365993/5000000000 : ℝ)] ![(45524339307391/100000000000000 : ℝ), (7570051465689/20000000000000 : ℝ), (8312701671849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86115387/156250000 : ℝ)|^8431 ≤ (45524339307391/100000000000000 : ℝ)^6383
        have hw : |(86115387/156250000 : ℝ)|=(86115387/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191699693/400000000 : ℝ)|^8431 ≤ (7570051465689/20000000000000 : ℝ)^6383
        have hw : |(191699693/400000000 : ℝ)|=(191699693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1285365993/5000000000 : ℝ)|^8431 ≤ (8312701671849/50000000000000 : ℝ)^6383
        have hw : |(-1285365993/5000000000 : ℝ)|=(1285365993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s0_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (419333589/1000000000 : ℝ)*x 0 + (3117041687/10000000000 : ℝ)*x 1 + (5630353951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419333589/1000000000 : ℝ)^8431 ≤ (15864524697619/50000000000000 : ℝ)^6383 := by
    have hnat : (419333589 : ℕ)^8431*50000000000000^6383 ≤ 15864524697619^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419333589 1000000000 15864524697619 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117041687/10000000000 : ℝ)^8431 ≤ (5361036816353/25000000000000 : ℝ)^6383 := by
    have hnat : (3117041687 : ℕ)^8431*25000000000000^6383 ≤ 5361036816353^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117041687 10000000000 5361036816353 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5630353951/10000000000 : ℝ)^8431 ≤ (23413401666353/50000000000000 : ℝ)^6383 := by
    have hnat : (5630353951 : ℕ)^8431*50000000000000^6383 ≤ 23413401666353^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630353951 10000000000 23413401666353 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419333589/1000000000 : ℝ), (3117041687/10000000000 : ℝ), (5630353951/10000000000 : ℝ)] ![(15864524697619/50000000000000 : ℝ), (5361036816353/25000000000000 : ℝ), (23413401666353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419333589/1000000000 : ℝ)|^8431 ≤ (15864524697619/50000000000000 : ℝ)^6383
        have hw : |(419333589/1000000000 : ℝ)|=(419333589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117041687/10000000000 : ℝ)|^8431 ≤ (5361036816353/25000000000000 : ℝ)^6383
        have hw : |(3117041687/10000000000 : ℝ)|=(3117041687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5630353951/10000000000 : ℝ)|^8431 ≤ (23413401666353/50000000000000 : ℝ)^6383
        have hw : |(5630353951/10000000000 : ℝ)|=(5630353951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s0_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-933331921/5000000000 : ℝ)*x 0 + (241221271/500000000 : ℝ)*x 1 + (1499836391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933331921/5000000000 : ℝ)^8431 ≤ (1089396631227/10000000000000 : ℝ)^6383 := by
    have hnat : (933331921 : ℕ)^8431*10000000000000^6383 ≤ 1089396631227^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933331921 5000000000 1089396631227 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241221271/500000000 : ℝ)^8431 ≤ (4772966798071/12500000000000 : ℝ)^6383 := by
    have hnat : (241221271 : ℕ)^8431*12500000000000^6383 ≤ 4772966798071^6383*500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241221271 500000000 4772966798071 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499836391/2500000000 : ℝ)^8431 ≤ (50922299293139/100000000000000 : ℝ)^6383 := by
    have hnat : (1499836391 : ℕ)^8431*100000000000000^6383 ≤ 50922299293139^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499836391 2500000000 50922299293139 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933331921/5000000000 : ℝ), (241221271/500000000 : ℝ), (1499836391/2500000000 : ℝ)] ![(1089396631227/10000000000000 : ℝ), (4772966798071/12500000000000 : ℝ), (50922299293139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933331921/5000000000 : ℝ)|^8431 ≤ (1089396631227/10000000000000 : ℝ)^6383
        have hw : |(-933331921/5000000000 : ℝ)|=(933331921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241221271/500000000 : ℝ)|^8431 ≤ (4772966798071/12500000000000 : ℝ)^6383
        have hw : |(241221271/500000000 : ℝ)|=(241221271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1499836391/2500000000 : ℝ)|^8431 ≤ (50922299293139/100000000000000 : ℝ)^6383
        have hw : |(1499836391/2500000000 : ℝ)|=(1499836391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s0_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174038411/10000000000 : ℝ)*x 0 + (-1363876533/10000000000 : ℝ)*x 1 + (2999673901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174038411/10000000000 : ℝ)^8431 ≤ (2617527545913/6250000000000 : ℝ)^6383 := by
    have hnat : (5174038411 : ℕ)^8431*6250000000000^6383 ≤ 2617527545913^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174038411 10000000000 2617527545913 6250000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363876533/10000000000 : ℝ)^8431 ≤ (1799308716749/25000000000000 : ℝ)^6383 := by
    have hnat : (1363876533 : ℕ)^8431*25000000000000^6383 ≤ 1799308716749^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363876533 10000000000 1799308716749 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2999673901/5000000000 : ℝ)^8431 ≤ (6365290548021/12500000000000 : ℝ)^6383 := by
    have hnat : (2999673901 : ℕ)^8431*12500000000000^6383 ≤ 6365290548021^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999673901 5000000000 6365290548021 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174038411/10000000000 : ℝ), (-1363876533/10000000000 : ℝ), (2999673901/5000000000 : ℝ)] ![(2617527545913/6250000000000 : ℝ), (1799308716749/25000000000000 : ℝ), (6365290548021/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174038411/10000000000 : ℝ)|^8431 ≤ (2617527545913/6250000000000 : ℝ)^6383
        have hw : |(5174038411/10000000000 : ℝ)|=(5174038411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1363876533/10000000000 : ℝ)|^8431 ≤ (1799308716749/25000000000000 : ℝ)^6383
        have hw : |(-1363876533/10000000000 : ℝ)|=(1363876533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2999673901/5000000000 : ℝ)|^8431 ≤ (6365290548021/12500000000000 : ℝ)^6383
        have hw : |(2999673901/5000000000 : ℝ)|=(2999673901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s0_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174039277/10000000000 : ℝ)*x 0 + (5999346037/10000000000 : ℝ)*x 1 + (-340969511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174039277/10000000000 : ℝ)^8431 ≤ (10470112498347/25000000000000 : ℝ)^6383 := by
    have hnat : (5174039277 : ℕ)^8431*25000000000000^6383 ≤ 10470112498347^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174039277 10000000000 10470112498347 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5999346037/10000000000 : ℝ)^8431 ≤ (50922304596113/100000000000000 : ℝ)^6383 := by
    have hnat : (5999346037 : ℕ)^8431*100000000000000^6383 ≤ 50922304596113^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5999346037 10000000000 50922304596113 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340969511/2500000000 : ℝ)^8431 ≤ (7197245398961/100000000000000 : ℝ)^6383 := by
    have hnat : (340969511 : ℕ)^8431*100000000000000^6383 ≤ 7197245398961^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340969511 2500000000 7197245398961 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174039277/10000000000 : ℝ), (5999346037/10000000000 : ℝ), (-340969511/2500000000 : ℝ)] ![(10470112498347/25000000000000 : ℝ), (50922304596113/100000000000000 : ℝ), (7197245398961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174039277/10000000000 : ℝ)|^8431 ≤ (10470112498347/25000000000000 : ℝ)^6383
        have hw : |(5174039277/10000000000 : ℝ)|=(5174039277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5999346037/10000000000 : ℝ)|^8431 ≤ (50922304596113/100000000000000 : ℝ)^6383
        have hw : |(5999346037/10000000000 : ℝ)|=(5999346037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-340969511/2500000000 : ℝ)|^8431 ≤ (7197245398961/100000000000000 : ℝ)^6383
        have hw : |(-340969511/2500000000 : ℝ)|=(340969511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s0_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1050801461/2500000000 : ℝ)*x 0 + (5565630503/10000000000 : ℝ)*x 1 + (3184052093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050801461/2500000000 : ℝ)^8431 ≤ (636554594781/2000000000000 : ℝ)^6383 := by
    have hnat : (1050801461 : ℕ)^8431*2000000000000^6383 ≤ 636554594781^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050801461 2500000000 636554594781 2000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5565630503/10000000000 : ℝ)^8431 ≤ (23058554813681/50000000000000 : ℝ)^6383 := by
    have hnat : (5565630503 : ℕ)^8431*50000000000000^6383 ≤ 23058554813681^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5565630503 10000000000 23058554813681 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184052093/10000000000 : ℝ)^8431 ≤ (22055160624883/100000000000000 : ℝ)^6383 := by
    have hnat : (3184052093 : ℕ)^8431*100000000000000^6383 ≤ 22055160624883^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184052093 10000000000 22055160624883 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050801461/2500000000 : ℝ), (5565630503/10000000000 : ℝ), (3184052093/10000000000 : ℝ)] ![(636554594781/2000000000000 : ℝ), (23058554813681/50000000000000 : ℝ), (22055160624883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050801461/2500000000 : ℝ)|^8431 ≤ (636554594781/2000000000000 : ℝ)^6383
        have hw : |(1050801461/2500000000 : ℝ)|=(1050801461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5565630503/10000000000 : ℝ)|^8431 ≤ (23058554813681/50000000000000 : ℝ)^6383
        have hw : |(5565630503/10000000000 : ℝ)|=(5565630503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184052093/10000000000 : ℝ)|^8431 ≤ (22055160624883/100000000000000 : ℝ)^6383
        have hw : |(3184052093/10000000000 : ℝ)|=(3184052093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (401/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27451/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4215/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4215 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4215*1^1024 ≤ 0^1024*1^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4215/1024 : ℝ) ≤ (230141523557294987/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4215 ≤ (230141523557294987/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4215*10000000000000000000^1024 ≤ 230141523557294987^1024*5^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 230141523557294987 10000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (230141523557294987/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4215 := by
      have hnat : (1 : ℕ)^1024*1^4215 ≤ 1^4215*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10230141523557294987/10000000000000000000 : ℝ) ≤ (5027715202868949/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (10230141523557294987/10000000000000000000 : ℝ)^1024 ≤ (5027715202868949/5000000000000000 : ℝ)^4215 := by
      have hnat : (10230141523557294987 : ℕ)^1024*5000000000000000^4215 ≤ 5027715202868949^4215*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10230141523557294987 10000000000000000000 5027715202868949 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027715202868949/5000000000000000 : ℝ)) (X := (10230141523557294987/10000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5230141523557294987/5000000000000000000 : ℝ) ≤ (2527715202868949/2500000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (5230141523557294987/5000000000000000000 : ℝ)^1024 ≤ (2527715202868949/2500000000000000 : ℝ)^4215 := by
      have hnat : (5230141523557294987 : ℕ)^1024*2500000000000000^4215 ≤ 2527715202868949^4215*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5230141523557294987 5000000000000000000 2527715202868949 2500000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527715202868949/2500000000000000 : ℝ)) (X := (5230141523557294987/5000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27715202868949/2000000000000000 : ℝ)*(0 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27715202868949/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(230141523557294987/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27715202868949/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27715202868949/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5027715202868949/5000000000000000 : ℝ) by norm_num, show 1+(230141523557294987/10000000000000000000 : ℝ)+(0 : ℝ)=(10230141523557294987/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(230141523557294987/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27715202868949/2000000000000000 : ℝ)*(2/5 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27715202868949/2000000000000000 : ℝ)*(2/5 : ℝ)=(2527715202868949/2500000000000000 : ℝ) by norm_num, show 1+2*(230141523557294987/10000000000000000000 : ℝ)=(5230141523557294987/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27715202868949/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27715202868949/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27715202868949/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27715202868949/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27715202868949/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27715202868949/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-930897479/5000000000 : ℝ)*X 0 0+(6032407241/10000000000 : ℝ)*X 0 1+(299530769/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755692419/5000000000 : ℝ)*X 1 0+(-160670749/625000000 : ℝ)*X 1 1+(2396246127/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((86115387/156250000 : ℝ)*X 2 0+(191699693/400000000 : ℝ)*X 2 1+(-1285365993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419333589/1000000000 : ℝ)*X 0 0+(3117041687/10000000000 : ℝ)*X 0 1+(5630353951/10000000000 : ℝ)*X 0 2+(419333589/1000000000 : ℝ)*X 1 0+(3117041687/10000000000 : ℝ)*X 1 1+(5630353951/10000000000 : ℝ)*X 1 2+(419333589/1000000000 : ℝ)*X 2 0+(3117041687/10000000000 : ℝ)*X 2 1+(5630353951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-933331921/5000000000 : ℝ)*X 0 0+(241221271/500000000 : ℝ)*X 0 1+(1499836391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174038411/10000000000 : ℝ)*X 1 0+(-1363876533/10000000000 : ℝ)*X 1 1+(2999673901/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174039277/10000000000 : ℝ)*X 2 0+(5999346037/10000000000 : ℝ)*X 2 1+(-340969511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050801461/2500000000 : ℝ)*X 0 0+(5565630503/10000000000 : ℝ)*X 0 1+(3184052093/10000000000 : ℝ)*X 0 2+(1050801461/2500000000 : ℝ)*X 1 0+(5565630503/10000000000 : ℝ)*X 1 1+(3184052093/10000000000 : ℝ)*X 1 2+(1050801461/2500000000 : ℝ)*X 2 0+(5565630503/10000000000 : ℝ)*X 2 1+(3184052093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294558553999279006337181/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71934161/100000000000000 : ℝ)*(base1) + (718221443/50000000000000 : ℝ)*(base19) + (266069419/20000000000000 : ℝ)*(base23) + (95852277/100000000000000 : ℝ)*(base24) + (323512103/100000000000000 : ℝ)*(upper3) + (301100118354959/50000000000000 : ℝ)*(major0) + (301100118354959/50000000000000 : ℝ)*(major1) + (301100118354959/50000000000000 : ℝ)*(major2) + (806511808702287/100000000000000 : ℝ)*(sp0) + (806513498805861/100000000000000 : ℝ)*(sp1) + (403256754524687/50000000000000 : ℝ)*(sp2) + (397882782154767/100000000000000 : ℝ)*(sp3) + (3198480621/100000000000000 : ℝ)*(sp4) + (1243854893/50000000000000 : ℝ)*(sp7) + (79577068359743/20000000000000 : ℝ)*(f.failure) + (403257467624373/50000000000000 : ℝ)*(f.sum) + (59691031968091/50000000000000000000000000000 : ℝ)*base65 + (219149113868091/100000000000000000000000000000 : ℝ)*base67 + (105848040568091/100000000000000000000000000000 : ℝ)*base69 + (232349888068091/100000000000000000000000000000 : ℝ)*base71 + (77200338118091/50000000000000000000000000000 : ℝ)*base73 + (22280579631909/100000000000000000000000000000 : ℝ)*base76 + (572089916668091/100000000000000000000000000000 : ℝ)*base77 + (549228257568091/100000000000000000000000000000 : ℝ)*base79 + (225205846281909/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2420071/1000000000000000000000 : ℝ)*base89 + (2420071/1000000000000000000000 : ℝ)*base91 + (2420071/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (381591198522235059128427/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98305787/100000000000000 : ℝ)*(base1) + (38524983/4000000000000 : ℝ)*(base19) + (27152103/2500000000000 : ℝ)*(base23) + (234486119/100000000000000 : ℝ)*(upper3) + (635505524929141/100000000000000 : ℝ)*(major0) + (635505524929141/100000000000000 : ℝ)*(major1) + (635505524929141/100000000000000 : ℝ)*(major2) + (2339386627/100000000000000 : ℝ)*(sp1) + (408075431/20000000000000 : ℝ)*(sp2) + (207972541/100000000000000 : ℝ)*(sp3) + (425560115590533/50000000000000 : ℝ)*(sp4) + (851116830364077/100000000000000 : ℝ)*(sp5) + (212779251603501/25000000000000 : ℝ)*(sp6) + (104972620876901/25000000000000 : ℝ)*(sp7) + (419890789785933/100000000000000 : ℝ)*(f.failure) + (851120132875279/100000000000000 : ℝ)*(f.sum) + (48501264742809/100000000000000000000000000000 : ℝ)*base65 + (121631294342809/200000000000000000000000000000 : ℝ)*base67 + (771990043257191/200000000000000000000000000000 : ℝ)*base70 + (699388333657191/200000000000000000000000000000 : ℝ)*base72 + (282295287142809/100000000000000000000000000000 : ℝ)*base73 + (458091000857191/200000000000000000000000000000 : ℝ)*base76 + (475525748657191/200000000000000000000000000000 : ℝ)*base78 + (376056666257191/200000000000000000000000000000 : ℝ)*base80 + (263573531557191/100000000000000000000000000000 : ℝ)*base82 + (39010501/5000000000000000000000 : ℝ)*base89 + (39010501/5000000000000000000000 : ℝ)*base91 + (39010501/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1238_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (401/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27451/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1238_s1_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-514874613/2500000000 : ℝ)*x 0 + (2838303919/5000000000 : ℝ)*x 1 + (2510869587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514874613/2500000000 : ℝ)^8431 ≤ (12404529147987/100000000000000 : ℝ)^6383 := by
    have hnat : (514874613 : ℕ)^8431*100000000000000^6383 ≤ 12404529147987^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514874613 2500000000 12404529147987 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2838303919/5000000000 : ℝ)^8431 ≤ (47335585898391/100000000000000 : ℝ)^6383 := by
    have hnat : (2838303919 : ℕ)^8431*100000000000000^6383 ≤ 47335585898391^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838303919 5000000000 47335585898391 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510869587/5000000000 : ℝ)^8431 ≤ (40259884945181/100000000000000 : ℝ)^6383 := by
    have hnat : (2510869587 : ℕ)^8431*100000000000000^6383 ≤ 40259884945181^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510869587 5000000000 40259884945181 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514874613/2500000000 : ℝ), (2838303919/5000000000 : ℝ), (2510869587/5000000000 : ℝ)] ![(12404529147987/100000000000000 : ℝ), (47335585898391/100000000000000 : ℝ), (40259884945181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514874613/2500000000 : ℝ)|^8431 ≤ (12404529147987/100000000000000 : ℝ)^6383
        have hw : |(-514874613/2500000000 : ℝ)|=(514874613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2838303919/5000000000 : ℝ)|^8431 ≤ (47335585898391/100000000000000 : ℝ)^6383
        have hw : |(2838303919/5000000000 : ℝ)|=(2838303919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510869587/5000000000 : ℝ)|^8431 ≤ (40259884945181/100000000000000 : ℝ)^6383
        have hw : |(2510869587/5000000000 : ℝ)|=(2510869587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s1_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1353468671/2500000000 : ℝ)*x 0 + (-48224467/200000000 : ℝ)*x 1 + (1004347867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353468671/2500000000 : ℝ)^8431 ≤ (555793820927/1250000000000 : ℝ)^6383 := by
    have hnat : (1353468671 : ℕ)^8431*1250000000000^6383 ≤ 555793820927^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353468671 2500000000 555793820927 1250000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48224467/200000000 : ℝ)^8431 ≤ (15276607657459/100000000000000 : ℝ)^6383 := by
    have hnat : (48224467 : ℕ)^8431*100000000000000^6383 ≤ 15276607657459^6383*200000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48224467 200000000 15276607657459 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004347867/2000000000 : ℝ)^8431 ≤ (40259886650079/100000000000000 : ℝ)^6383 := by
    have hnat : (1004347867 : ℕ)^8431*100000000000000^6383 ≤ 40259886650079^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004347867 2000000000 40259886650079 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353468671/2500000000 : ℝ), (-48224467/200000000 : ℝ), (1004347867/2000000000 : ℝ)] ![(555793820927/1250000000000 : ℝ), (15276607657459/100000000000000 : ℝ), (40259886650079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353468671/2500000000 : ℝ)|^8431 ≤ (555793820927/1250000000000 : ℝ)^6383
        have hw : |(1353468671/2500000000 : ℝ)|=(1353468671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48224467/200000000 : ℝ)|^8431 ≤ (15276607657459/100000000000000 : ℝ)^6383
        have hw : |(-48224467/200000000 : ℝ)|=(48224467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004347867/2000000000 : ℝ)|^8431 ≤ (40259886650079/100000000000000 : ℝ)^6383
        have hw : |(1004347867/2000000000 : ℝ)|=(1004347867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s1_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706937419/5000000000 : ℝ)*x 0 + (1255434807/2500000000 : ℝ)*x 1 + (-1205611643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706937419/5000000000 : ℝ)^8431 ≤ (44463507344753/100000000000000 : ℝ)^6383 := by
    have hnat : (2706937419 : ℕ)^8431*100000000000000^6383 ≤ 44463507344753^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706937419 5000000000 44463507344753 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255434807/2500000000 : ℝ)^8431 ≤ (4025988551701/10000000000000 : ℝ)^6383 := by
    have hnat : (1255434807 : ℕ)^8431*10000000000000^6383 ≤ 4025988551701^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255434807 2500000000 4025988551701 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205611643/5000000000 : ℝ)^8431 ≤ (15276607121879/100000000000000 : ℝ)^6383 := by
    have hnat : (1205611643 : ℕ)^8431*100000000000000^6383 ≤ 15276607121879^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205611643 5000000000 15276607121879 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706937419/5000000000 : ℝ), (1255434807/2500000000 : ℝ), (-1205611643/5000000000 : ℝ)] ![(44463507344753/100000000000000 : ℝ), (4025988551701/10000000000000 : ℝ), (15276607121879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706937419/5000000000 : ℝ)|^8431 ≤ (44463507344753/100000000000000 : ℝ)^6383
        have hw : |(2706937419/5000000000 : ℝ)|=(2706937419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255434807/2500000000 : ℝ)|^8431 ≤ (4025988551701/10000000000000 : ℝ)^6383
        have hw : |(1255434807/2500000000 : ℝ)|=(1255434807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1205611643/5000000000 : ℝ)|^8431 ≤ (15276607121879/100000000000000 : ℝ)^6383
        have hw : |(-1205611643/5000000000 : ℝ)|=(1205611643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s1_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4309203417/10000000000 : ℝ)*x 0 + (1847364707/5000000000 : ℝ)*x 1 + (2511075651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309203417/10000000000 : ℝ)^8431 ≤ (8223040941861/25000000000000 : ℝ)^6383 := by
    have hnat : (4309203417 : ℕ)^8431*25000000000000^6383 ≤ 8223040941861^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309203417 10000000000 8223040941861 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847364707/5000000000 : ℝ)^8431 ≤ (5368717401921/20000000000000 : ℝ)^6383 := by
    have hnat : (1847364707 : ℕ)^8431*20000000000000^6383 ≤ 5368717401921^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847364707 5000000000 5368717401921 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511075651/5000000000 : ℝ)^8431 ≤ (40264249203633/100000000000000 : ℝ)^6383 := by
    have hnat : (2511075651 : ℕ)^8431*100000000000000^6383 ≤ 40264249203633^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511075651 5000000000 40264249203633 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309203417/10000000000 : ℝ), (1847364707/5000000000 : ℝ), (2511075651/5000000000 : ℝ)] ![(8223040941861/25000000000000 : ℝ), (5368717401921/20000000000000 : ℝ), (40264249203633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309203417/10000000000 : ℝ)|^8431 ≤ (8223040941861/25000000000000 : ℝ)^6383
        have hw : |(4309203417/10000000000 : ℝ)|=(4309203417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1847364707/5000000000 : ℝ)|^8431 ≤ (5368717401921/20000000000000 : ℝ)^6383
        have hw : |(1847364707/5000000000 : ℝ)|=(1847364707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511075651/5000000000 : ℝ)|^8431 ≤ (40264249203633/100000000000000 : ℝ)^6383
        have hw : |(2511075651/5000000000 : ℝ)|=(2511075651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s1_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060180119/10000000000 : ℝ)*x 0 + (2515177577/5000000000 : ℝ)*x 1 + (1133565457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060180119/10000000000 : ℝ)^8431 ≤ (12409952507407/100000000000000 : ℝ)^6383 := by
    have hnat : (2060180119 : ℕ)^8431*100000000000000^6383 ≤ 12409952507407^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060180119 10000000000 12409952507407 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2515177577/5000000000 : ℝ)^8431 ≤ (20175574186929/50000000000000 : ℝ)^6383 := by
    have hnat : (2515177577 : ℕ)^8431*50000000000000^6383 ≤ 20175574186929^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515177577 5000000000 20175574186929 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133565457/2000000000 : ℝ)^8431 ≤ (11809724776189/25000000000000 : ℝ)^6383 := by
    have hnat : (1133565457 : ℕ)^8431*25000000000000^6383 ≤ 11809724776189^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133565457 2000000000 11809724776189 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060180119/10000000000 : ℝ), (2515177577/5000000000 : ℝ), (1133565457/2000000000 : ℝ)] ![(12409952507407/100000000000000 : ℝ), (20175574186929/50000000000000 : ℝ), (11809724776189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060180119/10000000000 : ℝ)|^8431 ≤ (12409952507407/100000000000000 : ℝ)^6383
        have hw : |(-2060180119/10000000000 : ℝ)|=(2060180119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2515177577/5000000000 : ℝ)|^8431 ≤ (20175574186929/50000000000000 : ℝ)^6383
        have hw : |(2515177577/5000000000 : ℝ)|=(2515177577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133565457/2000000000 : ℝ)|^8431 ≤ (11809724776189/25000000000000 : ℝ)^6383
        have hw : |(1133565457/2000000000 : ℝ)|=(1133565457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s1_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (262259667/500000000 : ℝ)*x 0 + (-1765134797/10000000000 : ℝ)*x 1 + (113356549/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262259667/500000000 : ℝ)^8431 ≤ (42642861940813/100000000000000 : ℝ)^6383 := by
    have hnat : (262259667 : ℕ)^8431*100000000000000^6383 ≤ 42642861940813^6383*500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262259667 500000000 42642861940813 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1765134797/10000000000 : ℝ)^8431 ≤ (10118237123843/100000000000000 : ℝ)^6383 := by
    have hnat : (1765134797 : ℕ)^8431*100000000000000^6383 ≤ 10118237123843^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765134797 10000000000 10118237123843 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113356549/200000000 : ℝ)^8431 ≤ (47238900921197/100000000000000 : ℝ)^6383 := by
    have hnat : (113356549 : ℕ)^8431*100000000000000^6383 ≤ 47238900921197^6383*200000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113356549 200000000 47238900921197 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262259667/500000000 : ℝ), (-1765134797/10000000000 : ℝ), (113356549/200000000 : ℝ)] ![(42642861940813/100000000000000 : ℝ), (10118237123843/100000000000000 : ℝ), (47238900921197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262259667/500000000 : ℝ)|^8431 ≤ (42642861940813/100000000000000 : ℝ)^6383
        have hw : |(262259667/500000000 : ℝ)|=(262259667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1765134797/10000000000 : ℝ)|^8431 ≤ (10118237123843/100000000000000 : ℝ)^6383
        have hw : |(-1765134797/10000000000 : ℝ)|=(1765134797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113356549/200000000 : ℝ)|^8431 ≤ (47238900921197/100000000000000 : ℝ)^6383
        have hw : |(113356549/200000000 : ℝ)|=(113356549/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s1_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5245193691/10000000000 : ℝ)*x 0 + (708478527/1250000000 : ℝ)*x 1 + (-353026637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245193691/10000000000 : ℝ)^8431 ≤ (10660716427497/25000000000000 : ℝ)^6383 := by
    have hnat : (5245193691 : ℕ)^8431*25000000000000^6383 ≤ 10660716427497^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245193691 10000000000 10660716427497 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708478527/1250000000 : ℝ)^8431 ≤ (1476215917309/3125000000000 : ℝ)^6383 := by
    have hnat : (708478527 : ℕ)^8431*3125000000000^6383 ≤ 1476215917309^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708478527 1250000000 1476215917309 3125000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353026637/2000000000 : ℝ)^8431 ≤ (10118224918607/100000000000000 : ℝ)^6383 := by
    have hnat : (353026637 : ℕ)^8431*100000000000000^6383 ≤ 10118224918607^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353026637 2000000000 10118224918607 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245193691/10000000000 : ℝ), (708478527/1250000000 : ℝ), (-353026637/2000000000 : ℝ)] ![(10660716427497/25000000000000 : ℝ), (1476215917309/3125000000000 : ℝ), (10118224918607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245193691/10000000000 : ℝ)|^8431 ≤ (10660716427497/25000000000000 : ℝ)^6383
        have hw : |(5245193691/10000000000 : ℝ)|=(5245193691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708478527/1250000000 : ℝ)|^8431 ≤ (1476215917309/3125000000000 : ℝ)^6383
        have hw : |(708478527/1250000000 : ℝ)|=(708478527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353026637/2000000000 : ℝ)|^8431 ≤ (10118224918607/100000000000000 : ℝ)^6383
        have hw : |(-353026637/2000000000 : ℝ)|=(353026637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s1_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155291763/5000000000 : ℝ)*x 0 + (200187497/400000000 : ℝ)*x 1 + (3712526269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155291763/5000000000 : ℝ)^8431 ≤ (32906078837367/100000000000000 : ℝ)^6383 := by
    have hnat : (2155291763 : ℕ)^8431*100000000000000^6383 ≤ 32906078837367^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155291763 5000000000 32906078837367 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200187497/400000000 : ℝ)^8431 ≤ (20039707532711/50000000000000 : ℝ)^6383 := by
    have hnat : (200187497 : ℕ)^8431*50000000000000^6383 ≤ 20039707532711^6383*400000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200187497 400000000 20039707532711 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3712526269/10000000000 : ℝ)^8431 ≤ (27014506079733/100000000000000 : ℝ)^6383 := by
    have hnat : (3712526269 : ℕ)^8431*100000000000000^6383 ≤ 27014506079733^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712526269 10000000000 27014506079733 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155291763/5000000000 : ℝ), (200187497/400000000 : ℝ), (3712526269/10000000000 : ℝ)] ![(32906078837367/100000000000000 : ℝ), (20039707532711/50000000000000 : ℝ), (27014506079733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155291763/5000000000 : ℝ)|^8431 ≤ (32906078837367/100000000000000 : ℝ)^6383
        have hw : |(2155291763/5000000000 : ℝ)|=(2155291763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200187497/400000000 : ℝ)|^8431 ≤ (20039707532711/50000000000000 : ℝ)^6383
        have hw : |(200187497/400000000 : ℝ)|=(200187497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3712526269/10000000000 : ℝ)|^8431 ≤ (27014506079733/100000000000000 : ℝ)^6383
        have hw : |(3712526269/10000000000 : ℝ)|=(3712526269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27451/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (617/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1251/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27451/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27451/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27451/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27451/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27451/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27451/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (401/50000 : ℝ) ^ (4215/1024 : ℝ) ≤ (118061858631/50000000000000000000 : ℝ) := by
    have hpowers : (401/50000 : ℝ)^4215 ≤ (118061858631/50000000000000000000 : ℝ)^1024 := by
      have hnat : (401 : ℕ)^4215*50000000000000000000^1024 ≤ 118061858631^1024*50000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401 50000 118061858631 50000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (401/50000 : ℝ)) (X := (118061858631/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27451/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (488637729871164473/100000000000000000000 : ℝ) := by
    have hpowers : (27451/100000 : ℝ)^4215 ≤ (488637729871164473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27451 : ℕ)^4215*100000000000000000000^1024 ≤ 488637729871164473^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27451 100000 488637729871164473 100000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27451/100000 : ℝ)) (X := (488637729871164473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000118061858631/25000000000000000000 : ℝ) ≤ (2500000002868217/2500000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (25000000118061858631/25000000000000000000 : ℝ)^1024 ≤ (2500000002868217/2500000000000000 : ℝ)^4215 := by
      have hnat : (25000000118061858631 : ℕ)^1024*2500000000000000^4215 ≤ 2500000002868217^4215*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000118061858631 25000000000000000000 2500000002868217 2500000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000002868217/2500000000000000 : ℝ)) (X := (25000000118061858631/25000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20097727593198976347/20000000000000000000 : ℝ) ≤ (10011849167804523/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (20097727593198976347/20000000000000000000 : ℝ)^1024 ≤ (10011849167804523/10000000000000000 : ℝ)^4215 := by
      have hnat : (20097727593198976347 : ℕ)^1024*10000000000000000^4215 ≤ 10011849167804523^4215*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20097727593198976347 20000000000000000000 10011849167804523 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011849167804523/10000000000000000 : ℝ)) (X := (20097727593198976347/20000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50488637729871164473/50000000000000000000 : ℝ) ≤ (5011849162068089/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50488637729871164473/50000000000000000000 : ℝ)^1024 ≤ (5011849162068089/5000000000000000 : ℝ)^4215 := by
      have hnat : (50488637729871164473 : ℕ)^1024*5000000000000000^4215 ≤ 5011849162068089^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50488637729871164473 50000000000000000000 5011849162068089 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011849162068089/5000000000000000 : ℝ)) (X := (50488637729871164473/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(118061858631/50000000000000000000 : ℝ) ≤ ((33308874282373060589/33311250000000000000 : ℝ)+2*(2369831266331/532980000000000 : ℝ)*(401/50000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (33308874282373060589/33311250000000000000 : ℝ)+2*(2369831266331/532980000000000 : ℝ)*(401/50000 : ℝ)=(2500000002868217/2500000000000000 : ℝ) by norm_num, show 1+2*(118061858631/50000000000000000000 : ℝ)=(25000000118061858631/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(488637729871164473/100000000000000000000 : ℝ)+(118061858631/50000000000000000000 : ℝ) ≤ ((33308874282373060589/33311250000000000000 : ℝ)+(2369831266331/532980000000000 : ℝ)*((27451/100000 : ℝ)+(401/50000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (33308874282373060589/33311250000000000000 : ℝ)+(2369831266331/532980000000000 : ℝ)*((27451/100000 : ℝ)+(401/50000 : ℝ))=(10011849167804523/10000000000000000 : ℝ) by norm_num, show 1+(488637729871164473/100000000000000000000 : ℝ)+(118061858631/50000000000000000000 : ℝ)=(20097727593198976347/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(488637729871164473/100000000000000000000 : ℝ) ≤ ((33308874282373060589/33311250000000000000 : ℝ)+2*(2369831266331/532980000000000 : ℝ)*(27451/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (33308874282373060589/33311250000000000000 : ℝ)+2*(2369831266331/532980000000000 : ℝ)*(27451/100000 : ℝ)=(5011849162068089/5000000000000000 : ℝ) by norm_num, show 1+2*(488637729871164473/100000000000000000000 : ℝ)=(50488637729871164473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33308874282373060589/33311250000000000000 : ℝ)*(X 1 0+X 2 0)+(2369831266331/532980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (401/50000 : ℝ)) (hi := (27451/100000 : ℝ)) (c := (33308874282373060589/33311250000000000000 : ℝ)) (alpha := (2369831266331/532980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33308874282373060589/33311250000000000000 : ℝ)*(X 0 1+X 2 1)+(2369831266331/532980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (401/50000 : ℝ)) (hi := (27451/100000 : ℝ)) (c := (33308874282373060589/33311250000000000000 : ℝ)) (alpha := (2369831266331/532980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33308874282373060589/33311250000000000000 : ℝ)*(X 0 2+X 1 2)+(2369831266331/532980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (401/50000 : ℝ)) (hi := (27451/100000 : ℝ)) (c := (33308874282373060589/33311250000000000000 : ℝ)) (alpha := (2369831266331/532980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-514874613/2500000000 : ℝ)*X 0 0+(2838303919/5000000000 : ℝ)*X 0 1+(2510869587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1353468671/2500000000 : ℝ)*X 1 0+(-48224467/200000000 : ℝ)*X 1 1+(1004347867/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706937419/5000000000 : ℝ)*X 2 0+(1255434807/2500000000 : ℝ)*X 2 1+(-1205611643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4309203417/10000000000 : ℝ)*X 0 0+(1847364707/5000000000 : ℝ)*X 0 1+(2511075651/5000000000 : ℝ)*X 0 2+(4309203417/10000000000 : ℝ)*X 1 0+(1847364707/5000000000 : ℝ)*X 1 1+(2511075651/5000000000 : ℝ)*X 1 2+(4309203417/10000000000 : ℝ)*X 2 0+(1847364707/5000000000 : ℝ)*X 2 1+(2511075651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2060180119/10000000000 : ℝ)*X 0 0+(2515177577/5000000000 : ℝ)*X 0 1+(1133565457/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262259667/500000000 : ℝ)*X 1 0+(-1765134797/10000000000 : ℝ)*X 1 1+(113356549/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245193691/10000000000 : ℝ)*X 2 0+(708478527/1250000000 : ℝ)*X 2 1+(-353026637/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155291763/5000000000 : ℝ)*X 0 0+(200187497/400000000 : ℝ)*X 0 1+(3712526269/10000000000 : ℝ)*X 0 2+(2155291763/5000000000 : ℝ)*X 1 0+(200187497/400000000 : ℝ)*X 1 1+(3712526269/10000000000 : ℝ)*X 1 2+(2155291763/5000000000 : ℝ)*X 2 0+(200187497/400000000 : ℝ)*X 2 1+(3712526269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1652193225527130385063924241/277593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15697751/25000000000000 : ℝ)*(base1) + (331388381/25000000000000 : ℝ)*(base19) + (1368990763/100000000000000 : ℝ)*(base23) + (71331561/50000000000000 : ℝ)*(upper3) + (177855361/100000000000000 : ℝ)*(upper5) + (1140193429215031/100000000000000 : ℝ)*(major0) + (1140193429215031/100000000000000 : ℝ)*(major1) + (1140193429215031/100000000000000 : ℝ)*(major2) + (763515488450513/50000000000000 : ℝ)*(sp0) + (1527037486632417/100000000000000 : ℝ)*(sp1) + (763518721597589/50000000000000 : ℝ)*(sp2) + (37667194761899/5000000000000 : ℝ)*(sp3) + (98725949/1250000000000 : ℝ)*(sp4) + (3889820507/100000000000000 : ℝ)*(sp7) + (188336961962373/25000000000000 : ℝ)*(f.failure) + (1527038812185941/100000000000000 : ℝ)*(f.sum) + (70271102638871/26649000000000000000000000000 : ℝ)*base65 + (9380122917940450759/3331125000000000000000000000000000 : ℝ)*base67 + (1111976138334049241/3331125000000000000000000000000000 : ℝ)*base70 + (13029453943360075759/3331125000000000000000000000000000 : ℝ)*base71 + (12401049421657/3331125000000000000000000000 : ℝ)*base73 + (14302628346143575759/3331125000000000000000000000000000 : ℝ)*base75 + (20734013169052075759/3331125000000000000000000000000000 : ℝ)*base77 + (25949441413904950759/3331125000000000000000000000000000 : ℝ)*base79 + (23433518055973/13324500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (374819/1250000000000000000000 : ℝ)*base90 + (374819/1250000000000000000000 : ℝ)*base92 + (374819/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (202855908940996754643947819/30843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2063739641/100000000000000 : ℝ)*(base19) + (626981033/25000000000000 : ℝ)*(base23) + (41038647/50000000000000 : ℝ)*(upper2) + (62156771/20000000000000 : ℝ)*(upper3) + (9699041/6250000000000 : ℝ)*(upper5) + (585648216407787/50000000000000 : ℝ)*(major0) + (585648216407787/50000000000000 : ℝ)*(major1) + (585648216407787/50000000000000 : ℝ)*(major2) + (4714118801/50000000000000 : ℝ)*(sp1) + (15110269033/100000000000000 : ℝ)*(sp2) + (784347221300179/50000000000000 : ℝ)*(sp4) + (784341475311557/50000000000000 : ℝ)*(sp5) + (1568676824407193/100000000000000 : ℝ)*(sp6) + (386949101900581/50000000000000 : ℝ)*(sp7) + (386949101900581/50000000000000 : ℝ)*(f.failure) + (784347221300179/50000000000000 : ℝ)*(f.sum) + (2256662327977/555187500000000000000000000 : ℝ)*base66 + (5590241269622864681/555187500000000000000000000000000 : ℝ)*base67 + (2677805578512989681/555187500000000000000000000000000 : ℝ)*base69 + (3627679685290739681/555187500000000000000000000000000 : ℝ)*base71 + (21315618934919/4441500000000000000000000000 : ℝ)*base74 + (8007613384449239681/555187500000000000000000000000000 : ℝ)*base75 + (2461573582179052181/555187500000000000000000000000000 : ℝ)*base77 + (1936586154145364681/555187500000000000000000000000000 : ℝ)*base79 + (35071264277107/8883000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1531357/2500000000000000000000 : ℝ)*base89 + (1531357/2500000000000000000000 : ℝ)*base91 + (1531357/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1238_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27451/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (617/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1251/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1238_s2_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107738991/10000000000 : ℝ)*x 0 + (5493478407/10000000000 : ℝ)*x 1 + (5174107229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107738991/10000000000 : ℝ)^8431 ≤ (199839785389/1562500000000 : ℝ)^6383 := by
    have hnat : (2107738991 : ℕ)^8431*1562500000000^6383 ≤ 199839785389^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107738991 10000000000 199839785389 1562500000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493478407/10000000000 : ℝ)^8431 ≤ (45329077227257/100000000000000 : ℝ)^6383 := by
    have hnat : (5493478407 : ℕ)^8431*100000000000000^6383 ≤ 45329077227257^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493478407 10000000000 45329077227257 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174107229/10000000000 : ℝ)^8431 ≤ (41881176499081/100000000000000 : ℝ)^6383 := by
    have hnat : (5174107229 : ℕ)^8431*100000000000000^6383 ≤ 41881176499081^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174107229 10000000000 41881176499081 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107738991/10000000000 : ℝ), (5493478407/10000000000 : ℝ), (5174107229/10000000000 : ℝ)] ![(199839785389/1562500000000 : ℝ), (45329077227257/100000000000000 : ℝ), (41881176499081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107738991/10000000000 : ℝ)|^8431 ≤ (199839785389/1562500000000 : ℝ)^6383
        have hw : |(-2107738991/10000000000 : ℝ)|=(2107738991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493478407/10000000000 : ℝ)|^8431 ≤ (45329077227257/100000000000000 : ℝ)^6383
        have hw : |(5493478407/10000000000 : ℝ)|=(5493478407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174107229/10000000000 : ℝ)|^8431 ≤ (41881176499081/100000000000000 : ℝ)^6383
        have hw : |(5174107229/10000000000 : ℝ)|=(5174107229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s2_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369850329/10000000000 : ℝ)*x 0 + (-2273194253/10000000000 : ℝ)*x 1 + (517410721/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369850329/10000000000 : ℝ)^8431 ≤ (43986553565233/100000000000000 : ℝ)^6383 := by
    have hnat : (5369850329 : ℕ)^8431*100000000000000^6383 ≤ 43986553565233^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369850329 10000000000 43986553565233 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273194253/10000000000 : ℝ)^8431 ≤ (1413227012017/10000000000000 : ℝ)^6383 := by
    have hnat : (2273194253 : ℕ)^8431*10000000000000^6383 ≤ 1413227012017^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273194253 10000000000 1413227012017 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517410721/1000000000 : ℝ)^8431 ≤ (41881176295943/100000000000000 : ℝ)^6383 := by
    have hnat : (517410721 : ℕ)^8431*100000000000000^6383 ≤ 41881176295943^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517410721 1000000000 41881176295943 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369850329/10000000000 : ℝ), (-2273194253/10000000000 : ℝ), (517410721/1000000000 : ℝ)] ![(43986553565233/100000000000000 : ℝ), (1413227012017/10000000000000 : ℝ), (41881176295943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369850329/10000000000 : ℝ)|^8431 ≤ (43986553565233/100000000000000 : ℝ)^6383
        have hw : |(5369850329/10000000000 : ℝ)|=(5369850329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273194253/10000000000 : ℝ)|^8431 ≤ (1413227012017/10000000000000 : ℝ)^6383
        have hw : |(-2273194253/10000000000 : ℝ)|=(2273194253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517410721/1000000000 : ℝ)|^8431 ≤ (41881176295943/100000000000000 : ℝ)^6383
        have hw : |(517410721/1000000000 : ℝ)|=(517410721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s2_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073970033/2000000000 : ℝ)*x 0 + (5174107347/10000000000 : ℝ)*x 1 + (-2273194291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073970033/2000000000 : ℝ)^8431 ≤ (1374579743463/3125000000000 : ℝ)^6383 := by
    have hnat : (1073970033 : ℕ)^8431*3125000000000^6383 ≤ 1374579743463^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073970033 2000000000 1374579743463 3125000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174107347/10000000000 : ℝ)^8431 ≤ (1675247110427/4000000000000 : ℝ)^6383 := by
    have hnat : (5174107347 : ℕ)^8431*4000000000000^6383 ≤ 1675247110427^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174107347 10000000000 1675247110427 4000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273194291/10000000000 : ℝ)^8431 ≤ (3533067608053/25000000000000 : ℝ)^6383 := by
    have hnat : (2273194291 : ℕ)^8431*25000000000000^6383 ≤ 3533067608053^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273194291 10000000000 3533067608053 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073970033/2000000000 : ℝ), (5174107347/10000000000 : ℝ), (-2273194291/10000000000 : ℝ)] ![(1374579743463/3125000000000 : ℝ), (1675247110427/4000000000000 : ℝ), (3533067608053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073970033/2000000000 : ℝ)|^8431 ≤ (1374579743463/3125000000000 : ℝ)^6383
        have hw : |(1073970033/2000000000 : ℝ)|=(1073970033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174107347/10000000000 : ℝ)|^8431 ≤ (1675247110427/4000000000000 : ℝ)^6383
        have hw : |(5174107347/10000000000 : ℝ)|=(5174107347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273194291/10000000000 : ℝ)|^8431 ≤ (3533067608053/25000000000000 : ℝ)^6383
        have hw : |(-2273194291/10000000000 : ℝ)|=(2273194291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s2_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271407329/625000000 : ℝ)*x 0 + (4030528947/10000000000 : ℝ)*x 1 + (292368477/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271407329/625000000 : ℝ)^8431 ≤ (4153556515783/12500000000000 : ℝ)^6383 := by
    have hnat : (271407329 : ℕ)^8431*12500000000000^6383 ≤ 4153556515783^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271407329 625000000 4153556515783 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030528947/10000000000 : ℝ)^8431 ≤ (12044854399/40000000000 : ℝ)^6383 := by
    have hnat : (4030528947 : ℕ)^8431*40000000000^6383 ≤ 12044854399^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030528947 10000000000 12044854399 40000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292368477/625000000 : ℝ)^8431 ≤ (7331882370877/20000000000000 : ℝ)^6383 := by
    have hnat : (292368477 : ℕ)^8431*20000000000000^6383 ≤ 7331882370877^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292368477 625000000 7331882370877 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271407329/625000000 : ℝ), (4030528947/10000000000 : ℝ), (292368477/625000000 : ℝ)] ![(4153556515783/12500000000000 : ℝ), (12044854399/40000000000 : ℝ), (7331882370877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271407329/625000000 : ℝ)|^8431 ≤ (4153556515783/12500000000000 : ℝ)^6383
        have hw : |(271407329/625000000 : ℝ)|=(271407329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030528947/10000000000 : ℝ)|^8431 ≤ (12044854399/40000000000 : ℝ)^6383
        have hw : |(4030528947/10000000000 : ℝ)|=(4030528947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(292368477/625000000 : ℝ)|^8431 ≤ (7331882370877/20000000000000 : ℝ)^6383
        have hw : |(292368477/625000000 : ℝ)|=(292368477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s2_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053909127/5000000000 : ℝ)*x 0 + (2588083041/5000000000 : ℝ)*x 1 + (5491400197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053909127/5000000000 : ℝ)^8431 ≤ (2558076311111/20000000000000 : ℝ)^6383 := by
    have hnat : (1053909127 : ℕ)^8431*20000000000000^6383 ≤ 2558076311111^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053909127 5000000000 2558076311111 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588083041/5000000000 : ℝ)^8431 ≤ (41903190082963/100000000000000 : ℝ)^6383 := by
    have hnat : (2588083041 : ℕ)^8431*100000000000000^6383 ≤ 41903190082963^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588083041 5000000000 41903190082963 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491400197/10000000000 : ℝ)^8431 ≤ (9061285669031/20000000000000 : ℝ)^6383 := by
    have hnat : (5491400197 : ℕ)^8431*20000000000000^6383 ≤ 9061285669031^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491400197 10000000000 9061285669031 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053909127/5000000000 : ℝ), (2588083041/5000000000 : ℝ), (5491400197/10000000000 : ℝ)] ![(2558076311111/20000000000000 : ℝ), (41903190082963/100000000000000 : ℝ), (9061285669031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053909127/5000000000 : ℝ)|^8431 ≤ (2558076311111/20000000000000 : ℝ)^6383
        have hw : |(-1053909127/5000000000 : ℝ)|=(1053909127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588083041/5000000000 : ℝ)|^8431 ≤ (41903190082963/100000000000000 : ℝ)^6383
        have hw : |(2588083041/5000000000 : ℝ)|=(2588083041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491400197/10000000000 : ℝ)|^8431 ≤ (9061285669031/20000000000000 : ℝ)^6383
        have hw : |(5491400197/10000000000 : ℝ)|=(5491400197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s2_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132207793/250000000 : ℝ)*x 0 + (-977950529/5000000000 : ℝ)*x 1 + (68642503/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132207793/250000000 : ℝ)^8431 ≤ (21553246663947/50000000000000 : ℝ)^6383 := by
    have hnat : (132207793 : ℕ)^8431*50000000000000^6383 ≤ 21553246663947^6383*250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132207793 250000000 21553246663947 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977950529/5000000000 : ℝ)^8431 ≤ (11587077835167/100000000000000 : ℝ)^6383 := by
    have hnat : (977950529 : ℕ)^8431*100000000000000^6383 ≤ 11587077835167^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977950529 5000000000 11587077835167 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68642503/125000000 : ℝ)^8431 ≤ (5663303601719/12500000000000 : ℝ)^6383 := by
    have hnat : (68642503 : ℕ)^8431*12500000000000^6383 ≤ 5663303601719^6383*125000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68642503 125000000 5663303601719 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132207793/250000000 : ℝ), (-977950529/5000000000 : ℝ), (68642503/125000000 : ℝ)] ![(21553246663947/50000000000000 : ℝ), (11587077835167/100000000000000 : ℝ), (5663303601719/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132207793/250000000 : ℝ)|^8431 ≤ (21553246663947/50000000000000 : ℝ)^6383
        have hw : |(132207793/250000000 : ℝ)|=(132207793/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977950529/5000000000 : ℝ)|^8431 ≤ (11587077835167/100000000000000 : ℝ)^6383
        have hw : |(-977950529/5000000000 : ℝ)|=(977950529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68642503/125000000 : ℝ)|^8431 ≤ (5663303601719/12500000000000 : ℝ)^6383
        have hw : |(68642503/125000000 : ℝ)|=(68642503/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s2_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288311891/10000000000 : ℝ)*x 0 + (1098280063/2000000000 : ℝ)*x 1 + (-24448759/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288311891/10000000000 : ℝ)^8431 ≤ (43106495168989/100000000000000 : ℝ)^6383 := by
    have hnat : (5288311891 : ℕ)^8431*100000000000000^6383 ≤ 43106495168989^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288311891 10000000000 43106495168989 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098280063/2000000000 : ℝ)^8431 ≤ (1415825925971/3125000000000 : ℝ)^6383 := by
    have hnat : (1098280063 : ℕ)^8431*3125000000000^6383 ≤ 1415825925971^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098280063 2000000000 1415825925971 3125000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24448759/125000000 : ℝ)^8431 ≤ (181048049849/1562500000000 : ℝ)^6383 := by
    have hnat : (24448759 : ℕ)^8431*1562500000000^6383 ≤ 181048049849^6383*125000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24448759 125000000 181048049849 1562500000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288311891/10000000000 : ℝ), (1098280063/2000000000 : ℝ), (-24448759/125000000 : ℝ)] ![(43106495168989/100000000000000 : ℝ), (1415825925971/3125000000000 : ℝ), (181048049849/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288311891/10000000000 : ℝ)|^8431 ≤ (43106495168989/100000000000000 : ℝ)^6383
        have hw : |(5288311891/10000000000 : ℝ)|=(5288311891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098280063/2000000000 : ℝ)|^8431 ≤ (1415825925971/3125000000000 : ℝ)^6383
        have hw : |(1098280063/2000000000 : ℝ)|=(1098280063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24448759/125000000 : ℝ)|^8431 ≤ (181048049849/1562500000000 : ℝ)^6383
        have hw : |(-24448759/125000000 : ℝ)|=(24448759/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s2_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434267739/1000000000 : ℝ)*x 0 + (4673722551/10000000000 : ℝ)*x 1 + (4034740971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434267739/1000000000 : ℝ)^8431 ≤ (33230070531319/100000000000000 : ℝ)^6383 := by
    have hnat : (434267739 : ℕ)^8431*100000000000000^6383 ≤ 33230070531319^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434267739 1000000000 33230070531319 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4673722551/10000000000 : ℝ)^8431 ≤ (9154055447441/25000000000000 : ℝ)^6383 := by
    have hnat : (4673722551 : ℕ)^8431*25000000000000^6383 ≤ 9154055447441^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673722551 10000000000 9154055447441 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034740971/10000000000 : ℝ)^8431 ≤ (30153707659427/100000000000000 : ℝ)^6383 := by
    have hnat : (4034740971 : ℕ)^8431*100000000000000^6383 ≤ 30153707659427^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034740971 10000000000 30153707659427 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434267739/1000000000 : ℝ), (4673722551/10000000000 : ℝ), (4034740971/10000000000 : ℝ)] ![(33230070531319/100000000000000 : ℝ), (9154055447441/25000000000000 : ℝ), (30153707659427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434267739/1000000000 : ℝ)|^8431 ≤ (33230070531319/100000000000000 : ℝ)^6383
        have hw : |(434267739/1000000000 : ℝ)|=(434267739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4673722551/10000000000 : ℝ)|^8431 ≤ (9154055447441/25000000000000 : ℝ)^6383
        have hw : |(4673722551/10000000000 : ℝ)|=(4673722551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034740971/10000000000 : ℝ)|^8431 ≤ (30153707659427/100000000000000 : ℝ)^6383
        have hw : |(4034740971/10000000000 : ℝ)|=(4034740971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1251/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (617/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9483/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1251/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (617/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1251/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (617/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1251/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (617/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1251/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (617/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1251/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (617/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1251/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (617/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (617/10000 : ℝ) ^ (4215/1024 : ℝ) ≤ (1048476162192041/100000000000000000000 : ℝ) := by
    have hpowers : (617/10000 : ℝ)^4215 ≤ (1048476162192041/100000000000000000000 : ℝ)^1024 := by
      have hnat : (617 : ℕ)^4215*100000000000000000000^1024 ≤ 1048476162192041^1024*10000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        617 10000 1048476162192041 100000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (617/10000 : ℝ)) (X := (1048476162192041/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1251/6250 : ℝ) ^ (4215/1024 : ℝ) ≤ (2662879812431987/2000000000000000000 : ℝ) := by
    have hpowers : (1251/6250 : ℝ)^4215 ≤ (2662879812431987/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1251 : ℕ)^4215*2000000000000000000^1024 ≤ 2662879812431987^1024*6250^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251 6250 2662879812431987 2000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1251/6250 : ℝ)) (X := (2662879812431987/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001048476162192041/50000000000000000000 : ℝ) ≤ (10000050943348427/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50001048476162192041/50000000000000000000 : ℝ)^1024 ≤ (10000050943348427/10000000000000000 : ℝ)^4215 := by
      have hnat : (50001048476162192041 : ℕ)^1024*10000000000000000^4215 ≤ 10000050943348427^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001048476162192041 50000000000000000000 10000050943348427 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050943348427/10000000000000000 : ℝ)) (X := (50001048476162192041/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100134192466783791391/100000000000000000000 : ℝ) ≤ (10003258442248853/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (100134192466783791391/100000000000000000000 : ℝ)^1024 ≤ (10003258442248853/10000000000000000 : ℝ)^4215 := by
      have hnat : (100134192466783791391 : ℕ)^1024*10000000000000000^4215 ≤ 10003258442248853^4215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100134192466783791391 100000000000000000000 10003258442248853 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003258442248853/10000000000000000 : ℝ)) (X := (100134192466783791391/100000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1002662879812431987/1000000000000000000 : ℝ) ≤ (10006465941149279/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (1002662879812431987/1000000000000000000 : ℝ)^1024 ≤ (10006465941149279/10000000000000000 : ℝ)^4215 := by
      have hnat : (1002662879812431987 : ℕ)^1024*10000000000000000^4215 ≤ 10006465941149279^4215*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1002662879812431987 1000000000000000000 10006465941149279 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006465941149279/10000000000000000 : ℝ)) (X := (1002662879812431987/1000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1048476162192041/100000000000000000000 : ℝ) ≤ ((69210562412585531701/69230000000000000000 : ℝ)+2*(1603749450213/692300000000000 : ℝ)*(617/10000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (69210562412585531701/69230000000000000000 : ℝ)+2*(1603749450213/692300000000000 : ℝ)*(617/10000 : ℝ)=(10000050943348427/10000000000000000 : ℝ) by norm_num, show 1+2*(1048476162192041/100000000000000000000 : ℝ)=(50001048476162192041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2662879812431987/2000000000000000000 : ℝ)+(1048476162192041/100000000000000000000 : ℝ) ≤ ((69210562412585531701/69230000000000000000 : ℝ)+(1603749450213/692300000000000 : ℝ)*((1251/6250 : ℝ)+(617/10000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (69210562412585531701/69230000000000000000 : ℝ)+(1603749450213/692300000000000 : ℝ)*((1251/6250 : ℝ)+(617/10000 : ℝ))=(10003258442248853/10000000000000000 : ℝ) by norm_num, show 1+(2662879812431987/2000000000000000000 : ℝ)+(1048476162192041/100000000000000000000 : ℝ)=(100134192466783791391/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2662879812431987/2000000000000000000 : ℝ) ≤ ((69210562412585531701/69230000000000000000 : ℝ)+2*(1603749450213/692300000000000 : ℝ)*(1251/6250 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (69210562412585531701/69230000000000000000 : ℝ)+2*(1603749450213/692300000000000 : ℝ)*(1251/6250 : ℝ)=(10006465941149279/10000000000000000 : ℝ) by norm_num, show 1+2*(2662879812431987/2000000000000000000 : ℝ)=(1002662879812431987/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69210562412585531701/69230000000000000000 : ℝ)*(X 1 0+X 2 0)+(1603749450213/692300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (617/10000 : ℝ)) (hi := (1251/6250 : ℝ)) (c := (69210562412585531701/69230000000000000000 : ℝ)) (alpha := (1603749450213/692300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69210562412585531701/69230000000000000000 : ℝ)*(X 0 1+X 2 1)+(1603749450213/692300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (617/10000 : ℝ)) (hi := (1251/6250 : ℝ)) (c := (69210562412585531701/69230000000000000000 : ℝ)) (alpha := (1603749450213/692300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69210562412585531701/69230000000000000000 : ℝ)*(X 0 2+X 1 2)+(1603749450213/692300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (617/10000 : ℝ)) (hi := (1251/6250 : ℝ)) (c := (69210562412585531701/69230000000000000000 : ℝ)) (alpha := (1603749450213/692300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2107738991/10000000000 : ℝ)*X 0 0+(5493478407/10000000000 : ℝ)*X 0 1+(5174107229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369850329/10000000000 : ℝ)*X 1 0+(-2273194253/10000000000 : ℝ)*X 1 1+(517410721/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073970033/2000000000 : ℝ)*X 2 0+(5174107347/10000000000 : ℝ)*X 2 1+(-2273194291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271407329/625000000 : ℝ)*X 0 0+(4030528947/10000000000 : ℝ)*X 0 1+(292368477/625000000 : ℝ)*X 0 2+(271407329/625000000 : ℝ)*X 1 0+(4030528947/10000000000 : ℝ)*X 1 1+(292368477/625000000 : ℝ)*X 1 2+(271407329/625000000 : ℝ)*X 2 0+(4030528947/10000000000 : ℝ)*X 2 1+(292368477/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1053909127/5000000000 : ℝ)*X 0 0+(2588083041/5000000000 : ℝ)*X 0 1+(5491400197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132207793/250000000 : ℝ)*X 1 0+(-977950529/5000000000 : ℝ)*X 1 1+(68642503/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288311891/10000000000 : ℝ)*X 2 0+(1098280063/2000000000 : ℝ)*X 2 1+(-24448759/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434267739/1000000000 : ℝ)*X 0 0+(4673722551/10000000000 : ℝ)*X 0 1+(4034740971/10000000000 : ℝ)*X 0 2+(434267739/1000000000 : ℝ)*X 1 0+(4673722551/10000000000 : ℝ)*X 1 1+(4034740971/10000000000 : ℝ)*X 1 2+(434267739/1000000000 : ℝ)*X 2 0+(4673722551/10000000000 : ℝ)*X 2 1+(4034740971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19371515701253696781050566887/3461500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (532840921/50000000000000 : ℝ)*(base19) + (446902937/50000000000000 : ℝ)*(base23) + (8188711/20000000000000 : ℝ)*(lower2) + (90078043/50000000000000 : ℝ)*(upper3) + (6951971/10000000000000 : ℝ)*(upper5) + (2337953476773671/100000000000000 : ℝ)*(major0) + (2337953476773671/100000000000000 : ℝ)*(major1) + (2337953476773671/100000000000000 : ℝ)*(major2) + (3131165350173747/100000000000000 : ℝ)*(sp0) + (3131174627655643/100000000000000 : ℝ)*(sp1) + (782793699882903/25000000000000 : ℝ)*(sp2) + (772362415187517/50000000000000 : ℝ)*(sp3) + (5171581869/50000000000000 : ℝ)*(sp4) + (312164611/5000000000000 : ℝ)*(sp7) + (1544731073667253/100000000000000 : ℝ)*(f.failure) + (626235138667497/20000000000000 : ℝ)*(f.sum) + (105092829567491/17307500000000000000000000000 : ℝ)*base66 + (25677653239915944371/6923000000000000000000000000000000 : ℝ)*base67 + (40485309211653944371/6923000000000000000000000000000000 : ℝ)*base69 + (22142275414635944371/6923000000000000000000000000000000 : ℝ)*base71 + (10188757584281/17307500000000000000000000000 : ℝ)*base74 + (49981501213390944371/6923000000000000000000000000000000 : ℝ)*base75 + (57878323840023055629/6923000000000000000000000000000000 : ℝ)*base78 + (55717704181021055629/6923000000000000000000000000000000 : ℝ)*base80 + (28490997638083/34615000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (33501459/5000000000000000000000 : ℝ)*base90 + (33501459/5000000000000000000000 : ℝ)*base92 + (33501459/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4204027804816462955152199301/494500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (523480171/25000000000000 : ℝ)*(base19) + (1164577183/50000000000000 : ℝ)*(base23) + (725393/3125000000000 : ℝ)*(upper2) + (276988287/100000000000000 : ℝ)*(upper3) + (168342783/100000000000000 : ℝ)*(upper5) + (2368617791511069/100000000000000 : ℝ)*(major0) + (2368617791511069/100000000000000 : ℝ)*(major1) + (2368617791511069/100000000000000 : ℝ)*(major2) + (21453903059/100000000000000 : ℝ)*(sp1) + (27210919579/100000000000000 : ℝ)*(sp2) + (317224372023273/10000000000000 : ℝ)*(sp4) + (1586110086204493/50000000000000 : ℝ)*(sp5) + (49565846564981/1562500000000 : ℝ)*(sp6) + (1564991579403637/100000000000000 : ℝ)*(sp7) + (1564991579403637/100000000000000 : ℝ)*(f.failure) + (317224372023273/10000000000000 : ℝ)*(f.sum) + (6702513149779/4945000000000000000000000000 : ℝ)*base66 + (1350449490225799767/989000000000000000000000000000000 : ℝ)*base67 + (12234036647384200233/989000000000000000000000000000000 : ℝ)*base70 + (1533729586720200233/989000000000000000000000000000000 : ℝ)*base72 + (30618010767631/4945000000000000000000000000 : ℝ)*base73 + (3237760560964200233/989000000000000000000000000000000 : ℝ)*base76 + (5279872438492200233/989000000000000000000000000000000 : ℝ)*base78 + (68877368799767/989000000000000000000000000000000 : ℝ)*base79 + (17116928164639/4945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17872211/5000000000000000000000 : ℝ)*base90 + (17872211/5000000000000000000000 : ℝ)*base92 + (17872211/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1238_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1251/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (617/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1238_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1238_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1238_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1238_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
