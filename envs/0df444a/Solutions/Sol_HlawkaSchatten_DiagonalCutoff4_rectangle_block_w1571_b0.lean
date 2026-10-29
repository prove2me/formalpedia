-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:49.285624+00:00
-- url     : https://prove2.me/submissions/ed77aeaf-640f-4577-88b3-3cee64193f55

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
theorem support_rectangle_w1571_s0_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1625006177/10000000000 : ℝ)*x 0 + (2934411881/5000000000 : ℝ)*x 1 + (2439876377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1625006177/10000000000 : ℝ)^4639 ≤ (9712220007309/100000000000000 : ℝ)^3615 := by
    have hnat : (1625006177 : ℕ)^4639*100000000000000^3615 ≤ 9712220007309^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625006177 10000000000 9712220007309 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934411881/5000000000 : ℝ)^4639 ≤ (50464953430241/100000000000000 : ℝ)^3615 := by
    have hnat : (2934411881 : ℕ)^4639*100000000000000^3615 ≤ 50464953430241^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934411881 5000000000 50464953430241 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2439876377/5000000000 : ℝ)^4639 ≤ (4977853318219/12500000000000 : ℝ)^3615 := by
    have hnat : (2439876377 : ℕ)^4639*12500000000000^3615 ≤ 4977853318219^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439876377 5000000000 4977853318219 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1625006177/10000000000 : ℝ), (2934411881/5000000000 : ℝ), (2439876377/5000000000 : ℝ)] ![(9712220007309/100000000000000 : ℝ), (50464953430241/100000000000000 : ℝ), (4977853318219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1625006177/10000000000 : ℝ)|^4639 ≤ (9712220007309/100000000000000 : ℝ)^3615
        have hw : |(-1625006177/10000000000 : ℝ)|=(1625006177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934411881/5000000000 : ℝ)|^4639 ≤ (50464953430241/100000000000000 : ℝ)^3615
        have hw : |(2934411881/5000000000 : ℝ)|=(2934411881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2439876377/5000000000 : ℝ)|^4639 ≤ (4977853318219/12500000000000 : ℝ)^3615
        have hw : |(2439876377/5000000000 : ℝ)|=(2439876377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s0_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5465265149/10000000000 : ℝ)*x 0 + (-2175338057/10000000000 : ℝ)*x 1 + (1219938189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5465265149/10000000000 : ℝ)^4639 ≤ (4605596640247/10000000000000 : ℝ)^3615 := by
    have hnat : (5465265149 : ℕ)^4639*10000000000000^3615 ≤ 4605596640247^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465265149 10000000000 4605596640247 10000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175338057/10000000000 : ℝ)^4639 ≤ (14121207023117/100000000000000 : ℝ)^3615 := by
    have hnat : (2175338057 : ℕ)^4639*100000000000000^3615 ≤ 14121207023117^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175338057 10000000000 14121207023117 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1219938189/2500000000 : ℝ)^4639 ≤ (39822826566697/100000000000000 : ℝ)^3615 := by
    have hnat : (1219938189 : ℕ)^4639*100000000000000^3615 ≤ 39822826566697^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219938189 2500000000 39822826566697 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5465265149/10000000000 : ℝ), (-2175338057/10000000000 : ℝ), (1219938189/2500000000 : ℝ)] ![(4605596640247/10000000000000 : ℝ), (14121207023117/100000000000000 : ℝ), (39822826566697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5465265149/10000000000 : ℝ)|^4639 ≤ (4605596640247/10000000000000 : ℝ)^3615
        have hw : |(5465265149/10000000000 : ℝ)|=(5465265149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2175338057/10000000000 : ℝ)|^4639 ≤ (14121207023117/100000000000000 : ℝ)^3615
        have hw : |(-2175338057/10000000000 : ℝ)|=(2175338057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1219938189/2500000000 : ℝ)|^4639 ≤ (39822826566697/100000000000000 : ℝ)^3615
        have hw : |(1219938189/2500000000 : ℝ)|=(1219938189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s0_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2732632603/5000000000 : ℝ)*x 0 + (4879752687/10000000000 : ℝ)*x 1 + (-2175338069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2732632603/5000000000 : ℝ)^4639 ≤ (23027983509437/50000000000000 : ℝ)^3615 := by
    have hnat : (2732632603 : ℕ)^4639*50000000000000^3615 ≤ 23027983509437^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732632603 5000000000 23027983509437 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4879752687/10000000000 : ℝ)^4639 ≤ (19911412922047/50000000000000 : ℝ)^3615 := by
    have hnat : (4879752687 : ℕ)^4639*50000000000000^3615 ≤ 19911412922047^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4879752687 10000000000 19911412922047 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175338069/10000000000 : ℝ)^4639 ≤ (14121207123081/100000000000000 : ℝ)^3615 := by
    have hnat : (2175338069 : ℕ)^4639*100000000000000^3615 ≤ 14121207123081^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175338069 10000000000 14121207123081 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2732632603/5000000000 : ℝ), (4879752687/10000000000 : ℝ), (-2175338069/10000000000 : ℝ)] ![(23027983509437/50000000000000 : ℝ), (19911412922047/50000000000000 : ℝ), (14121207123081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2732632603/5000000000 : ℝ)|^4639 ≤ (23027983509437/50000000000000 : ℝ)^3615
        have hw : |(2732632603/5000000000 : ℝ)|=(2732632603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4879752687/10000000000 : ℝ)|^4639 ≤ (19911412922047/50000000000000 : ℝ)^3615
        have hw : |(4879752687/10000000000 : ℝ)|=(4879752687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175338069/10000000000 : ℝ)|^4639 ≤ (14121207123081/100000000000000 : ℝ)^3615
        have hw : |(-2175338069/10000000000 : ℝ)|=(2175338069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s0_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4129592819/10000000000 : ℝ)*x 0 + (3093216383/10000000000 : ℝ)*x 1 + (2714785217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4129592819/10000000000 : ℝ)^4639 ≤ (32144561829793/100000000000000 : ℝ)^3615 := by
    have hnat : (4129592819 : ℕ)^4639*100000000000000^3615 ≤ 32144561829793^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129592819 10000000000 32144561829793 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093216383/10000000000 : ℝ)^4639 ≤ (22185120666113/100000000000000 : ℝ)^3615 := by
    have hnat : (3093216383 : ℕ)^4639*100000000000000^3615 ≤ 22185120666113^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093216383 10000000000 22185120666113 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714785217/5000000000 : ℝ)^4639 ≤ (9134063499357/20000000000000 : ℝ)^3615 := by
    have hnat : (2714785217 : ℕ)^4639*20000000000000^3615 ≤ 9134063499357^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714785217 5000000000 9134063499357 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4129592819/10000000000 : ℝ), (3093216383/10000000000 : ℝ), (2714785217/5000000000 : ℝ)] ![(32144561829793/100000000000000 : ℝ), (22185120666113/100000000000000 : ℝ), (9134063499357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4129592819/10000000000 : ℝ)|^4639 ≤ (32144561829793/100000000000000 : ℝ)^3615
        have hw : |(4129592819/10000000000 : ℝ)|=(4129592819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093216383/10000000000 : ℝ)|^4639 ≤ (22185120666113/100000000000000 : ℝ)^3615
        have hw : |(3093216383/10000000000 : ℝ)|=(3093216383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714785217/5000000000 : ℝ)|^4639 ≤ (9134063499357/20000000000000 : ℝ)^3615
        have hw : |(2714785217/5000000000 : ℝ)|=(2714785217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s0_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-407012557/2500000000 : ℝ)*x 0 + (2452337187/5000000000 : ℝ)*x 1 + (5843022011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407012557/2500000000 : ℝ)^4639 ≤ (4867786610357/50000000000000 : ℝ)^3615 := by
    have hnat : (407012557 : ℕ)^4639*50000000000000^3615 ≤ 4867786610357^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407012557 2500000000 4867786610357 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2452337187/5000000000 : ℝ)^4639 ≤ (40084006745689/100000000000000 : ℝ)^3615 := by
    have hnat : (2452337187 : ℕ)^4639*100000000000000^3615 ≤ 40084006745689^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452337187 5000000000 40084006745689 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5843022011/10000000000 : ℝ)^4639 ≤ (50180420021273/100000000000000 : ℝ)^3615 := by
    have hnat : (5843022011 : ℕ)^4639*100000000000000^3615 ≤ 50180420021273^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5843022011 10000000000 50180420021273 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407012557/2500000000 : ℝ), (2452337187/5000000000 : ℝ), (5843022011/10000000000 : ℝ)] ![(4867786610357/50000000000000 : ℝ), (40084006745689/100000000000000 : ℝ), (50180420021273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407012557/2500000000 : ℝ)|^4639 ≤ (4867786610357/50000000000000 : ℝ)^3615
        have hw : |(-407012557/2500000000 : ℝ)|=(407012557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2452337187/5000000000 : ℝ)|^4639 ≤ (40084006745689/100000000000000 : ℝ)^3615
        have hw : |(2452337187/5000000000 : ℝ)|=(2452337187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5843022011/10000000000 : ℝ)|^4639 ≤ (50180420021273/100000000000000 : ℝ)^3615
        have hw : |(5843022011/10000000000 : ℝ)|=(5843022011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s0_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298717693/2500000000 : ℝ)*x 0 + (-606037143/5000000000 : ℝ)*x 1 + (5843023867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298717693/2500000000 : ℝ)^4639 ≤ (215763147077/500000000000 : ℝ)^3615 := by
    have hnat : (1298717693 : ℕ)^4639*500000000000^3615 ≤ 215763147077^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298717693 2500000000 215763147077 500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606037143/5000000000 : ℝ)^4639 ≤ (6666930097639/100000000000000 : ℝ)^3615 := by
    have hnat : (606037143 : ℕ)^4639*100000000000000^3615 ≤ 6666930097639^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606037143 5000000000 6666930097639 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5843023867/10000000000 : ℝ)^4639 ≤ (10036088095173/20000000000000 : ℝ)^3615 := by
    have hnat : (5843023867 : ℕ)^4639*20000000000000^3615 ≤ 10036088095173^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5843023867 10000000000 10036088095173 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298717693/2500000000 : ℝ), (-606037143/5000000000 : ℝ), (5843023867/10000000000 : ℝ)] ![(215763147077/500000000000 : ℝ), (6666930097639/100000000000000 : ℝ), (10036088095173/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298717693/2500000000 : ℝ)|^4639 ≤ (215763147077/500000000000 : ℝ)^3615
        have hw : |(1298717693/2500000000 : ℝ)|=(1298717693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-606037143/5000000000 : ℝ)|^4639 ≤ (6666930097639/100000000000000 : ℝ)^3615
        have hw : |(-606037143/5000000000 : ℝ)|=(606037143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5843023867/10000000000 : ℝ)|^4639 ≤ (10036088095173/20000000000000 : ℝ)^3615
        have hw : |(5843023867/10000000000 : ℝ)|=(5843023867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s0_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194879473/10000000000 : ℝ)*x 0 + (2337207/4000000 : ℝ)*x 1 + (-606035543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194879473/10000000000 : ℝ)^4639 ≤ (21576361083121/50000000000000 : ℝ)^3615 := by
    have hnat : (5194879473 : ℕ)^4639*50000000000000^3615 ≤ 21576361083121^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194879473 10000000000 21576361083121 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2337207/4000000 : ℝ)^4639 ≤ (50180370306481/100000000000000 : ℝ)^3615 := by
    have hnat : (2337207 : ℕ)^4639*100000000000000^3615 ≤ 50180370306481^3615*4000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337207 4000000 50180370306481 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606035543/5000000000 : ℝ)^4639 ≤ (6666907510431/100000000000000 : ℝ)^3615 := by
    have hnat : (606035543 : ℕ)^4639*100000000000000^3615 ≤ 6666907510431^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606035543 5000000000 6666907510431 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194879473/10000000000 : ℝ), (2337207/4000000 : ℝ), (-606035543/5000000000 : ℝ)] ![(21576361083121/50000000000000 : ℝ), (50180370306481/100000000000000 : ℝ), (6666907510431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194879473/10000000000 : ℝ)|^4639 ≤ (21576361083121/50000000000000 : ℝ)^3615
        have hw : |(5194879473/10000000000 : ℝ)|=(5194879473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2337207/4000000 : ℝ)|^4639 ≤ (50180370306481/100000000000000 : ℝ)^3615
        have hw : |(2337207/4000000 : ℝ)|=(2337207/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-606035543/5000000000 : ℝ)|^4639 ≤ (6666907510431/100000000000000 : ℝ)^3615
        have hw : |(-606035543/5000000000 : ℝ)|=(606035543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s0_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034197573/2500000000 : ℝ)*x 0 + (5370706719/10000000000 : ℝ)*x 1 + (315416177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034197573/2500000000 : ℝ)^4639 ≤ (32216474189791/100000000000000 : ℝ)^3615 := by
    have hnat : (1034197573 : ℕ)^4639*100000000000000^3615 ≤ 32216474189791^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034197573 2500000000 32216474189791 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5370706719/10000000000 : ℝ)^4639 ≤ (11258979365663/25000000000000 : ℝ)^3615 := by
    have hnat : (5370706719 : ℕ)^4639*25000000000000^3615 ≤ 11258979365663^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370706719 10000000000 11258979365663 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315416177/1000000000 : ℝ)^4639 ≤ (22747608328911/100000000000000 : ℝ)^3615 := by
    have hnat : (315416177 : ℕ)^4639*100000000000000^3615 ≤ 22747608328911^3615*1000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315416177 1000000000 22747608328911 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034197573/2500000000 : ℝ), (5370706719/10000000000 : ℝ), (315416177/1000000000 : ℝ)] ![(32216474189791/100000000000000 : ℝ), (11258979365663/25000000000000 : ℝ), (22747608328911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034197573/2500000000 : ℝ)|^4639 ≤ (32216474189791/100000000000000 : ℝ)^3615
        have hw : |(1034197573/2500000000 : ℝ)|=(1034197573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5370706719/10000000000 : ℝ)|^4639 ≤ (11258979365663/25000000000000 : ℝ)^3615
        have hw : |(5370706719/10000000000 : ℝ)|=(5370706719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315416177/1000000000 : ℝ)|^4639 ≤ (22747608328911/100000000000000 : ℝ)^3615
        have hw : |(315416177/1000000000 : ℝ)|=(315416177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (889/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12371/50000 : ℝ)*pair X 0 0 := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
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
  have hpowlo : (0 : ℝ) ^ (4637/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4637 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4637*1^1024 ≤ 0^1024*1^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4637/1024 : ℝ) ≤ (1577611907486763421/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4637 ≤ (1577611907486763421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4637*100000000000000000000^1024 ≤ 1577611907486763421^1024*5^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1577611907486763421 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1577611907486763421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4637 := by
      have hnat : (1 : ℕ)^1024*1^4637 ≤ 1^4637*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101577611907486763421/100000000000000000000 : ℝ) ≤ (501731332307591/500000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (101577611907486763421/100000000000000000000 : ℝ)^1024 ≤ (501731332307591/500000000000000 : ℝ)^4637 := by
      have hnat : (101577611907486763421 : ℕ)^1024*500000000000000^4637 ≤ 501731332307591^4637*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101577611907486763421 100000000000000000000 501731332307591 500000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501731332307591/500000000000000 : ℝ)) (X := (101577611907486763421/100000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51577611907486763421/50000000000000000000 : ℝ) ≤ (251731332307591/250000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (51577611907486763421/50000000000000000000 : ℝ)^1024 ≤ (251731332307591/250000000000000 : ℝ)^4637 := by
      have hnat : (51577611907486763421 : ℕ)^1024*250000000000000^4637 ≤ 251731332307591^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51577611907486763421 50000000000000000000 251731332307591 250000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251731332307591/250000000000000 : ℝ)) (X := (51577611907486763421/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1731332307591/200000000000000 : ℝ)*(0 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1731332307591/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1577611907486763421/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1731332307591/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1731332307591/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(501731332307591/500000000000000 : ℝ) by norm_num, show 1+(1577611907486763421/100000000000000000000 : ℝ)+(0 : ℝ)=(101577611907486763421/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1577611907486763421/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1731332307591/200000000000000 : ℝ)*(2/5 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1731332307591/200000000000000 : ℝ)*(2/5 : ℝ)=(251731332307591/250000000000000 : ℝ) by norm_num, show 1+2*(1577611907486763421/100000000000000000000 : ℝ)=(51577611907486763421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1731332307591/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1731332307591/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1731332307591/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1731332307591/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1731332307591/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1731332307591/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1625006177/10000000000 : ℝ)*X 0 0+(2934411881/5000000000 : ℝ)*X 0 1+(2439876377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5465265149/10000000000 : ℝ)*X 1 0+(-2175338057/10000000000 : ℝ)*X 1 1+(1219938189/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2732632603/5000000000 : ℝ)*X 2 0+(4879752687/10000000000 : ℝ)*X 2 1+(-2175338069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4129592819/10000000000 : ℝ)*X 0 0+(3093216383/10000000000 : ℝ)*X 0 1+(2714785217/5000000000 : ℝ)*X 0 2+(4129592819/10000000000 : ℝ)*X 1 0+(3093216383/10000000000 : ℝ)*X 1 1+(2714785217/5000000000 : ℝ)*X 1 2+(4129592819/10000000000 : ℝ)*X 2 0+(3093216383/10000000000 : ℝ)*X 2 1+(2714785217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-407012557/2500000000 : ℝ)*X 0 0+(2452337187/5000000000 : ℝ)*X 0 1+(5843022011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1298717693/2500000000 : ℝ)*X 1 0+(-606037143/5000000000 : ℝ)*X 1 1+(5843023867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5194879473/10000000000 : ℝ)*X 2 0+(2337207/4000000 : ℝ)*X 2 1+(-606035543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1034197573/2500000000 : ℝ)*X 0 0+(5370706719/10000000000 : ℝ)*X 0 1+(315416177/1000000000 : ℝ)*X 0 2+(1034197573/2500000000 : ℝ)*X 1 0+(5370706719/10000000000 : ℝ)*X 1 1+(315416177/1000000000 : ℝ)*X 1 2+(1034197573/2500000000 : ℝ)*X 2 0+(5370706719/10000000000 : ℝ)*X 2 1+(315416177/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14342783999366796329643/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8370073/12500000000000 : ℝ)*(base1) + (296422689/20000000000000 : ℝ)*(base19) + (93291143/6250000000000 : ℝ)*(base23) + (193273281/100000000000000 : ℝ)*(upper3) + (38489157/20000000000000 : ℝ)*(upper5) + (719541331082191/100000000000000 : ℝ)*(major0) + (719541331082191/100000000000000 : ℝ)*(major1) + (719541331082191/100000000000000 : ℝ)*(major2) + (505527498940703/50000000000000 : ℝ)*(sp0) + (505529491711719/50000000000000 : ℝ)*(sp1) + (202211794575719/20000000000000 : ℝ)*(sp2) + (107004885273947/25000000000000 : ℝ)*(sp3) + (5534616061/100000000000000 : ℝ)*(sp4) + (587381181/25000000000000 : ℝ)*(sp7) + (85604391516219/20000000000000 : ℝ)*(f.failure) + (1011060465536883/100000000000000 : ℝ)*(f.sum) + (9584375888119/10000000000000000000000000000 : ℝ)*base66 + (177794796708119/20000000000000000000000000000 : ℝ)*base68 + (21489571128119/20000000000000000000000000000 : ℝ)*base70 + (70208446628119/20000000000000000000000000000 : ℝ)*base72 + (50824039728119/10000000000000000000000000000 : ℝ)*base74 + (19620742211881/20000000000000000000000000000 : ℝ)*base75 + (40298512788119/20000000000000000000000000000 : ℝ)*base78 + (69189688288119/20000000000000000000000000000 : ℝ)*base80 + (14308689958119/10000000000000000000000000000 : ℝ)*base82 + (5407471/2000000000000000000000 : ℝ)*base89 + (5407471/2000000000000000000000 : ℝ)*base91 + (5407471/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43113792849551159861841/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (351258343/100000000000000 : ℝ)*(base15) + (370108097/100000000000000 : ℝ)*(base23) + (449969611/100000000000000 : ℝ)*(base51) + (116251989/100000000000000 : ℝ)*(upper4) + (7330217/6250000000000 : ℝ)*(upper5) + (758432210046083/100000000000000 : ℝ)*(major0) + (758432210046083/100000000000000 : ℝ)*(major1) + (758432210046083/100000000000000 : ℝ)*(major2) + (15459223/20000000000000 : ℝ)*(sp0) + (332991613/25000000000000 : ℝ)*(sp3) + (1065707850985593/100000000000000 : ℝ)*(sp4) + (213141515404673/20000000000000 : ℝ)*(sp5) + (1065707558173611/100000000000000 : ℝ)*(sp6) + (451155016131361/100000000000000 : ℝ)*(sp7) + (451156348097813/100000000000000 : ℝ)*(f.failure) + (266426982070427/25000000000000 : ℝ)*(f.sum) + (11789039693947/10000000000000000000000000000 : ℝ)*base66 + (28999318976053/20000000000000000000000000000 : ℝ)*base67 + (33326906703947/20000000000000000000000000000 : ℝ)*base70 + (16707973116053/20000000000000000000000000000 : ℝ)*base71 + (29848787866053/10000000000000000000000000000 : ℝ)*base73 + (123807191143947/20000000000000000000000000000 : ℝ)*base76 + (65615988656053/20000000000000000000000000000 : ℝ)*base77 + (12172962783947/20000000000000000000000000000 : ℝ)*base80 + (5272464796053/10000000000000000000000000000 : ℝ)*base81 + (29590817/10000000000000000000000 : ℝ)*base89 + (29590817/10000000000000000000000 : ℝ)*base91 + (29590817/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1571_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (889/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12371/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1571_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1571_s1_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-881680007/5000000000 : ℝ)*x 0 + (5534264519/10000000000 : ℝ)*x 1 + (5125131039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881680007/5000000000 : ℝ)^4639 ≤ (10785899984169/100000000000000 : ℝ)^3615 := by
    have hnat : (881680007 : ℕ)^4639*100000000000000^3615 ≤ 10785899984169^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881680007 5000000000 10785899984169 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5534264519/10000000000 : ℝ)^4639 ≤ (2925216457793/6250000000000 : ℝ)^3615 := by
    have hnat : (5534264519 : ℕ)^4639*6250000000000^3615 ≤ 2925216457793^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534264519 10000000000 2925216457793 6250000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5125131039/10000000000 : ℝ)^4639 ≤ (42410636675473/100000000000000 : ℝ)^3615 := by
    have hnat : (5125131039 : ℕ)^4639*100000000000000^3615 ≤ 42410636675473^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125131039 10000000000 42410636675473 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881680007/5000000000 : ℝ), (5534264519/10000000000 : ℝ), (5125131039/10000000000 : ℝ)] ![(10785899984169/100000000000000 : ℝ), (2925216457793/6250000000000 : ℝ), (42410636675473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881680007/5000000000 : ℝ)|^4639 ≤ (10785899984169/100000000000000 : ℝ)^3615
        have hw : |(-881680007/5000000000 : ℝ)|=(881680007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5534264519/10000000000 : ℝ)|^4639 ≤ (2925216457793/6250000000000 : ℝ)^3615
        have hw : |(5534264519/10000000000 : ℝ)|=(5534264519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5125131039/10000000000 : ℝ)|^4639 ≤ (42410636675473/100000000000000 : ℝ)^3615
        have hw : |(5125131039/10000000000 : ℝ)|=(5125131039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s1_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344067209/2500000000 : ℝ)*x 0 + (-1977342623/10000000000 : ℝ)*x 1 + (2562565383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344067209/2500000000 : ℝ)^4639 ≤ (45095778942653/100000000000000 : ℝ)^3615 := by
    have hnat : (1344067209 : ℕ)^4639*100000000000000^3615 ≤ 45095778942653^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344067209 2500000000 45095778942653 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1977342623/10000000000 : ℝ)^4639 ≤ (12493587265097/100000000000000 : ℝ)^3615 := by
    have hnat : (1977342623 : ℕ)^4639*100000000000000^3615 ≤ 12493587265097^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977342623 10000000000 12493587265097 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2562565383/5000000000 : ℝ)^4639 ≤ (42410633776471/100000000000000 : ℝ)^3615 := by
    have hnat : (2562565383 : ℕ)^4639*100000000000000^3615 ≤ 42410633776471^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562565383 5000000000 42410633776471 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344067209/2500000000 : ℝ), (-1977342623/10000000000 : ℝ), (2562565383/5000000000 : ℝ)] ![(45095778942653/100000000000000 : ℝ), (12493587265097/100000000000000 : ℝ), (42410633776471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344067209/2500000000 : ℝ)|^4639 ≤ (45095778942653/100000000000000 : ℝ)^3615
        have hw : |(1344067209/2500000000 : ℝ)|=(1344067209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1977342623/10000000000 : ℝ)|^4639 ≤ (12493587265097/100000000000000 : ℝ)^3615
        have hw : |(-1977342623/10000000000 : ℝ)|=(1977342623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2562565383/5000000000 : ℝ)|^4639 ≤ (42410633776471/100000000000000 : ℝ)^3615
        have hw : |(2562565383/5000000000 : ℝ)|=(2562565383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s1_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376268741/10000000000 : ℝ)*x 0 + (5125131063/10000000000 : ℝ)*x 1 + (-1977342361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376268741/10000000000 : ℝ)^4639 ≤ (45095777920079/100000000000000 : ℝ)^3615 := by
    have hnat : (5376268741 : ℕ)^4639*100000000000000^3615 ≤ 45095777920079^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376268741 10000000000 45095777920079 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125131063/10000000000 : ℝ)^4639 ≤ (4241063693033/10000000000000 : ℝ)^3615 := by
    have hnat : (5125131063 : ℕ)^4639*10000000000000^3615 ≤ 4241063693033^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125131063 10000000000 4241063693033 10000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977342361/10000000000 : ℝ)^4639 ≤ (3123396285191/25000000000000 : ℝ)^3615 := by
    have hnat : (1977342361 : ℕ)^4639*25000000000000^3615 ≤ 3123396285191^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977342361 10000000000 3123396285191 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376268741/10000000000 : ℝ), (5125131063/10000000000 : ℝ), (-1977342361/10000000000 : ℝ)] ![(45095777920079/100000000000000 : ℝ), (4241063693033/10000000000000 : ℝ), (3123396285191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376268741/10000000000 : ℝ)|^4639 ≤ (45095777920079/100000000000000 : ℝ)^3615
        have hw : |(5376268741/10000000000 : ℝ)|=(5376268741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125131063/10000000000 : ℝ)|^4639 ≤ (4241063693033/10000000000000 : ℝ)^3615
        have hw : |(5125131063/10000000000 : ℝ)|=(5125131063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1977342361/10000000000 : ℝ)|^4639 ≤ (3123396285191/25000000000000 : ℝ)^3615
        have hw : |(-1977342361/10000000000 : ℝ)|=(1977342361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s1_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528512017/1250000000 : ℝ)*x 0 + (3767116193/10000000000 : ℝ)*x 1 + (4733560577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528512017/1250000000 : ℝ)^4639 ≤ (33131803966731/100000000000000 : ℝ)^3615 := by
    have hnat : (528512017 : ℕ)^4639*100000000000000^3615 ≤ 33131803966731^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528512017 1250000000 33131803966731 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3767116193/10000000000 : ℝ)^4639 ≤ (28569823578797/100000000000000 : ℝ)^3615 := by
    have hnat : (3767116193 : ℕ)^4639*100000000000000^3615 ≤ 28569823578797^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3767116193 10000000000 28569823578797 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4733560577/10000000000 : ℝ)^4639 ≤ (38298372442073/100000000000000 : ℝ)^3615 := by
    have hnat : (4733560577 : ℕ)^4639*100000000000000^3615 ≤ 38298372442073^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4733560577 10000000000 38298372442073 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528512017/1250000000 : ℝ), (3767116193/10000000000 : ℝ), (4733560577/10000000000 : ℝ)] ![(33131803966731/100000000000000 : ℝ), (28569823578797/100000000000000 : ℝ), (38298372442073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528512017/1250000000 : ℝ)|^4639 ≤ (33131803966731/100000000000000 : ℝ)^3615
        have hw : |(528512017/1250000000 : ℝ)|=(528512017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3767116193/10000000000 : ℝ)|^4639 ≤ (28569823578797/100000000000000 : ℝ)^3615
        have hw : |(3767116193/10000000000 : ℝ)|=(3767116193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4733560577/10000000000 : ℝ)|^4639 ≤ (38298372442073/100000000000000 : ℝ)^3615
        have hw : |(4733560577/10000000000 : ℝ)|=(4733560577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s1_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-881784987/5000000000 : ℝ)*x 0 + (80146033/156250000 : ℝ)*x 1 + (5529987349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881784987/5000000000 : ℝ)^4639 ≤ (10787548053049/100000000000000 : ℝ)^3615 := by
    have hnat : (881784987 : ℕ)^4639*100000000000000^3615 ≤ 10787548053049^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881784987 5000000000 10787548053049 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80146033/156250000 : ℝ)^4639 ≤ (165841413993/390625000000 : ℝ)^3615 := by
    have hnat : (80146033 : ℕ)^4639*390625000000^3615 ≤ 165841413993^3615*156250000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80146033 156250000 165841413993 390625000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5529987349/10000000000 : ℝ)^4639 ≤ (23378524976911/50000000000000 : ℝ)^3615 := by
    have hnat : (5529987349 : ℕ)^4639*50000000000000^3615 ≤ 23378524976911^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529987349 10000000000 23378524976911 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881784987/5000000000 : ℝ), (80146033/156250000 : ℝ), (5529987349/10000000000 : ℝ)] ![(10787548053049/100000000000000 : ℝ), (165841413993/390625000000 : ℝ), (23378524976911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881784987/5000000000 : ℝ)|^4639 ≤ (10787548053049/100000000000000 : ℝ)^3615
        have hw : |(-881784987/5000000000 : ℝ)|=(881784987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80146033/156250000 : ℝ)|^4639 ≤ (165841413993/390625000000 : ℝ)^3615
        have hw : |(80146033/156250000 : ℝ)|=(80146033/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5529987349/10000000000 : ℝ)|^4639 ≤ (23378524976911/50000000000000 : ℝ)^3615
        have hw : |(5529987349/10000000000 : ℝ)|=(5529987349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s1_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210712379/400000000 : ℝ)*x 0 + (-157248601/1000000000 : ℝ)*x 1 + (345624239/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210712379/400000000 : ℝ)^4639 ≤ (43931681553809/100000000000000 : ℝ)^3615 := by
    have hnat : (210712379 : ℕ)^4639*100000000000000^3615 ≤ 43931681553809^3615*400000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210712379 400000000 43931681553809 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157248601/1000000000 : ℝ)^4639 ≤ (9311263322499/100000000000000 : ℝ)^3615 := by
    have hnat : (157248601 : ℕ)^4639*100000000000000^3615 ≤ 9311263322499^3615*1000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157248601 1000000000 9311263322499 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345624239/625000000 : ℝ)^4639 ≤ (46757055107683/100000000000000 : ℝ)^3615 := by
    have hnat : (345624239 : ℕ)^4639*100000000000000^3615 ≤ 46757055107683^3615*625000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345624239 625000000 46757055107683 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210712379/400000000 : ℝ), (-157248601/1000000000 : ℝ), (345624239/625000000 : ℝ)] ![(43931681553809/100000000000000 : ℝ), (9311263322499/100000000000000 : ℝ), (46757055107683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210712379/400000000 : ℝ)|^4639 ≤ (43931681553809/100000000000000 : ℝ)^3615
        have hw : |(210712379/400000000 : ℝ)|=(210712379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-157248601/1000000000 : ℝ)|^4639 ≤ (9311263322499/100000000000000 : ℝ)^3615
        have hw : |(-157248601/1000000000 : ℝ)|=(157248601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345624239/625000000 : ℝ)|^4639 ≤ (46757055107683/100000000000000 : ℝ)^3615
        have hw : |(345624239/625000000 : ℝ)|=(345624239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s1_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267808933/10000000000 : ℝ)*x 0 + (221199521/400000000 : ℝ)*x 1 + (-786243243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267808933/10000000000 : ℝ)^4639 ≤ (2196583787667/5000000000000 : ℝ)^3615 := by
    have hnat : (5267808933 : ℕ)^4639*5000000000000^3615 ≤ 2196583787667^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267808933 10000000000 2196583787667 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221199521/400000000 : ℝ)^4639 ≤ (46757057288579/100000000000000 : ℝ)^3615 := by
    have hnat : (221199521 : ℕ)^4639*100000000000000^3615 ≤ 46757057288579^3615*400000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221199521 400000000 46757057288579 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (786243243/5000000000 : ℝ)^4639 ≤ (9311266939469/100000000000000 : ℝ)^3615 := by
    have hnat : (786243243 : ℕ)^4639*100000000000000^3615 ≤ 9311266939469^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786243243 5000000000 9311266939469 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267808933/10000000000 : ℝ), (221199521/400000000 : ℝ), (-786243243/5000000000 : ℝ)] ![(2196583787667/5000000000000 : ℝ), (46757057288579/100000000000000 : ℝ), (9311266939469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267808933/10000000000 : ℝ)|^4639 ≤ (2196583787667/5000000000000 : ℝ)^3615
        have hw : |(5267808933/10000000000 : ℝ)|=(5267808933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221199521/400000000 : ℝ)|^4639 ≤ (46757057288579/100000000000000 : ℝ)^3615
        have hw : |(221199521/400000000 : ℝ)|=(221199521/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-786243243/5000000000 : ℝ)|^4639 ≤ (9311266939469/100000000000000 : ℝ)^3615
        have hw : |(-786243243/5000000000 : ℝ)|=(786243243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s1_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114295501/5000000000 : ℝ)*x 0 + (1180901033/2500000000 : ℝ)*x 1 + (3777219667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114295501/5000000000 : ℝ)^4639 ≤ (33136780319/100000000000 : ℝ)^3615 := by
    have hnat : (2114295501 : ℕ)^4639*100000000000^3615 ≤ 33136780319^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114295501 5000000000 33136780319 100000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1180901033/2500000000 : ℝ)^4639 ≤ (38195028913537/100000000000000 : ℝ)^3615 := by
    have hnat : (1180901033 : ℕ)^4639*100000000000000^3615 ≤ 38195028913537^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180901033 2500000000 38195028913537 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3777219667/10000000000 : ℝ)^4639 ≤ (28668190748573/100000000000000 : ℝ)^3615 := by
    have hnat : (3777219667 : ℕ)^4639*100000000000000^3615 ≤ 28668190748573^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3777219667 10000000000 28668190748573 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114295501/5000000000 : ℝ), (1180901033/2500000000 : ℝ), (3777219667/10000000000 : ℝ)] ![(33136780319/100000000000 : ℝ), (38195028913537/100000000000000 : ℝ), (28668190748573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114295501/5000000000 : ℝ)|^4639 ≤ (33136780319/100000000000 : ℝ)^3615
        have hw : |(2114295501/5000000000 : ℝ)|=(2114295501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1180901033/2500000000 : ℝ)|^4639 ≤ (38195028913537/100000000000000 : ℝ)^3615
        have hw : |(1180901033/2500000000 : ℝ)|=(1180901033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3777219667/10000000000 : ℝ)|^4639 ≤ (28668190748573/100000000000000 : ℝ)^3615
        have hw : |(3777219667/10000000000 : ℝ)|=(3777219667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (889/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9081/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8873/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (889/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (889/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (889/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (889/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (889/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (889/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (889/25000 : ℝ) ^ (4637/1024 : ℝ) ≤ (27434096967403/100000000000000000000 : ℝ) := by
    have hpowers : (889/25000 : ℝ)^4637 ≤ (27434096967403/100000000000000000000 : ℝ)^1024 := by
      have hnat : (889 : ℕ)^4637*100000000000000000000^1024 ≤ 27434096967403^1024*25000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        889 25000 27434096967403 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (889/25000 : ℝ)) (X := (27434096967403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12371/50000 : ℝ) ^ (4637/1024 : ℝ) ≤ (179175446581799549/100000000000000000000 : ℝ) := by
    have hpowers : (12371/50000 : ℝ)^4637 ≤ (179175446581799549/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12371 : ℕ)^4637*100000000000000000000^1024 ≤ 179175446581799549^1024*50000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12371 50000 179175446581799549 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12371/50000 : ℝ)) (X := (179175446581799549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000027434096967403/50000000000000000000 : ℝ) ≤ (10000001211667427/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50000027434096967403/50000000000000000000 : ℝ)^1024 ≤ (10000001211667427/10000000000000000 : ℝ)^4637 := by
      have hnat : (50000027434096967403 : ℕ)^1024*10000000000000000^4637 ≤ 10000001211667427^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000027434096967403 50000000000000000000 10000001211667427 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001211667427/10000000000000000 : ℝ)) (X := (50000027434096967403/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12522400360084845869/12500000000000000000 : ℝ) ≤ (10003954620951227/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (12522400360084845869/12500000000000000000 : ℝ)^1024 ≤ (10003954620951227/10000000000000000 : ℝ)^4637 := by
      have hnat : (12522400360084845869 : ℕ)^1024*10000000000000000^4637 ≤ 10003954620951227^4637*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12522400360084845869 12500000000000000000 10003954620951227 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003954620951227/10000000000000000 : ℝ)) (X := (12522400360084845869/12500000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50179175446581799549/50000000000000000000 : ℝ) ≤ (10007908030235027/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50179175446581799549/50000000000000000000 : ℝ)^1024 ≤ (10007908030235027/10000000000000000 : ℝ)^4637 := by
      have hnat : (50179175446581799549 : ℕ)^1024*10000000000000000^4637 ≤ 10007908030235027^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50179175446581799549 50000000000000000000 10007908030235027 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007908030235027/10000000000000000 : ℝ)) (X := (50179175446581799549/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27434096967403/100000000000000000000 : ℝ) ≤ ((11768439390197762379/11770000000000000000 : ℝ)+2*(2196338491/1177000000000 : ℝ)*(889/25000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (11768439390197762379/11770000000000000000 : ℝ)+2*(2196338491/1177000000000 : ℝ)*(889/25000 : ℝ)=(10000001211667427/10000000000000000 : ℝ) by norm_num, show 1+2*(27434096967403/100000000000000000000 : ℝ)=(50000027434096967403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(179175446581799549/100000000000000000000 : ℝ)+(27434096967403/100000000000000000000 : ℝ) ≤ ((11768439390197762379/11770000000000000000 : ℝ)+(2196338491/1177000000000 : ℝ)*((12371/50000 : ℝ)+(889/25000 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (11768439390197762379/11770000000000000000 : ℝ)+(2196338491/1177000000000 : ℝ)*((12371/50000 : ℝ)+(889/25000 : ℝ))=(10003954620951227/10000000000000000 : ℝ) by norm_num, show 1+(179175446581799549/100000000000000000000 : ℝ)+(27434096967403/100000000000000000000 : ℝ)=(12522400360084845869/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(179175446581799549/100000000000000000000 : ℝ) ≤ ((11768439390197762379/11770000000000000000 : ℝ)+2*(2196338491/1177000000000 : ℝ)*(12371/50000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (11768439390197762379/11770000000000000000 : ℝ)+2*(2196338491/1177000000000 : ℝ)*(12371/50000 : ℝ)=(10007908030235027/10000000000000000 : ℝ) by norm_num, show 1+2*(179175446581799549/100000000000000000000 : ℝ)=(50179175446581799549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11768439390197762379/11770000000000000000 : ℝ)*(X 1 0+X 2 0)+(2196338491/1177000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (889/25000 : ℝ)) (hi := (12371/50000 : ℝ)) (c := (11768439390197762379/11770000000000000000 : ℝ)) (alpha := (2196338491/1177000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11768439390197762379/11770000000000000000 : ℝ)*(X 0 1+X 2 1)+(2196338491/1177000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (889/25000 : ℝ)) (hi := (12371/50000 : ℝ)) (c := (11768439390197762379/11770000000000000000 : ℝ)) (alpha := (2196338491/1177000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11768439390197762379/11770000000000000000 : ℝ)*(X 0 2+X 1 2)+(2196338491/1177000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (889/25000 : ℝ)) (hi := (12371/50000 : ℝ)) (c := (11768439390197762379/11770000000000000000 : ℝ)) (alpha := (2196338491/1177000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-881680007/5000000000 : ℝ)*X 0 0+(5534264519/10000000000 : ℝ)*X 0 1+(5125131039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1344067209/2500000000 : ℝ)*X 1 0+(-1977342623/10000000000 : ℝ)*X 1 1+(2562565383/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376268741/10000000000 : ℝ)*X 2 0+(5125131063/10000000000 : ℝ)*X 2 1+(-1977342361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((528512017/1250000000 : ℝ)*X 0 0+(3767116193/10000000000 : ℝ)*X 0 1+(4733560577/10000000000 : ℝ)*X 0 2+(528512017/1250000000 : ℝ)*X 1 0+(3767116193/10000000000 : ℝ)*X 1 1+(4733560577/10000000000 : ℝ)*X 1 2+(528512017/1250000000 : ℝ)*X 2 0+(3767116193/10000000000 : ℝ)*X 2 1+(4733560577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-881784987/5000000000 : ℝ)*X 0 0+(80146033/156250000 : ℝ)*X 0 1+(5529987349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210712379/400000000 : ℝ)*X 1 0+(-157248601/1000000000 : ℝ)*X 1 1+(345624239/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5267808933/10000000000 : ℝ)*X 2 0+(221199521/400000000 : ℝ)*X 2 1+(-786243243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2114295501/5000000000 : ℝ)*X 0 0+(1180901033/2500000000 : ℝ)*X 0 1+(3777219667/10000000000 : ℝ)*X 0 2+(2114295501/5000000000 : ℝ)*X 1 0+(1180901033/2500000000 : ℝ)*X 1 1+(3777219667/10000000000 : ℝ)*X 1 2+(2114295501/5000000000 : ℝ)*X 2 0+(1180901033/2500000000 : ℝ)*X 2 1+(3777219667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (576488648557385566031199747/588500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (880049/12500000000000 : ℝ)*(base1) + (742079943/100000000000000 : ℝ)*(base19) + (44208601/6250000000000 : ℝ)*(base23) + (104865429/100000000000000 : ℝ)*(upper5) + (1739465780709469/100000000000000 : ℝ)*(major0) + (1739465780709469/100000000000000 : ℝ)*(major1) + (1739465780709469/100000000000000 : ℝ)*(major2) + (15276224613731/625000000000 : ℝ)*(sp0) + (1222101193583739/50000000000000 : ℝ)*(sp1) + (1222101420319873/50000000000000 : ℝ)*(sp2) + (1034724631734377/100000000000000 : ℝ)*(sp3) + (1523364159/20000000000000 : ℝ)*(sp4) + (418729941/100000000000000 : ℝ)*(sp5) + (16710069/500000000000 : ℝ)*(sp7) + (129340997598571/12500000000000 : ℝ)*(f.failure) + (2444203547977363/100000000000000 : ℝ)*(f.sum) + (537464775237/588500000000000000000000000 : ℝ)*base66 + (4349677307769733249/1177000000000000000000000000000000 : ℝ)*base68 + (2478099456560733249/1177000000000000000000000000000000 : ℝ)*base70 + (3637619107152266751/1177000000000000000000000000000000 : ℝ)*base71 + (3172720255209/1177000000000000000000000000 : ℝ)*base74 + (10439354739690266751/1177000000000000000000000000000000 : ℝ)*base75 + (1387344347221266751/1177000000000000000000000000000000 : ℝ)*base77 + (9984571711144266751/1177000000000000000000000000000000 : ℝ)*base79 + (2312488226091/1177000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11159361/1250000000000000000000 : ℝ)*base90 + (11159361/1250000000000000000000 : ℝ)*base92 + (11159361/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (923171420176844709565335501/117700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1385021239/100000000000000 : ℝ)*(base19) + (1246295197/100000000000000 : ℝ)*(base23) + (71199833/100000000000000 : ℝ)*(upper2) + (271956507/100000000000000 : ℝ)*(upper3) + (135197453/100000000000000 : ℝ)*(upper5) + (355264831938573/20000000000000 : ℝ)*(major0) + (355264831938573/20000000000000 : ℝ)*(major1) + (355264831938573/20000000000000 : ℝ)*(major2) + (11503058019/100000000000000 : ℝ)*(sp1) + (166775791/1562500000000 : ℝ)*(sp2) + (2495994727146383/100000000000000 : ℝ)*(sp4) + (19967854712537/800000000000 : ℝ)*(sp5) + (1247991403600281/50000000000000 : ℝ)*(sp6) + (13208166634897/1250000000000 : ℝ)*(sp7) + (13208166634897/1250000000000 : ℝ)*(f.failure) + (2495994727146383/100000000000000 : ℝ)*(f.sum) + (425500265653/588500000000000000000000000 : ℝ)*base66 + (153903701038054833/235400000000000000000000000000000 : ℝ)*base68 + (1078041631828545167/235400000000000000000000000000000 : ℝ)*base69 + (1077115091768254833/235400000000000000000000000000000 : ℝ)*base72 + (2758566861059/1177000000000000000000000000 : ℝ)*base73 + (1038614512428745167/235400000000000000000000000000000 : ℝ)*base75 + (349013351241654833/235400000000000000000000000000000 : ℝ)*base78 + (108963596734454833/235400000000000000000000000000000 : ℝ)*base80 + (208852597819/147125000000000000000000000 : ℝ)*base81 + (788573/125000000000000000000 : ℝ)*base89 + (788573/125000000000000000000 : ℝ)*base91 + (788573/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1571_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (889/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9081/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8873/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1571_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1571_s2_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-890932619/5000000000 : ℝ)*x 0 + (5441196831/10000000000 : ℝ)*x 1 + (5206138689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890932619/5000000000 : ℝ)^4639 ≤ (10931368575819/100000000000000 : ℝ)^3615 := by
    have hnat : (890932619 : ℕ)^4639*100000000000000^3615 ≤ 10931368575819^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890932619 5000000000 10931368575819 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441196831/10000000000 : ℝ)^4639 ≤ (45795851507291/100000000000000 : ℝ)^3615 := by
    have hnat : (5441196831 : ℕ)^4639*100000000000000^3615 ≤ 45795851507291^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441196831 10000000000 45795851507291 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206138689/10000000000 : ℝ)^4639 ≤ (1730911196301/4000000000000 : ℝ)^3615 := by
    have hnat : (5206138689 : ℕ)^4639*4000000000000^3615 ≤ 1730911196301^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206138689 10000000000 1730911196301 4000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-890932619/5000000000 : ℝ), (5441196831/10000000000 : ℝ), (5206138689/10000000000 : ℝ)] ![(10931368575819/100000000000000 : ℝ), (45795851507291/100000000000000 : ℝ), (1730911196301/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-890932619/5000000000 : ℝ)|^4639 ≤ (10931368575819/100000000000000 : ℝ)^3615
        have hw : |(-890932619/5000000000 : ℝ)|=(890932619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441196831/10000000000 : ℝ)|^4639 ≤ (45795851507291/100000000000000 : ℝ)^3615
        have hw : |(5441196831/10000000000 : ℝ)|=(5441196831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206138689/10000000000 : ℝ)|^4639 ≤ (1730911196301/4000000000000 : ℝ)^3615
        have hw : |(5206138689/10000000000 : ℝ)|=(5206138689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s2_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167257049/312500000 : ℝ)*x 0 + (-1902505851/10000000000 : ℝ)*x 1 + (2603069087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167257049/312500000 : ℝ)^4639 ≤ (5604642864289/12500000000000 : ℝ)^3615 := by
    have hnat : (167257049 : ℕ)^4639*12500000000000^3615 ≤ 5604642864289^3615*312500000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167257049 312500000 5604642864289 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902505851/10000000000 : ℝ)^4639 ≤ (371565083137/3125000000000 : ℝ)^3615 := by
    have hnat : (1902505851 : ℕ)^4639*3125000000000^3615 ≤ 371565083137^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902505851 10000000000 371565083137 3125000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603069087/5000000000 : ℝ)^4639 ≤ (10818193603591/25000000000000 : ℝ)^3615 := by
    have hnat : (2603069087 : ℕ)^4639*25000000000000^3615 ≤ 10818193603591^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603069087 5000000000 10818193603591 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167257049/312500000 : ℝ), (-1902505851/10000000000 : ℝ), (2603069087/5000000000 : ℝ)] ![(5604642864289/12500000000000 : ℝ), (371565083137/3125000000000 : ℝ), (10818193603591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167257049/312500000 : ℝ)|^4639 ≤ (5604642864289/12500000000000 : ℝ)^3615
        have hw : |(167257049/312500000 : ℝ)|=(167257049/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1902505851/10000000000 : ℝ)|^4639 ≤ (371565083137/3125000000000 : ℝ)^3615
        have hw : |(-1902505851/10000000000 : ℝ)|=(1902505851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2603069087/5000000000 : ℝ)|^4639 ≤ (10818193603591/25000000000000 : ℝ)^3615
        have hw : |(2603069087/5000000000 : ℝ)|=(2603069087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s2_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352226081/10000000000 : ℝ)*x 0 + (1301534439/2500000000 : ℝ)*x 1 + (-47562643/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352226081/10000000000 : ℝ)^4639 ≤ (11209287107301/25000000000000 : ℝ)^3615 := by
    have hnat : (5352226081 : ℕ)^4639*25000000000000^3615 ≤ 11209287107301^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352226081 10000000000 11209287107301 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301534439/2500000000 : ℝ)^4639 ≤ (43272769955837/100000000000000 : ℝ)^3615 := by
    have hnat : (1301534439 : ℕ)^4639*100000000000000^3615 ≤ 43272769955837^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301534439 2500000000 43272769955837 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47562643/250000000 : ℝ)^4639 ≤ (5945040804881/50000000000000 : ℝ)^3615 := by
    have hnat : (47562643 : ℕ)^4639*50000000000000^3615 ≤ 5945040804881^3615*250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47562643 250000000 5945040804881 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352226081/10000000000 : ℝ), (1301534439/2500000000 : ℝ), (-47562643/250000000 : ℝ)] ![(11209287107301/25000000000000 : ℝ), (43272769955837/100000000000000 : ℝ), (5945040804881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352226081/10000000000 : ℝ)|^4639 ≤ (11209287107301/25000000000000 : ℝ)^3615
        have hw : |(5352226081/10000000000 : ℝ)|=(5352226081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301534439/2500000000 : ℝ)|^4639 ≤ (43272769955837/100000000000000 : ℝ)^3615
        have hw : |(1301534439/2500000000 : ℝ)|=(1301534439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47562643/250000000 : ℝ)|^4639 ≤ (5945040804881/50000000000000 : ℝ)^3615
        have hw : |(-47562643/250000000 : ℝ)|=(47562643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s2_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241511221/10000000000 : ℝ)*x 0 + (794246941/2000000000 : ℝ)*x 1 + (2263241557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241511221/10000000000 : ℝ)^4639 ≤ (33266763851701/100000000000000 : ℝ)^3615 := by
    have hnat : (4241511221 : ℕ)^4639*100000000000000^3615 ≤ 33266763851701^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241511221 10000000000 33266763851701 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794246941/2000000000 : ℝ)^4639 ≤ (30571414443247/100000000000000 : ℝ)^3615 := by
    have hnat : (794246941 : ℕ)^4639*100000000000000^3615 ≤ 30571414443247^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794246941 2000000000 30571414443247 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263241557/5000000000 : ℝ)^4639 ≤ (18080910849603/50000000000000 : ℝ)^3615 := by
    have hnat : (2263241557 : ℕ)^4639*50000000000000^3615 ≤ 18080910849603^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263241557 5000000000 18080910849603 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241511221/10000000000 : ℝ), (794246941/2000000000 : ℝ), (2263241557/5000000000 : ℝ)] ![(33266763851701/100000000000000 : ℝ), (30571414443247/100000000000000 : ℝ), (18080910849603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241511221/10000000000 : ℝ)|^4639 ≤ (33266763851701/100000000000000 : ℝ)^3615
        have hw : |(4241511221/10000000000 : ℝ)|=(4241511221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(794246941/2000000000 : ℝ)|^4639 ≤ (30571414443247/100000000000000 : ℝ)^3615
        have hw : |(794246941/2000000000 : ℝ)|=(794246941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263241557/5000000000 : ℝ)|^4639 ≤ (18080910849603/50000000000000 : ℝ)^3615
        have hw : |(2263241557/5000000000 : ℝ)|=(2263241557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s2_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1781904929/10000000000 : ℝ)*x 0 + (2603768867/5000000000 : ℝ)*x 1 + (2719893071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1781904929/10000000000 : ℝ)^4639 ≤ (10931681046421/100000000000000 : ℝ)^3615 := by
    have hnat : (1781904929 : ℕ)^4639*100000000000000^3615 ≤ 10931681046421^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781904929 10000000000 10931681046421 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603768867/5000000000 : ℝ)^4639 ≤ (43287703155147/100000000000000 : ℝ)^3615 := by
    have hnat : (2603768867 : ℕ)^4639*100000000000000^3615 ≤ 43287703155147^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603768867 5000000000 43287703155147 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719893071/5000000000 : ℝ)^4639 ≤ (2289030789151/5000000000000 : ℝ)^3615 := by
    have hnat : (2719893071 : ℕ)^4639*5000000000000^3615 ≤ 2289030789151^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719893071 5000000000 2289030789151 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1781904929/10000000000 : ℝ), (2603768867/5000000000 : ℝ), (2719893071/5000000000 : ℝ)] ![(10931681046421/100000000000000 : ℝ), (43287703155147/100000000000000 : ℝ), (2289030789151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1781904929/10000000000 : ℝ)|^4639 ≤ (10931681046421/100000000000000 : ℝ)^3615
        have hw : |(-1781904929/10000000000 : ℝ)|=(1781904929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603768867/5000000000 : ℝ)|^4639 ≤ (43287703155147/100000000000000 : ℝ)^3615
        have hw : |(2603768867/5000000000 : ℝ)|=(2603768867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719893071/5000000000 : ℝ)|^4639 ≤ (2289030789151/5000000000000 : ℝ)^3615
        have hw : |(2719893071/5000000000 : ℝ)|=(2719893071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s2_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661252797/1250000000 : ℝ)*x 0 + (-834429033/5000000000 : ℝ)*x 1 + (271989353/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661252797/1250000000 : ℝ)^4639 ≤ (8833909048829/20000000000000 : ℝ)^3615 := by
    have hnat : (661252797 : ℕ)^4639*20000000000000^3615 ≤ 8833909048829^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661252797 1250000000 8833909048829 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834429033/5000000000 : ℝ)^4639 ≤ (5024914520569/50000000000000 : ℝ)^3615 := by
    have hnat : (834429033 : ℕ)^4639*50000000000000^3615 ≤ 5024914520569^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834429033 5000000000 5024914520569 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271989353/500000000 : ℝ)^4639 ≤ (1144515642431/2500000000000 : ℝ)^3615 := by
    have hnat : (271989353 : ℕ)^4639*2500000000000^3615 ≤ 1144515642431^3615*500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271989353 500000000 1144515642431 2500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661252797/1250000000 : ℝ), (-834429033/5000000000 : ℝ), (271989353/500000000 : ℝ)] ![(8833909048829/20000000000000 : ℝ), (5024914520569/50000000000000 : ℝ), (1144515642431/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661252797/1250000000 : ℝ)|^4639 ≤ (8833909048829/20000000000000 : ℝ)^3615
        have hw : |(661252797/1250000000 : ℝ)|=(661252797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-834429033/5000000000 : ℝ)|^4639 ≤ (5024914520569/50000000000000 : ℝ)^3615
        have hw : |(-834429033/5000000000 : ℝ)|=(834429033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271989353/500000000 : ℝ)|^4639 ≤ (1144515642431/2500000000000 : ℝ)^3615
        have hw : |(271989353/500000000 : ℝ)|=(271989353/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s2_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322505681/2500000000 : ℝ)*x 0 + (1087957627/2000000000 : ℝ)*x 1 + (-834428041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322505681/2500000000 : ℝ)^4639 ≤ (22084774486437/50000000000000 : ℝ)^3615 := by
    have hnat : (1322505681 : ℕ)^4639*50000000000000^3615 ≤ 22084774486437^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322505681 2500000000 22084774486437 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087957627/2000000000 : ℝ)^4639 ≤ (4578063730703/10000000000000 : ℝ)^3615 := by
    have hnat : (1087957627 : ℕ)^4639*10000000000000^3615 ≤ 4578063730703^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087957627 2000000000 4578063730703 10000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834428041/5000000000 : ℝ)^4639 ≤ (2512453427301/25000000000000 : ℝ)^3615 := by
    have hnat : (834428041 : ℕ)^4639*25000000000000^3615 ≤ 2512453427301^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834428041 5000000000 2512453427301 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322505681/2500000000 : ℝ), (1087957627/2000000000 : ℝ), (-834428041/5000000000 : ℝ)] ![(22084774486437/50000000000000 : ℝ), (4578063730703/10000000000000 : ℝ), (2512453427301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322505681/2500000000 : ℝ)|^4639 ≤ (22084774486437/50000000000000 : ℝ)^3615
        have hw : |(1322505681/2500000000 : ℝ)|=(1322505681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087957627/2000000000 : ℝ)|^4639 ≤ (4578063730703/10000000000000 : ℝ)^3615
        have hw : |(1087957627/2000000000 : ℝ)|=(1087957627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-834428041/5000000000 : ℝ)|^4639 ≤ (2512453427301/25000000000000 : ℝ)^3615
        have hw : |(-834428041/5000000000 : ℝ)|=(834428041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s2_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120802599/5000000000 : ℝ)*x 0 + (90463573/200000000 : ℝ)*x 1 + (3974567467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120802599/5000000000 : ℝ)^4639 ≤ (8316927429061/25000000000000 : ℝ)^3615 := by
    have hnat : (2120802599 : ℕ)^4639*25000000000000^3615 ≤ 8316927429061^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120802599 5000000000 8316927429061 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90463573/200000000 : ℝ)^4639 ≤ (36127948081843/100000000000000 : ℝ)^3615 := by
    have hnat : (90463573 : ℕ)^4639*100000000000000^3615 ≤ 36127948081843^3615*200000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90463573 200000000 36127948081843 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3974567467/10000000000 : ℝ)^4639 ≤ (1224173687429/4000000000000 : ℝ)^3615 := by
    have hnat : (3974567467 : ℕ)^4639*4000000000000^3615 ≤ 1224173687429^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3974567467 10000000000 1224173687429 4000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120802599/5000000000 : ℝ), (90463573/200000000 : ℝ), (3974567467/10000000000 : ℝ)] ![(8316927429061/25000000000000 : ℝ), (36127948081843/100000000000000 : ℝ), (1224173687429/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120802599/5000000000 : ℝ)|^4639 ≤ (8316927429061/25000000000000 : ℝ)^3615
        have hw : |(2120802599/5000000000 : ℝ)|=(2120802599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90463573/200000000 : ℝ)|^4639 ≤ (36127948081843/100000000000000 : ℝ)^3615
        have hw : |(90463573/200000000 : ℝ)|=(90463573/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3974567467/10000000000 : ℝ)|^4639 ≤ (1224173687429/4000000000000 : ℝ)^3615
        have hw : |(3974567467/10000000000 : ℝ)|=(3974567467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (433/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15809/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (9081/100000 : ℝ) ^ (4637/1024 : ℝ) ≤ (9573385888073/500000000000000000 : ℝ) := by
    have hpowers : (9081/100000 : ℝ)^4637 ≤ (9573385888073/500000000000000000 : ℝ)^1024 := by
      have hnat : (9081 : ℕ)^4637*500000000000000000^1024 ≤ 9573385888073^1024*100000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9081 100000 9573385888073 500000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9081/100000 : ℝ)) (X := (9573385888073/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8873/50000 : ℝ) ^ (4637/1024 : ℝ) ≤ (9945495995317363/25000000000000000000 : ℝ) := by
    have hpowers : (8873/50000 : ℝ)^4637 ≤ (9945495995317363/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8873 : ℕ)^4637*25000000000000000000^1024 ≤ 9945495995317363^1024*50000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8873 50000 9945495995317363 25000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8873/50000 : ℝ)) (X := (9945495995317363/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250009573385888073/250000000000000000 : ℝ) ≤ (10000084563303033/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (250009573385888073/250000000000000000 : ℝ)^1024 ≤ (10000084563303033/10000000000000000 : ℝ)^4637 := by
      have hnat : (250009573385888073 : ℕ)^1024*10000000000000000^4637 ≤ 10000084563303033^4637*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250009573385888073 250000000000000000 10000084563303033 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084563303033/10000000000000000 : ℝ)) (X := (250009573385888073/250000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010424165289721013/25000000000000000000 : ℝ) ≤ (2000184129595999/2000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (25010424165289721013/25000000000000000000 : ℝ)^1024 ≤ (2000184129595999/2000000000000000 : ℝ)^4637 := by
      have hnat : (25010424165289721013 : ℕ)^1024*2000000000000000^4637 ≤ 2000184129595999^4637*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010424165289721013 25000000000000000000 2000184129595999 2000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000184129595999/2000000000000000 : ℝ)) (X := (25010424165289721013/25000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509945495995317363/12500000000000000000 : ℝ) ≤ (10001756732656957/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (12509945495995317363/12500000000000000000 : ℝ)^1024 ≤ (10001756732656957/10000000000000000 : ℝ)^4637 := by
      have hnat : (12509945495995317363 : ℕ)^1024*10000000000000000^4637 ≤ 10001756732656957^4637*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509945495995317363 12500000000000000000 10001756732656957 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001756732656957/10000000000000000 : ℝ)) (X := (12509945495995317363/12500000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9573385888073/500000000000000000 : ℝ) ≤ ((86635547771117797101/86650000000000000000 : ℝ)+2*(418042338481/433250000000000 : ℝ)*(9081/100000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (86635547771117797101/86650000000000000000 : ℝ)+2*(418042338481/433250000000000 : ℝ)*(9081/100000 : ℝ)=(10000084563303033/10000000000000000 : ℝ) by norm_num, show 1+2*(9573385888073/500000000000000000 : ℝ)=(250009573385888073/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9945495995317363/25000000000000000000 : ℝ)+(9573385888073/500000000000000000 : ℝ) ≤ ((86635547771117797101/86650000000000000000 : ℝ)+(418042338481/433250000000000 : ℝ)*((8873/50000 : ℝ)+(9081/100000 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (86635547771117797101/86650000000000000000 : ℝ)+(418042338481/433250000000000 : ℝ)*((8873/50000 : ℝ)+(9081/100000 : ℝ))=(2000184129595999/2000000000000000 : ℝ) by norm_num, show 1+(9945495995317363/25000000000000000000 : ℝ)+(9573385888073/500000000000000000 : ℝ)=(25010424165289721013/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9945495995317363/25000000000000000000 : ℝ) ≤ ((86635547771117797101/86650000000000000000 : ℝ)+2*(418042338481/433250000000000 : ℝ)*(8873/50000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (86635547771117797101/86650000000000000000 : ℝ)+2*(418042338481/433250000000000 : ℝ)*(8873/50000 : ℝ)=(10001756732656957/10000000000000000 : ℝ) by norm_num, show 1+2*(9945495995317363/25000000000000000000 : ℝ)=(12509945495995317363/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (86635547771117797101/86650000000000000000 : ℝ)*(X 1 0+X 2 0)+(418042338481/433250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (9081/100000 : ℝ)) (hi := (8873/50000 : ℝ)) (c := (86635547771117797101/86650000000000000000 : ℝ)) (alpha := (418042338481/433250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (86635547771117797101/86650000000000000000 : ℝ)*(X 0 1+X 2 1)+(418042338481/433250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (9081/100000 : ℝ)) (hi := (8873/50000 : ℝ)) (c := (86635547771117797101/86650000000000000000 : ℝ)) (alpha := (418042338481/433250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (86635547771117797101/86650000000000000000 : ℝ)*(X 0 2+X 1 2)+(418042338481/433250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (9081/100000 : ℝ)) (hi := (8873/50000 : ℝ)) (c := (86635547771117797101/86650000000000000000 : ℝ)) (alpha := (418042338481/433250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-890932619/5000000000 : ℝ)*X 0 0+(5441196831/10000000000 : ℝ)*X 0 1+(5206138689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167257049/312500000 : ℝ)*X 1 0+(-1902505851/10000000000 : ℝ)*X 1 1+(2603069087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352226081/10000000000 : ℝ)*X 2 0+(1301534439/2500000000 : ℝ)*X 2 1+(-47562643/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4241511221/10000000000 : ℝ)*X 0 0+(794246941/2000000000 : ℝ)*X 0 1+(2263241557/5000000000 : ℝ)*X 0 2+(4241511221/10000000000 : ℝ)*X 1 0+(794246941/2000000000 : ℝ)*X 1 1+(2263241557/5000000000 : ℝ)*X 1 2+(4241511221/10000000000 : ℝ)*X 2 0+(794246941/2000000000 : ℝ)*X 2 1+(2263241557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1781904929/10000000000 : ℝ)*X 0 0+(2603768867/5000000000 : ℝ)*X 0 1+(2719893071/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661252797/1250000000 : ℝ)*X 1 0+(-834429033/5000000000 : ℝ)*X 1 1+(271989353/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322505681/2500000000 : ℝ)*X 2 0+(1087957627/2000000000 : ℝ)*X 2 1+(-834428041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120802599/5000000000 : ℝ)*X 0 0+(90463573/200000000 : ℝ)*X 0 1+(3974567467/10000000000 : ℝ)*X 0 2+(2120802599/5000000000 : ℝ)*X 1 0+(90463573/200000000 : ℝ)*X 1 1+(3974567467/10000000000 : ℝ)*X 1 2+(2120802599/5000000000 : ℝ)*X 2 0+(90463573/200000000 : ℝ)*X 2 1+(3974567467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6320037693698832793231959729/541562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1588553423/100000000000000 : ℝ)*(base19) + (1612213781/100000000000000 : ℝ)*(base23) + (205581507/100000000000000 : ℝ)*(lower2) + (221233151/100000000000000 : ℝ)*(upper3) + (22950301/20000000000000 : ℝ)*(upper5) + (378456350183481/12500000000000 : ℝ)*(major0) + (378456350183481/12500000000000 : ℝ)*(major1) + (378456350183481/12500000000000 : ℝ)*(major2) + (2127138809615957/50000000000000 : ℝ)*(sp0) + (1063572444486513/25000000000000 : ℝ)*(sp1) + (2127144877142847/50000000000000 : ℝ)*(sp2) + (450250305895363/25000000000000 : ℝ)*(sp3) + (343681689/2500000000000 : ℝ)*(sp4) + (8623854557/100000000000000 : ℝ)*(sp7) + (225126230929501/12500000000000 : ℝ)*(f.failure) + (170171654659979/4000000000000 : ℝ)*(f.sum) + (44093483923587/21662500000000000000000000000 : ℝ)*base66 + (10378159815880411419/1083125000000000000000000000000000 : ℝ)*base68 + (4358367289041036419/1083125000000000000000000000000000 : ℝ)*base70 + (6934195376624161419/1083125000000000000000000000000000 : ℝ)*base72 + (127318600475037/21662500000000000000000000000 : ℝ)*base74 + (8080758987294786419/1083125000000000000000000000000000 : ℝ)*base76 + (7923010167857911419/1083125000000000000000000000000000 : ℝ)*base78 + (11611935686486661419/1083125000000000000000000000000000 : ℝ)*base80 + (121753956822501/43325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2775991/1250000000000000000000 : ℝ)*base90 + (2775991/1250000000000000000000 : ℝ)*base92 + (2775991/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23588476745063998848526370577/2166250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226735133/100000000000000 : ℝ)*(base15) + (244333667/100000000000000 : ℝ)*(lower2) + (120918929/100000000000000 : ℝ)*(upper3) + (413151/25000000000000 : ℝ)*(upper4) + (1532131524087959/50000000000000 : ℝ)*(major0) + (1532131524087959/50000000000000 : ℝ)*(major1) + (1532131524087959/50000000000000 : ℝ)*(major2) + (6463058351/100000000000000 : ℝ)*(sp1) + (39088027089/100000000000000 : ℝ)*(sp2) + (508193329/100000000000000 : ℝ)*(sp3) + (269108559292741/6250000000000 : ℝ)*(sp4) + (1076432564722593/25000000000000 : ℝ)*(sp5) + (4305697860656767/100000000000000 : ℝ)*(sp6) + (4556970691263/250000000000 : ℝ)*(sp7) + (182278878469853/10000000000000 : ℝ)*(f.failure) + (269108559292741/6250000000000 : ℝ)*(f.sum) + (54594592018491/43325000000000000000000000000 : ℝ)*base65 + (373986038997493141/4332500000000000000000000000000000 : ℝ)*base68 + (3492279733010006859/4332500000000000000000000000000000 : ℝ)*base69 + (60638070196247493141/4332500000000000000000000000000000 : ℝ)*base72 + (24919754321277/5415625000000000000000000000 : ℝ)*base73 + (7282014537454993141/4332500000000000000000000000000000 : ℝ)*base76 + (13264779063849993141/4332500000000000000000000000000000 : ℝ)*base78 + (7116431943940006859/4332500000000000000000000000000000 : ℝ)*base79 + (70980177803473/5415625000000000000000000000 : ℝ)*base82 + (9279177/1000000000000000000000 : ℝ)*base89 + (9279177/1000000000000000000000 : ℝ)*base91 + (9279177/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1571_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1571_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1571_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1571_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1571_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1571_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
