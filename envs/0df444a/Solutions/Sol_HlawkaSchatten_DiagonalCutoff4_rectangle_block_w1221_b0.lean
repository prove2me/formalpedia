-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:10:40.963994+00:00
-- url     : https://prove2.me/submissions/cfb5e07f-8361-48fe-914d-732b91d8a001

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
theorem support_rectangle_w1221_s0_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-933528553/5000000000 : ℝ)*x 0 + (6036250897/10000000000 : ℝ)*x 1 + (4790381583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933528553/5000000000 : ℝ)^4207 ≤ (2720335024319/25000000000000 : ℝ)^3183 := by
    have hnat : (933528553 : ℕ)^4207*25000000000000^3183 ≤ 2720335024319^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933528553 5000000000 2720335024319 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6036250897/10000000000 : ℝ)^4207 ≤ (51314266734729/100000000000000 : ℝ)^3183 := by
    have hnat : (6036250897 : ℕ)^4207*100000000000000^3183 ≤ 51314266734729^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036250897 10000000000 51314266734729 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790381583/10000000000 : ℝ)^4207 ≤ (37804393147683/100000000000000 : ℝ)^3183 := by
    have hnat : (4790381583 : ℕ)^4207*100000000000000^3183 ≤ 37804393147683^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790381583 10000000000 37804393147683 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933528553/5000000000 : ℝ), (6036250897/10000000000 : ℝ), (4790381583/10000000000 : ℝ)] ![(2720335024319/25000000000000 : ℝ), (51314266734729/100000000000000 : ℝ), (37804393147683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933528553/5000000000 : ℝ)|^4207 ≤ (2720335024319/25000000000000 : ℝ)^3183
        have hw : |(-933528553/5000000000 : ℝ)|=(933528553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6036250897/10000000000 : ℝ)|^4207 ≤ (51314266734729/100000000000000 : ℝ)^3183
        have hw : |(6036250897/10000000000 : ℝ)|=(6036250897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4790381583/10000000000 : ℝ)|^4207 ≤ (37804393147683/100000000000000 : ℝ)^3183
        have hw : |(4790381583/10000000000 : ℝ)|=(4790381583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s0_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (551234261/1000000000 : ℝ)*x 0 + (-2579860757/10000000000 : ℝ)*x 1 + (598797693/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551234261/1000000000 : ℝ)^4207 ≤ (2844472423383/6250000000000 : ℝ)^3183 := by
    have hnat : (551234261 : ℕ)^4207*6250000000000^3183 ≤ 2844472423383^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551234261 1000000000 2844472423383 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2579860757/10000000000 : ℝ)^4207 ≤ (16684048470391/100000000000000 : ℝ)^3183 := by
    have hnat : (2579860757 : ℕ)^4207*100000000000000^3183 ≤ 16684048470391^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579860757 10000000000 16684048470391 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598797693/1250000000 : ℝ)^4207 ≤ (37804392740891/100000000000000 : ℝ)^3183 := by
    have hnat : (598797693 : ℕ)^4207*100000000000000^3183 ≤ 37804392740891^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598797693 1250000000 37804392740891 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551234261/1000000000 : ℝ), (-2579860757/10000000000 : ℝ), (598797693/1250000000 : ℝ)] ![(2844472423383/6250000000000 : ℝ), (16684048470391/100000000000000 : ℝ), (37804392740891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551234261/1000000000 : ℝ)|^4207 ≤ (2844472423383/6250000000000 : ℝ)^3183
        have hw : |(551234261/1000000000 : ℝ)|=(551234261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2579860757/10000000000 : ℝ)|^4207 ≤ (16684048470391/100000000000000 : ℝ)^3183
        have hw : |(-2579860757/10000000000 : ℝ)|=(2579860757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598797693/1250000000 : ℝ)|^4207 ≤ (37804392740891/100000000000000 : ℝ)^3183
        have hw : |(598797693/1250000000 : ℝ)|=(598797693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s0_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (275617129/500000000 : ℝ)*x 0 + (2395190791/5000000000 : ℝ)*x 1 + (-2579860749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275617129/500000000 : ℝ)^4207 ≤ (9102311689351/20000000000000 : ℝ)^3183 := by
    have hnat : (275617129 : ℕ)^4207*20000000000000^3183 ≤ 9102311689351^3183*500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275617129 500000000 9102311689351 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2395190791/5000000000 : ℝ)^4207 ≤ (9451098284313/25000000000000 : ℝ)^3183 := by
    have hnat : (2395190791 : ℕ)^4207*25000000000000^3183 ≤ 9451098284313^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395190791 5000000000 9451098284313 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579860749/10000000000 : ℝ)^4207 ≤ (16684048402011/100000000000000 : ℝ)^3183 := by
    have hnat : (2579860749 : ℕ)^4207*100000000000000^3183 ≤ 16684048402011^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579860749 10000000000 16684048402011 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275617129/500000000 : ℝ), (2395190791/5000000000 : ℝ), (-2579860749/10000000000 : ℝ)] ![(9102311689351/20000000000000 : ℝ), (9451098284313/25000000000000 : ℝ), (16684048402011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275617129/500000000 : ℝ)|^4207 ≤ (9102311689351/20000000000000 : ℝ)^3183
        have hw : |(275617129/500000000 : ℝ)|=(275617129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2395190791/5000000000 : ℝ)|^4207 ≤ (9451098284313/25000000000000 : ℝ)^3183
        have hw : |(2395190791/5000000000 : ℝ)|=(2395190791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2579860749/10000000000 : ℝ)|^4207 ≤ (16684048402011/100000000000000 : ℝ)^3183
        have hw : |(-2579860749/10000000000 : ℝ)|=(2579860749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s0_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097337931/5000000000 : ℝ)*x 0 + (779424417/2500000000 : ℝ)*x 1 + (112695747/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097337931/5000000000 : ℝ)^4207 ≤ (15859411328057/50000000000000 : ℝ)^3183 := by
    have hnat : (2097337931 : ℕ)^4207*50000000000000^3183 ≤ 15859411328057^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097337931 5000000000 15859411328057 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779424417/2500000000 : ℝ)^4207 ≤ (1071434937817/5000000000000 : ℝ)^3183 := by
    have hnat : (779424417 : ℕ)^4207*5000000000000^3183 ≤ 1071434937817^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779424417 2500000000 1071434937817 5000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112695747/200000000 : ℝ)^4207 ≤ (46852478575951/100000000000000 : ℝ)^3183 := by
    have hnat : (112695747 : ℕ)^4207*100000000000000^3183 ≤ 46852478575951^3183*200000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112695747 200000000 46852478575951 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097337931/5000000000 : ℝ), (779424417/2500000000 : ℝ), (112695747/200000000 : ℝ)] ![(15859411328057/50000000000000 : ℝ), (1071434937817/5000000000000 : ℝ), (46852478575951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097337931/5000000000 : ℝ)|^4207 ≤ (15859411328057/50000000000000 : ℝ)^3183
        have hw : |(2097337931/5000000000 : ℝ)|=(2097337931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779424417/2500000000 : ℝ)|^4207 ≤ (1071434937817/5000000000000 : ℝ)^3183
        have hw : |(779424417/2500000000 : ℝ)|=(779424417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112695747/200000000 : ℝ)|^4207 ≤ (46852478575951/100000000000000 : ℝ)^3183
        have hw : |(112695747/200000000 : ℝ)|=(112695747/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s0_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871974677/10000000000 : ℝ)*x 0 + (301404919/625000000 : ℝ)*x 1 + (3001509969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871974677/10000000000 : ℝ)^4207 ≤ (10919236251913/100000000000000 : ℝ)^3183 := by
    have hnat : (1871974677 : ℕ)^4207*100000000000000^3183 ≤ 10919236251913^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871974677 10000000000 10919236251913 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301404919/625000000 : ℝ)^4207 ≤ (9534886173879/25000000000000 : ℝ)^3183 := by
    have hnat : (301404919 : ℕ)^4207*25000000000000^3183 ≤ 9534886173879^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301404919 625000000 9534886173879 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3001509969/5000000000 : ℝ)^4207 ≤ (1591913095123/3125000000000 : ℝ)^3183 := by
    have hnat : (3001509969 : ℕ)^4207*3125000000000^3183 ≤ 1591913095123^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001509969 5000000000 1591913095123 3125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871974677/10000000000 : ℝ), (301404919/625000000 : ℝ), (3001509969/5000000000 : ℝ)] ![(10919236251913/100000000000000 : ℝ), (9534886173879/25000000000000 : ℝ), (1591913095123/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871974677/10000000000 : ℝ)|^4207 ≤ (10919236251913/100000000000000 : ℝ)^3183
        have hw : |(-1871974677/10000000000 : ℝ)|=(1871974677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301404919/625000000 : ℝ)|^4207 ≤ (9534886173879/25000000000000 : ℝ)^3183
        have hw : |(301404919/625000000 : ℝ)|=(301404919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3001509969/5000000000 : ℝ)|^4207 ≤ (1591913095123/3125000000000 : ℝ)^3183
        have hw : |(3001509969/5000000000 : ℝ)|=(3001509969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s0_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173449637/10000000000 : ℝ)*x 0 + (-341805139/2500000000 : ℝ)*x 1 + (1200604363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173449637/10000000000 : ℝ)^4207 ≤ (41850507177927/100000000000000 : ℝ)^3183 := by
    have hnat : (5173449637 : ℕ)^4207*100000000000000^3183 ≤ 41850507177927^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173449637 10000000000 41850507177927 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341805139/2500000000 : ℝ)^4207 ≤ (1802063178489/25000000000000 : ℝ)^3183 := by
    have hnat : (341805139 : ℕ)^4207*25000000000000^3183 ≤ 1802063178489^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341805139 2500000000 1802063178489 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200604363/2000000000 : ℝ)^4207 ≤ (12735310024061/25000000000000 : ℝ)^3183 := by
    have hnat : (1200604363 : ℕ)^4207*25000000000000^3183 ≤ 12735310024061^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200604363 2000000000 12735310024061 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173449637/10000000000 : ℝ), (-341805139/2500000000 : ℝ), (1200604363/2000000000 : ℝ)] ![(41850507177927/100000000000000 : ℝ), (1802063178489/25000000000000 : ℝ), (12735310024061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173449637/10000000000 : ℝ)|^4207 ≤ (41850507177927/100000000000000 : ℝ)^3183
        have hw : |(5173449637/10000000000 : ℝ)|=(5173449637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341805139/2500000000 : ℝ)|^4207 ≤ (1802063178489/25000000000000 : ℝ)^3183
        have hw : |(-341805139/2500000000 : ℝ)|=(341805139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200604363/2000000000 : ℝ)|^4207 ≤ (12735310024061/25000000000000 : ℝ)^3183
        have hw : |(1200604363/2000000000 : ℝ)|=(1200604363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s0_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1293362649/2500000000 : ℝ)*x 0 + (300151019/500000000 : ℝ)*x 1 + (-683610697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293362649/2500000000 : ℝ)^4207 ≤ (20925258715747/50000000000000 : ℝ)^3183 := by
    have hnat : (1293362649 : ℕ)^4207*50000000000000^3183 ≤ 20925258715747^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293362649 2500000000 20925258715747 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300151019/500000000 : ℝ)^4207 ≤ (50941224001379/100000000000000 : ℝ)^3183 := by
    have hnat : (300151019 : ℕ)^4207*100000000000000^3183 ≤ 50941224001379^3183*500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300151019 500000000 50941224001379 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683610697/5000000000 : ℝ)^4207 ≤ (7208258553399/100000000000000 : ℝ)^3183 := by
    have hnat : (683610697 : ℕ)^4207*100000000000000^3183 ≤ 7208258553399^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683610697 5000000000 7208258553399 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293362649/2500000000 : ℝ), (300151019/500000000 : ℝ), (-683610697/5000000000 : ℝ)] ![(20925258715747/50000000000000 : ℝ), (50941224001379/100000000000000 : ℝ), (7208258553399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293362649/2500000000 : ℝ)|^4207 ≤ (20925258715747/50000000000000 : ℝ)^3183
        have hw : |(1293362649/2500000000 : ℝ)|=(1293362649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300151019/500000000 : ℝ)|^4207 ≤ (50941224001379/100000000000000 : ℝ)^3183
        have hw : |(300151019/500000000 : ℝ)|=(300151019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683610697/5000000000 : ℝ)|^4207 ≤ (7208258553399/100000000000000 : ℝ)^3183
        have hw : |(-683610697/5000000000 : ℝ)|=(683610697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s0_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102305137/5000000000 : ℝ)*x 0 + (2784972179/5000000000 : ℝ)*x 1 + (3184830431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102305137/5000000000 : ℝ)^4207 ≤ (7954537111089/25000000000000 : ℝ)^3183 := by
    have hnat : (2102305137 : ℕ)^4207*25000000000000^3183 ≤ 7954537111089^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102305137 5000000000 7954537111089 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2784972179/5000000000 : ℝ)^4207 ≤ (23070593875717/50000000000000 : ℝ)^3183 := by
    have hnat : (2784972179 : ℕ)^4207*50000000000000^3183 ≤ 23070593875717^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784972179 5000000000 23070593875717 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184830431/10000000000 : ℝ)^4207 ≤ (5510165947507/25000000000000 : ℝ)^3183 := by
    have hnat : (3184830431 : ℕ)^4207*25000000000000^3183 ≤ 5510165947507^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184830431 10000000000 5510165947507 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102305137/5000000000 : ℝ), (2784972179/5000000000 : ℝ), (3184830431/10000000000 : ℝ)] ![(7954537111089/25000000000000 : ℝ), (23070593875717/50000000000000 : ℝ), (5510165947507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102305137/5000000000 : ℝ)|^4207 ≤ (7954537111089/25000000000000 : ℝ)^3183
        have hw : |(2102305137/5000000000 : ℝ)|=(2102305137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2784972179/5000000000 : ℝ)|^4207 ≤ (23070593875717/50000000000000 : ℝ)^3183
        have hw : |(2784972179/5000000000 : ℝ)|=(2784972179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184830431/10000000000 : ℝ)|^4207 ≤ (5510165947507/25000000000000 : ℝ)^3183
        have hw : |(3184830431/10000000000 : ℝ)|=(3184830431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (367/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5503/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8413/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8413 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8413*1^2048 ≤ 0^2048*1^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8413/2048 : ℝ) ≤ (1159493186996417597/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8413 ≤ (1159493186996417597/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8413*50000000000000000000^2048 ≤ 1159493186996417597^2048*5^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1159493186996417597 50000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1159493186996417597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8413 := by
      have hnat : (1 : ℕ)^2048*1^8413 ≤ 1^8413*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51159493186996417597/50000000000000000000 : ℝ) ≤ (10055963134995141/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (51159493186996417597/50000000000000000000 : ℝ)^2048 ≤ (10055963134995141/10000000000000000 : ℝ)^8413 := by
      have hnat : (51159493186996417597 : ℕ)^2048*10000000000000000^8413 ≤ 10055963134995141^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51159493186996417597 50000000000000000000 10055963134995141 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055963134995141/10000000000000000 : ℝ)) (X := (51159493186996417597/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26159493186996417597/25000000000000000000 : ℝ) ≤ (5055963134995141/5000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (26159493186996417597/25000000000000000000 : ℝ)^2048 ≤ (5055963134995141/5000000000000000 : ℝ)^8413 := by
      have hnat : (26159493186996417597 : ℕ)^2048*5000000000000000^8413 ≤ 5055963134995141^8413*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26159493186996417597 25000000000000000000 5055963134995141 5000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055963134995141/5000000000000000 : ℝ)) (X := (26159493186996417597/25000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55963134995141/4000000000000000 : ℝ)*(0 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55963134995141/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1159493186996417597/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55963134995141/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55963134995141/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055963134995141/10000000000000000 : ℝ) by norm_num, show 1+(1159493186996417597/50000000000000000000 : ℝ)+(0 : ℝ)=(51159493186996417597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1159493186996417597/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55963134995141/4000000000000000 : ℝ)*(2/5 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55963134995141/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055963134995141/5000000000000000 : ℝ) by norm_num, show 1+2*(1159493186996417597/50000000000000000000 : ℝ)=(26159493186996417597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55963134995141/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55963134995141/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55963134995141/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55963134995141/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55963134995141/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55963134995141/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-933528553/5000000000 : ℝ)*X 0 0+(6036250897/10000000000 : ℝ)*X 0 1+(4790381583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((551234261/1000000000 : ℝ)*X 1 0+(-2579860757/10000000000 : ℝ)*X 1 1+(598797693/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((275617129/500000000 : ℝ)*X 2 0+(2395190791/5000000000 : ℝ)*X 2 1+(-2579860749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2097337931/5000000000 : ℝ)*X 0 0+(779424417/2500000000 : ℝ)*X 0 1+(112695747/200000000 : ℝ)*X 0 2+(2097337931/5000000000 : ℝ)*X 1 0+(779424417/2500000000 : ℝ)*X 1 1+(112695747/200000000 : ℝ)*X 1 2+(2097337931/5000000000 : ℝ)*X 2 0+(779424417/2500000000 : ℝ)*X 2 1+(112695747/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1871974677/10000000000 : ℝ)*X 0 0+(301404919/625000000 : ℝ)*X 0 1+(3001509969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173449637/10000000000 : ℝ)*X 1 0+(-341805139/2500000000 : ℝ)*X 1 1+(1200604363/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293362649/2500000000 : ℝ)*X 2 0+(300151019/500000000 : ℝ)*X 2 1+(-683610697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102305137/5000000000 : ℝ)*X 0 0+(2784972179/5000000000 : ℝ)*X 0 1+(3184830431/10000000000 : ℝ)*X 0 2+(2102305137/5000000000 : ℝ)*X 1 0+(2784972179/5000000000 : ℝ)*X 1 1+(3184830431/10000000000 : ℝ)*X 1 2+(2102305137/5000000000 : ℝ)*X 2 0+(2784972179/5000000000 : ℝ)*X 2 1+(3184830431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65329981481674760158023/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74903059/100000000000000 : ℝ)*(base1) + (319265911/20000000000000 : ℝ)*(base19) + (741390163/50000000000000 : ℝ)*(base23) + (13647611/12500000000000 : ℝ)*(base24) + (363453751/100000000000000 : ℝ)*(upper3) + (119995018293799/20000000000000 : ℝ)*(major0) + (119995018293799/20000000000000 : ℝ)*(major1) + (119995018293799/20000000000000 : ℝ)*(major2) + (160531560935567/20000000000000 : ℝ)*(sp0) + (200664918128877/25000000000000 : ℝ)*(sp1) + (100332459610481/12500000000000 : ℝ)*(sp2) + (397285841522263/100000000000000 : ℝ)*(sp3) + (3539070287/100000000000000 : ℝ)*(sp4) + (1389950497/50000000000000 : ℝ)*(sp7) + (397288696326317/100000000000000 : ℝ)*(f.failure) + (401330634422531/50000000000000 : ℝ)*(f.sum) + (97211565310659/40000000000000000000000000000 : ℝ)*base65 + (465129110659/80000000000000000000000000000 : ℝ)*base67 + (284840657430659/80000000000000000000000000000 : ℝ)*base69 + (84783939929341/80000000000000000000000000000 : ℝ)*base72 + (139667776230659/40000000000000000000000000000 : ℝ)*base73 + (251182489849341/80000000000000000000000000000 : ℝ)*base76 + (202379903270659/80000000000000000000000000000 : ℝ)*base77 + (537981009670659/80000000000000000000000000000 : ℝ)*base79 + (244632402950659/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (242599/156250000000000000000 : ℝ)*base89 + (242599/156250000000000000000 : ℝ)*base91 + (242599/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (474892022123990280030441/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483427/100000000000000 : ℝ)*(base1) + (345458431/25000000000000 : ℝ)*(base19) + (780865867/50000000000000 : ℝ)*(base23) + (325764173/100000000000000 : ℝ)*(upper3) + (12264619/50000000000000 : ℝ)*(upper5) + (633167780242233/100000000000000 : ℝ)*(major0) + (633167780242233/100000000000000 : ℝ)*(major1) + (633167780242233/100000000000000 : ℝ)*(major2) + (12708009/400000000000 : ℝ)*(sp1) + (3526259169/100000000000000 : ℝ)*(sp2) + (847067327137009/100000000000000 : ℝ)*(sp4) + (847062767817609/100000000000000 : ℝ)*(sp5) + (847062238662679/100000000000000 : ℝ)*(sp6) + (3275531836329/781250000000 : ℝ)*(sp7) + (419268075533539/100000000000000 : ℝ)*(f.failure) + (423533663326791/50000000000000 : ℝ)*(f.sum) + (211330338989853/200000000000000000000000000000 : ℝ)*base65 + (981933514810147/400000000000000000000000000000 : ℝ)*base68 + (1842938772389853/400000000000000000000000000000 : ℝ)*base69 + (542163809589853/400000000000000000000000000000 : ℝ)*base71 + (532642590410147/200000000000000000000000000000 : ℝ)*base74 + (929032784810147/400000000000000000000000000000 : ℝ)*base76 + (1739966901189853/400000000000000000000000000000 : ℝ)*base77 + (887719668389853/400000000000000000000000000000 : ℝ)*base79 + (62847024989853/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (361767/156250000000000000000 : ℝ)*base90 + (361767/156250000000000000000 : ℝ)*base92 + (361767/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1221_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (367/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5503/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1221_s1_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065995187/10000000000 : ℝ)*x 0 + (355056977/625000000 : ℝ)*x 1 + (1003675517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065995187/10000000000 : ℝ)^4207 ≤ (2487884305339/20000000000000 : ℝ)^3183 := by
    have hnat : (2065995187 : ℕ)^4207*20000000000000^3183 ≤ 2487884305339^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065995187 10000000000 2487884305339 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355056977/625000000 : ℝ)^4207 ≤ (23680021360919/50000000000000 : ℝ)^3183 := by
    have hnat : (355056977 : ℕ)^4207*50000000000000^3183 ≤ 23680021360919^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355056977 625000000 23680021360919 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003675517/2000000000 : ℝ)^4207 ≤ (40200535734477/100000000000000 : ℝ)^3183 := by
    have hnat : (1003675517 : ℕ)^4207*100000000000000^3183 ≤ 40200535734477^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003675517 2000000000 40200535734477 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065995187/10000000000 : ℝ), (355056977/625000000 : ℝ), (1003675517/2000000000 : ℝ)] ![(2487884305339/20000000000000 : ℝ), (23680021360919/50000000000000 : ℝ), (40200535734477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065995187/10000000000 : ℝ)|^4207 ≤ (2487884305339/20000000000000 : ℝ)^3183
        have hw : |(-2065995187/10000000000 : ℝ)|=(2065995187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355056977/625000000 : ℝ)|^4207 ≤ (23680021360919/50000000000000 : ℝ)^3183
        have hw : |(355056977/625000000 : ℝ)|=(355056977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003675517/2000000000 : ℝ)|^4207 ≤ (40200535734477/100000000000000 : ℝ)^3183
        have hw : |(1003675517/2000000000 : ℝ)|=(1003675517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s1_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5414800551/10000000000 : ℝ)*x 0 + (-2422129753/10000000000 : ℝ)*x 1 + (5018377617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414800551/10000000000 : ℝ)^4207 ≤ (8890036006817/20000000000000 : ℝ)^3183 := by
    have hnat : (5414800551 : ℕ)^4207*20000000000000^3183 ≤ 8890036006817^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414800551 10000000000 8890036006817 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422129753/10000000000 : ℝ)^4207 ≤ (1918660485237/12500000000000 : ℝ)^3183 := by
    have hnat : (2422129753 : ℕ)^4207*12500000000000^3183 ≤ 1918660485237^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422129753 10000000000 1918660485237 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5018377617/10000000000 : ℝ)^4207 ≤ (8040107214657/20000000000000 : ℝ)^3183 := by
    have hnat : (5018377617 : ℕ)^4207*20000000000000^3183 ≤ 8040107214657^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018377617 10000000000 8040107214657 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414800551/10000000000 : ℝ), (-2422129753/10000000000 : ℝ), (5018377617/10000000000 : ℝ)] ![(8890036006817/20000000000000 : ℝ), (1918660485237/12500000000000 : ℝ), (8040107214657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414800551/10000000000 : ℝ)|^4207 ≤ (8890036006817/20000000000000 : ℝ)^3183
        have hw : |(5414800551/10000000000 : ℝ)|=(5414800551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2422129753/10000000000 : ℝ)|^4207 ≤ (1918660485237/12500000000000 : ℝ)^3183
        have hw : |(-2422129753/10000000000 : ℝ)|=(2422129753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5018377617/10000000000 : ℝ)|^4207 ≤ (8040107214657/20000000000000 : ℝ)^3183
        have hw : |(5018377617/10000000000 : ℝ)|=(5018377617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s1_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707400277/5000000000 : ℝ)*x 0 + (2509188803/5000000000 : ℝ)*x 1 + (-1211064881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707400277/5000000000 : ℝ)^4207 ≤ (22225090033317/50000000000000 : ℝ)^3183 := by
    have hnat : (2707400277 : ℕ)^4207*50000000000000^3183 ≤ 22225090033317^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707400277 5000000000 22225090033317 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509188803/5000000000 : ℝ)^4207 ≤ (2010026797841/5000000000000 : ℝ)^3183 := by
    have hnat : (2509188803 : ℕ)^4207*5000000000000^3183 ≤ 2010026797841^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509188803 5000000000 2010026797841 5000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211064881/5000000000 : ℝ)^4207 ≤ (7674641978639/50000000000000 : ℝ)^3183 := by
    have hnat : (1211064881 : ℕ)^4207*50000000000000^3183 ≤ 7674641978639^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211064881 5000000000 7674641978639 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707400277/5000000000 : ℝ), (2509188803/5000000000 : ℝ), (-1211064881/5000000000 : ℝ)] ![(22225090033317/50000000000000 : ℝ), (2010026797841/5000000000000 : ℝ), (7674641978639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707400277/5000000000 : ℝ)|^4207 ≤ (22225090033317/50000000000000 : ℝ)^3183
        have hw : |(2707400277/5000000000 : ℝ)|=(2707400277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509188803/5000000000 : ℝ)|^4207 ≤ (2010026797841/5000000000000 : ℝ)^3183
        have hw : |(2509188803/5000000000 : ℝ)|=(2509188803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1211064881/5000000000 : ℝ)|^4207 ≤ (7674641978639/50000000000000 : ℝ)^3183
        have hw : |(-1211064881/5000000000 : ℝ)|=(1211064881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s1_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269417153/625000000 : ℝ)*x 0 + (922910253/2500000000 : ℝ)*x 1 + (5030190307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269417153/625000000 : ℝ)^4207 ≤ (32883278144227/100000000000000 : ℝ)^3183 := by
    have hnat : (269417153 : ℕ)^4207*100000000000000^3183 ≤ 32883278144227^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269417153 625000000 32883278144227 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922910253/2500000000 : ℝ)^4207 ≤ (13395534214497/50000000000000 : ℝ)^3183 := by
    have hnat : (922910253 : ℕ)^4207*50000000000000^3183 ≤ 13395534214497^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922910253 2500000000 13395534214497 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5030190307/10000000000 : ℝ)^4207 ≤ (8065130682911/20000000000000 : ℝ)^3183 := by
    have hnat : (5030190307 : ℕ)^4207*20000000000000^3183 ≤ 8065130682911^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030190307 10000000000 8065130682911 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269417153/625000000 : ℝ), (922910253/2500000000 : ℝ), (5030190307/10000000000 : ℝ)] ![(32883278144227/100000000000000 : ℝ), (13395534214497/50000000000000 : ℝ), (8065130682911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269417153/625000000 : ℝ)|^4207 ≤ (32883278144227/100000000000000 : ℝ)^3183
        have hw : |(269417153/625000000 : ℝ)|=(269417153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922910253/2500000000 : ℝ)|^4207 ≤ (13395534214497/50000000000000 : ℝ)^3183
        have hw : |(922910253/2500000000 : ℝ)|=(922910253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5030190307/10000000000 : ℝ)|^4207 ≤ (8065130682911/20000000000000 : ℝ)^3183
        have hw : |(5030190307/10000000000 : ℝ)|=(5030190307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s1_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066693199/10000000000 : ℝ)*x 0 + (628393737/1250000000 : ℝ)*x 1 + (1134394721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066693199/10000000000 : ℝ)^4207 ≤ (3111244161023/25000000000000 : ℝ)^3183 := by
    have hnat : (2066693199 : ℕ)^4207*25000000000000^3183 ≤ 3111244161023^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066693199 10000000000 3111244161023 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628393737/1250000000 : ℝ)^4207 ≤ (40293441025687/100000000000000 : ℝ)^3183 := by
    have hnat : (628393737 : ℕ)^4207*100000000000000^3183 ≤ 40293441025687^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628393737 1250000000 40293441025687 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134394721/2000000000 : ℝ)^4207 ≤ (9452316463121/20000000000000 : ℝ)^3183 := by
    have hnat : (1134394721 : ℕ)^4207*20000000000000^3183 ≤ 9452316463121^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134394721 2000000000 9452316463121 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066693199/10000000000 : ℝ), (628393737/1250000000 : ℝ), (1134394721/2000000000 : ℝ)] ![(3111244161023/25000000000000 : ℝ), (40293441025687/100000000000000 : ℝ), (9452316463121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066693199/10000000000 : ℝ)|^4207 ≤ (3111244161023/25000000000000 : ℝ)^3183
        have hw : |(-2066693199/10000000000 : ℝ)|=(2066693199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(628393737/1250000000 : ℝ)|^4207 ≤ (40293441025687/100000000000000 : ℝ)^3183
        have hw : |(628393737/1250000000 : ℝ)|=(628393737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134394721/2000000000 : ℝ)|^4207 ≤ (9452316463121/20000000000000 : ℝ)^3183
        have hw : |(1134394721/2000000000 : ℝ)|=(1134394721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s1_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5244282539/10000000000 : ℝ)*x 0 + (-884269573/5000000000 : ℝ)*x 1 + (5671967437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244282539/10000000000 : ℝ)^4207 ≤ (21304755437621/50000000000000 : ℝ)^3183 := by
    have hnat : (5244282539 : ℕ)^4207*50000000000000^3183 ≤ 21304755437621^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244282539 10000000000 21304755437621 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884269573/5000000000 : ℝ)^4207 ≤ (2025794945799/20000000000000 : ℝ)^3183 := by
    have hnat : (884269573 : ℕ)^4207*20000000000000^3183 ≤ 2025794945799^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884269573 5000000000 2025794945799 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5671967437/10000000000 : ℝ)^4207 ≤ (23630757193381/50000000000000 : ℝ)^3183 := by
    have hnat : (5671967437 : ℕ)^4207*50000000000000^3183 ≤ 23630757193381^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671967437 10000000000 23630757193381 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244282539/10000000000 : ℝ), (-884269573/5000000000 : ℝ), (5671967437/10000000000 : ℝ)] ![(21304755437621/50000000000000 : ℝ), (2025794945799/20000000000000 : ℝ), (23630757193381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244282539/10000000000 : ℝ)|^4207 ≤ (21304755437621/50000000000000 : ℝ)^3183
        have hw : |(5244282539/10000000000 : ℝ)|=(5244282539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884269573/5000000000 : ℝ)|^4207 ≤ (2025794945799/20000000000000 : ℝ)^3183
        have hw : |(-884269573/5000000000 : ℝ)|=(884269573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5671967437/10000000000 : ℝ)|^4207 ≤ (23630757193381/50000000000000 : ℝ)^3183
        have hw : |(5671967437/10000000000 : ℝ)|=(5671967437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s1_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5244282653/10000000000 : ℝ)*x 0 + (5671967911/10000000000 : ℝ)*x 1 + (-884269147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244282653/10000000000 : ℝ)^4207 ≤ (42609512099467/100000000000000 : ℝ)^3183 := by
    have hnat : (5244282653 : ℕ)^4207*100000000000000^3183 ≤ 42609512099467^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244282653 10000000000 42609512099467 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671967911/10000000000 : ℝ)^4207 ≤ (23630759803487/50000000000000 : ℝ)^3183 := by
    have hnat : (5671967911 : ℕ)^4207*50000000000000^3183 ≤ 23630759803487^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671967911 10000000000 23630759803487 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884269147/5000000000 : ℝ)^4207 ≤ (2532242069873/25000000000000 : ℝ)^3183 := by
    have hnat : (884269147 : ℕ)^4207*25000000000000^3183 ≤ 2532242069873^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884269147 5000000000 2532242069873 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244282653/10000000000 : ℝ), (5671967911/10000000000 : ℝ), (-884269147/5000000000 : ℝ)] ![(42609512099467/100000000000000 : ℝ), (23630759803487/50000000000000 : ℝ), (2532242069873/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244282653/10000000000 : ℝ)|^4207 ≤ (42609512099467/100000000000000 : ℝ)^3183
        have hw : |(5244282653/10000000000 : ℝ)|=(5244282653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671967911/10000000000 : ℝ)|^4207 ≤ (23630759803487/50000000000000 : ℝ)^3183
        have hw : |(5671967911/10000000000 : ℝ)|=(5671967911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-884269147/5000000000 : ℝ)|^4207 ≤ (2532242069873/25000000000000 : ℝ)^3183
        have hw : |(-884269147/5000000000 : ℝ)|=(884269147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s1_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172483643/400000000 : ℝ)*x 0 + (1253115407/2500000000 : ℝ)*x 1 + (927427651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172483643/400000000 : ℝ)^4207 ≤ (32897561959483/100000000000000 : ℝ)^3183 := by
    have hnat : (172483643 : ℕ)^4207*100000000000000^3183 ≤ 32897561959483^3183*400000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172483643 400000000 32897561959483 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253115407/2500000000 : ℝ)^4207 ≤ (5017238855031/12500000000000 : ℝ)^3183 := by
    have hnat : (1253115407 : ℕ)^4207*12500000000000^3183 ≤ 5017238855031^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253115407 2500000000 5017238855031 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (927427651/2500000000 : ℝ)^4207 ≤ (26964527180813/100000000000000 : ℝ)^3183 := by
    have hnat : (927427651 : ℕ)^4207*100000000000000^3183 ≤ 26964527180813^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927427651 2500000000 26964527180813 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172483643/400000000 : ℝ), (1253115407/2500000000 : ℝ), (927427651/2500000000 : ℝ)] ![(32897561959483/100000000000000 : ℝ), (5017238855031/12500000000000 : ℝ), (26964527180813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172483643/400000000 : ℝ)|^4207 ≤ (32897561959483/100000000000000 : ℝ)^3183
        have hw : |(172483643/400000000 : ℝ)|=(172483643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1253115407/2500000000 : ℝ)|^4207 ≤ (5017238855031/12500000000000 : ℝ)^3183
        have hw : |(1253115407/2500000000 : ℝ)|=(1253115407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(927427651/2500000000 : ℝ)|^4207 ≤ (26964527180813/100000000000000 : ℝ)^3183
        have hw : |(927427651/2500000000 : ℝ)|=(927427651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5503/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (367/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (38/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2511/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5503/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (367/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5503/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (367/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5503/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (367/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5503/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (367/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5503/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (367/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5503/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (367/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (367/50000 : ℝ) ^ (8413/2048 : ℝ) ≤ (6831737319/4000000000000000000 : ℝ) := by
    have hpowers : (367/50000 : ℝ)^8413 ≤ (6831737319/4000000000000000000 : ℝ)^2048 := by
      have hnat : (367 : ℕ)^8413*4000000000000000000^2048 ≤ 6831737319^2048*50000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        367 50000 6831737319 4000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (367/50000 : ℝ)) (X := (6831737319/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5503/20000 : ℝ) ^ (8413/2048 : ℝ) ≤ (124664252210214807/25000000000000000000 : ℝ) := by
    have hpowers : (5503/20000 : ℝ)^8413 ≤ (124664252210214807/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5503 : ℕ)^8413*25000000000000000000^2048 ≤ 124664252210214807^2048*20000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5503 20000 124664252210214807 25000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5503/20000 : ℝ)) (X := (124664252210214807/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000000006831737319/2000000000000000000 : ℝ) ≤ (2000000001663069/2000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (2000000006831737319/2000000000000000000 : ℝ)^2048 ≤ (2000000001663069/2000000000000000 : ℝ)^8413 := by
      have hnat : (2000000006831737319 : ℕ)^2048*2000000000000000^8413 ≤ 2000000001663069^8413*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000006831737319 2000000000000000000 2000000001663069 2000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000001663069/2000000000000000 : ℝ)) (X := (2000000006831737319/2000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100498657179634292203/100000000000000000000 : ℝ) ≤ (2503029029735003/2500000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (100498657179634292203/100000000000000000000 : ℝ)^2048 ≤ (2503029029735003/2500000000000000 : ℝ)^8413 := by
      have hnat : (100498657179634292203 : ℕ)^2048*2500000000000000^8413 ≤ 2503029029735003^8413*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100498657179634292203 100000000000000000000 2503029029735003 2500000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503029029735003/2500000000000000 : ℝ)) (X := (100498657179634292203/100000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12624664252210214807/12500000000000000000 : ℝ) ≤ (10024232229564679/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (12624664252210214807/12500000000000000000 : ℝ)^2048 ≤ (10024232229564679/10000000000000000 : ℝ)^8413 := by
      have hnat : (12624664252210214807 : ℕ)^2048*10000000000000000^8413 ≤ 10024232229564679^8413*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12624664252210214807 12500000000000000000 10024232229564679 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024232229564679/10000000000000000 : ℝ)) (X := (12624664252210214807/12500000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6831737319/4000000000000000000 : ℝ) ≤ ((267792213772296243289/267810000000000000000 : ℝ)+2*(12116110624667/2678100000000000 : ℝ)*(367/50000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (267792213772296243289/267810000000000000000 : ℝ)+2*(12116110624667/2678100000000000 : ℝ)*(367/50000 : ℝ)=(2000000001663069/2000000000000000 : ℝ) by norm_num, show 1+2*(6831737319/4000000000000000000 : ℝ)=(2000000006831737319/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(124664252210214807/25000000000000000000 : ℝ)+(6831737319/4000000000000000000 : ℝ) ≤ ((267792213772296243289/267810000000000000000 : ℝ)+(12116110624667/2678100000000000 : ℝ)*((5503/20000 : ℝ)+(367/50000 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (267792213772296243289/267810000000000000000 : ℝ)+(12116110624667/2678100000000000 : ℝ)*((5503/20000 : ℝ)+(367/50000 : ℝ))=(2503029029735003/2500000000000000 : ℝ) by norm_num, show 1+(124664252210214807/25000000000000000000 : ℝ)+(6831737319/4000000000000000000 : ℝ)=(100498657179634292203/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(124664252210214807/25000000000000000000 : ℝ) ≤ ((267792213772296243289/267810000000000000000 : ℝ)+2*(12116110624667/2678100000000000 : ℝ)*(5503/20000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (267792213772296243289/267810000000000000000 : ℝ)+2*(12116110624667/2678100000000000 : ℝ)*(5503/20000 : ℝ)=(10024232229564679/10000000000000000 : ℝ) by norm_num, show 1+2*(124664252210214807/25000000000000000000 : ℝ)=(12624664252210214807/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (267792213772296243289/267810000000000000000 : ℝ)*(X 1 0+X 2 0)+(12116110624667/2678100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (367/50000 : ℝ)) (hi := (5503/20000 : ℝ)) (c := (267792213772296243289/267810000000000000000 : ℝ)) (alpha := (12116110624667/2678100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (267792213772296243289/267810000000000000000 : ℝ)*(X 0 1+X 2 1)+(12116110624667/2678100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (367/50000 : ℝ)) (hi := (5503/20000 : ℝ)) (c := (267792213772296243289/267810000000000000000 : ℝ)) (alpha := (12116110624667/2678100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (267792213772296243289/267810000000000000000 : ℝ)*(X 0 2+X 1 2)+(12116110624667/2678100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (367/50000 : ℝ)) (hi := (5503/20000 : ℝ)) (c := (267792213772296243289/267810000000000000000 : ℝ)) (alpha := (12116110624667/2678100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2065995187/10000000000 : ℝ)*X 0 0+(355056977/625000000 : ℝ)*X 0 1+(1003675517/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414800551/10000000000 : ℝ)*X 1 0+(-2422129753/10000000000 : ℝ)*X 1 1+(5018377617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2707400277/5000000000 : ℝ)*X 2 0+(2509188803/5000000000 : ℝ)*X 2 1+(-1211064881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269417153/625000000 : ℝ)*X 0 0+(922910253/2500000000 : ℝ)*X 0 1+(5030190307/10000000000 : ℝ)*X 0 2+(269417153/625000000 : ℝ)*X 1 0+(922910253/2500000000 : ℝ)*X 1 1+(5030190307/10000000000 : ℝ)*X 1 2+(269417153/625000000 : ℝ)*X 2 0+(922910253/2500000000 : ℝ)*X 2 1+(5030190307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2066693199/10000000000 : ℝ)*X 0 0+(628393737/1250000000 : ℝ)*X 0 1+(1134394721/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244282539/10000000000 : ℝ)*X 1 0+(-884269573/5000000000 : ℝ)*X 1 1+(5671967437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244282653/10000000000 : ℝ)*X 2 0+(5671967911/10000000000 : ℝ)*X 2 1+(-884269147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172483643/400000000 : ℝ)*X 0 0+(1253115407/2500000000 : ℝ)*X 0 1+(927427651/2500000000 : ℝ)*X 0 2+(172483643/400000000 : ℝ)*X 1 0+(1253115407/2500000000 : ℝ)*X 1 1+(927427651/2500000000 : ℝ)*X 1 2+(172483643/400000000 : ℝ)*X 2 0+(1253115407/2500000000 : ℝ)*X 2 1+(927427651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16544473829251568342586088929/2231750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76170357/100000000000000 : ℝ)*(base1) + (1574146789/100000000000000 : ℝ)*(base19) + (787491519/50000000000000 : ℝ)*(base23) + (43185237/25000000000000 : ℝ)*(upper3) + (8471523/5000000000000 : ℝ)*(upper5) + (1128230078864761/100000000000000 : ℝ)*(major0) + (1128230078864761/100000000000000 : ℝ)*(major1) + (1128230078864761/100000000000000 : ℝ)*(major2) + (377341258180107/25000000000000 : ℝ)*(sp0) + (188671528308167/12500000000000 : ℝ)*(sp1) + (47167882050909/3125000000000 : ℝ)*(sp2) + (747081677861391/100000000000000 : ℝ)*(sp3) + (4422031027/50000000000000 : ℝ)*(sp4) + (4355978009/100000000000000 : ℝ)*(sp7) + (186771527502439/25000000000000 : ℝ)*(f.failure) + (12074990404897/800000000000 : ℝ)*(f.sum) + (204506167094309/66952500000000000000000000000 : ℝ)*base66 + (61775578355266820357/8927000000000000000000000000000000 : ℝ)*base68 + (77135055852439820357/8927000000000000000000000000000000 : ℝ)*base70 + (30956322740151820357/8927000000000000000000000000000000 : ℝ)*base72 + (538673653752493/133905000000000000000000000000 : ℝ)*base74 + (25597812997686179643/8927000000000000000000000000000000 : ℝ)*base75 + (35827917117183820357/8927000000000000000000000000000000 : ℝ)*base78 + (57031221080562820357/8927000000000000000000000000000000 : ℝ)*base80 + (364112314056899/66952500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12919/1220703125000000000 : ℝ)*base89 + (12919/1220703125000000000 : ℝ)*base91 + (12919/1220703125000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2400375073846436803963155597/1115875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (815851/5000000000000 : ℝ)*(base19) + (66294763/25000000000000 : ℝ)*(lower2) + (59766453/20000000000000 : ℝ)*(lower3) + (119471221/50000000000000 : ℝ)*(lower4) + (101498501/100000000000000 : ℝ)*(lower5) + (289805115796809/25000000000000 : ℝ)*(major0) + (289805115796809/25000000000000 : ℝ)*(major1) + (289805115796809/25000000000000 : ℝ)*(major2) + (1991015453/20000000000000 : ℝ)*(sp0) + (20320163/3125000000000 : ℝ)*(sp3) + (193852965252999/12500000000000 : ℝ)*(sp4) + (1550833660784237/100000000000000 : ℝ)*(sp5) + (775416838550629/50000000000000 : ℝ)*(sp6) + (191901631831041/25000000000000 : ℝ)*(sp7) + (38380358878469/5000000000000 : ℝ)*(f.failure) + (775416838550629/50000000000000 : ℝ)*(f.sum) + (388298403074871/44635000000000000000000000000 : ℝ)*base66 + (21611429686123388267/2231750000000000000000000000000000 : ℝ)*base67 + (25401691819613638267/2231750000000000000000000000000000 : ℝ)*base69 + (17281196595322138267/2231750000000000000000000000000000 : ℝ)*base71 + (23152803919883/22317500000000000000000000000 : ℝ)*base74 + (19315588198121638267/2231750000000000000000000000000000 : ℝ)*base75 + (524459400662888267/2231750000000000000000000000000000 : ℝ)*base77 + (11827034350872888267/2231750000000000000000000000000000 : ℝ)*base79 + (2042468235607/5579375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (72057/7812500000000000000 : ℝ)*base90 + (72057/7812500000000000000 : ℝ)*base92 + (72057/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1221_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5503/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (367/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (38/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2511/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1221_s2_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132193707/625000000 : ℝ)*x 0 + (5496406379/10000000000 : ℝ)*x 1 + (646448251/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132193707/625000000 : ℝ)^4207 ≤ (6415840363117/50000000000000 : ℝ)^3183 := by
    have hnat : (132193707 : ℕ)^4207*50000000000000^3183 ≤ 6415840363117^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132193707 625000000 6415840363117 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496406379/10000000000 : ℝ)^4207 ≤ (45337736728119/100000000000000 : ℝ)^3183 := by
    have hnat : (5496406379 : ℕ)^4207*100000000000000^3183 ≤ 45337736728119^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496406379 10000000000 45337736728119 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646448251/1250000000 : ℝ)^4207 ≤ (10457645632393/25000000000000 : ℝ)^3183 := by
    have hnat : (646448251 : ℕ)^4207*25000000000000^3183 ≤ 10457645632393^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646448251 1250000000 10457645632393 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132193707/625000000 : ℝ), (5496406379/10000000000 : ℝ), (646448251/1250000000 : ℝ)] ![(6415840363117/50000000000000 : ℝ), (45337736728119/100000000000000 : ℝ), (10457645632393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132193707/625000000 : ℝ)|^4207 ≤ (6415840363117/50000000000000 : ℝ)^3183
        have hw : |(-132193707/625000000 : ℝ)|=(132193707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496406379/10000000000 : ℝ)|^4207 ≤ (45337736728119/100000000000000 : ℝ)^3183
        have hw : |(5496406379/10000000000 : ℝ)|=(5496406379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646448251/1250000000 : ℝ)|^4207 ≤ (10457645632393/25000000000000 : ℝ)^3183
        have hw : |(646448251/1250000000 : ℝ)|=(646448251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s2_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685271301/5000000000 : ℝ)*x 0 + (-1141739143/5000000000 : ℝ)*x 1 + (2585792971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685271301/5000000000 : ℝ)^4207 ≤ (21985308447631/50000000000000 : ℝ)^3183 := by
    have hnat : (2685271301 : ℕ)^4207*50000000000000^3183 ≤ 21985308447631^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685271301 5000000000 21985308447631 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141739143/5000000000 : ℝ)^4207 ≤ (14198801273869/100000000000000 : ℝ)^3183 := by
    have hnat : (1141739143 : ℕ)^4207*100000000000000^3183 ≤ 14198801273869^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141739143 5000000000 14198801273869 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585792971/5000000000 : ℝ)^4207 ≤ (20915290911993/50000000000000 : ℝ)^3183 := by
    have hnat : (2585792971 : ℕ)^4207*50000000000000^3183 ≤ 20915290911993^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585792971 5000000000 20915290911993 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685271301/5000000000 : ℝ), (-1141739143/5000000000 : ℝ), (2585792971/5000000000 : ℝ)] ![(21985308447631/50000000000000 : ℝ), (14198801273869/100000000000000 : ℝ), (20915290911993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685271301/5000000000 : ℝ)|^4207 ≤ (21985308447631/50000000000000 : ℝ)^3183
        have hw : |(2685271301/5000000000 : ℝ)|=(2685271301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141739143/5000000000 : ℝ)|^4207 ≤ (14198801273869/100000000000000 : ℝ)^3183
        have hw : |(-1141739143/5000000000 : ℝ)|=(1141739143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585792971/5000000000 : ℝ)|^4207 ≤ (20915290911993/50000000000000 : ℝ)^3183
        have hw : |(2585792971/5000000000 : ℝ)|=(2585792971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s2_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074108481/2000000000 : ℝ)*x 0 + (1292896529/2500000000 : ℝ)*x 1 + (-1141739159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074108481/2000000000 : ℝ)^4207 ≤ (43970614763461/100000000000000 : ℝ)^3183 := by
    have hnat : (1074108481 : ℕ)^4207*100000000000000^3183 ≤ 43970614763461^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074108481 2000000000 43970614763461 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292896529/2500000000 : ℝ)^4207 ≤ (41830583684167/100000000000000 : ℝ)^3183 := by
    have hnat : (1292896529 : ℕ)^4207*100000000000000^3183 ≤ 41830583684167^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292896529 2500000000 41830583684167 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141739159/5000000000 : ℝ)^4207 ≤ (709940076843/5000000000000 : ℝ)^3183 := by
    have hnat : (1141739159 : ℕ)^4207*5000000000000^3183 ≤ 709940076843^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141739159 5000000000 709940076843 5000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074108481/2000000000 : ℝ), (1292896529/2500000000 : ℝ), (-1141739159/5000000000 : ℝ)] ![(43970614763461/100000000000000 : ℝ), (41830583684167/100000000000000 : ℝ), (709940076843/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074108481/2000000000 : ℝ)|^4207 ≤ (43970614763461/100000000000000 : ℝ)^3183
        have hw : |(1074108481/2000000000 : ℝ)|=(1074108481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292896529/2500000000 : ℝ)|^4207 ≤ (41830583684167/100000000000000 : ℝ)^3183
        have hw : |(1292896529/2500000000 : ℝ)|=(1292896529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1141739159/5000000000 : ℝ)|^4207 ≤ (709940076843/5000000000000 : ℝ)^3183
        have hw : |(-1141739159/5000000000 : ℝ)|=(1141739159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s2_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086136379/2500000000 : ℝ)*x 0 + (2014239527/5000000000 : ℝ)*x 1 + (468472957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086136379/2500000000 : ℝ)^4207 ≤ (33225212105687/100000000000000 : ℝ)^3183 := by
    have hnat : (1086136379 : ℕ)^4207*100000000000000^3183 ≤ 33225212105687^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086136379 2500000000 33225212105687 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014239527/5000000000 : ℝ)^4207 ≤ (6013695242533/20000000000000 : ℝ)^3183 := by
    have hnat : (2014239527 : ℕ)^4207*20000000000000^3183 ≤ 6013695242533^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014239527 5000000000 6013695242533 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468472957/1000000000 : ℝ)^4207 ≤ (36706311675313/100000000000000 : ℝ)^3183 := by
    have hnat : (468472957 : ℕ)^4207*100000000000000^3183 ≤ 36706311675313^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468472957 1000000000 36706311675313 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086136379/2500000000 : ℝ), (2014239527/5000000000 : ℝ), (468472957/1000000000 : ℝ)] ![(33225212105687/100000000000000 : ℝ), (6013695242533/20000000000000 : ℝ), (36706311675313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086136379/2500000000 : ℝ)|^4207 ≤ (33225212105687/100000000000000 : ℝ)^3183
        have hw : |(1086136379/2500000000 : ℝ)|=(1086136379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014239527/5000000000 : ℝ)|^4207 ≤ (6013695242533/20000000000000 : ℝ)^3183
        have hw : |(2014239527/5000000000 : ℝ)|=(2014239527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468472957/1000000000 : ℝ)|^4207 ≤ (36706311675313/100000000000000 : ℝ)^3183
        have hw : |(468472957/1000000000 : ℝ)|=(468472957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s2_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115182217/10000000000 : ℝ)*x 0 + (5173704747/10000000000 : ℝ)*x 1 + (549426751/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115182217/10000000000 : ℝ)^4207 ≤ (401010796791/3125000000000 : ℝ)^3183 := by
    have hnat : (2115182217 : ℕ)^4207*3125000000000^3183 ≤ 401010796791^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115182217 10000000000 401010796791 3125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173704747/10000000000 : ℝ)^4207 ≤ (20926617409749/50000000000000 : ℝ)^3183 := by
    have hnat : (5173704747 : ℕ)^4207*50000000000000^3183 ≤ 20926617409749^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173704747 10000000000 20926617409749 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549426751/1000000000 : ℝ)^4207 ≤ (9062883932737/20000000000000 : ℝ)^3183 := by
    have hnat : (549426751 : ℕ)^4207*20000000000000^3183 ≤ 9062883932737^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549426751 1000000000 9062883932737 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115182217/10000000000 : ℝ), (5173704747/10000000000 : ℝ), (549426751/1000000000 : ℝ)] ![(401010796791/3125000000000 : ℝ), (20926617409749/50000000000000 : ℝ), (9062883932737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115182217/10000000000 : ℝ)|^4207 ≤ (401010796791/3125000000000 : ℝ)^3183
        have hw : |(-2115182217/10000000000 : ℝ)|=(2115182217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173704747/10000000000 : ℝ)|^4207 ≤ (20926617409749/50000000000000 : ℝ)^3183
        have hw : |(5173704747/10000000000 : ℝ)|=(5173704747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549426751/1000000000 : ℝ)|^4207 ≤ (9062883932737/20000000000000 : ℝ)^3183
        have hw : |(549426751/1000000000 : ℝ)|=(549426751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s2_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287701321/10000000000 : ℝ)*x 0 + (-1960796557/10000000000 : ℝ)*x 1 + (1098853509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287701321/10000000000 : ℝ)^4207 ≤ (43076396915983/100000000000000 : ℝ)^3183 := by
    have hnat : (5287701321 : ℕ)^4207*100000000000000^3183 ≤ 43076396915983^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287701321 10000000000 43076396915983 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960796557/10000000000 : ℝ)^4207 ≤ (5804591511127/50000000000000 : ℝ)^3183 := by
    have hnat : (1960796557 : ℕ)^4207*50000000000000^3183 ≤ 5804591511127^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960796557 10000000000 5804591511127 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098853509/2000000000 : ℝ)^4207 ≤ (1416075626413/3125000000000 : ℝ)^3183 := by
    have hnat : (1098853509 : ℕ)^4207*3125000000000^3183 ≤ 1416075626413^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098853509 2000000000 1416075626413 3125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287701321/10000000000 : ℝ), (-1960796557/10000000000 : ℝ), (1098853509/2000000000 : ℝ)] ![(43076396915983/100000000000000 : ℝ), (5804591511127/50000000000000 : ℝ), (1416075626413/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287701321/10000000000 : ℝ)|^4207 ≤ (43076396915983/100000000000000 : ℝ)^3183
        have hw : |(5287701321/10000000000 : ℝ)|=(5287701321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960796557/10000000000 : ℝ)|^4207 ≤ (5804591511127/50000000000000 : ℝ)^3183
        have hw : |(-1960796557/10000000000 : ℝ)|=(1960796557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098853509/2000000000 : ℝ)|^4207 ≤ (1416075626413/3125000000000 : ℝ)^3183
        have hw : |(1098853509/2000000000 : ℝ)|=(1098853509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s2_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287701503/10000000000 : ℝ)*x 0 + (686783449/1250000000 : ℝ)*x 1 + (-1960796241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287701503/10000000000 : ℝ)^4207 ≤ (43076398875639/100000000000000 : ℝ)^3183 := by
    have hnat : (5287701503 : ℕ)^4207*100000000000000^3183 ≤ 43076398875639^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287701503 10000000000 43076398875639 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686783449/1250000000 : ℝ)^4207 ≤ (45314420557559/100000000000000 : ℝ)^3183 := by
    have hnat : (686783449 : ℕ)^4207*100000000000000^3183 ≤ 45314420557559^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686783449 1250000000 45314420557559 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960796241/10000000000 : ℝ)^4207 ≤ (2902295137359/25000000000000 : ℝ)^3183 := by
    have hnat : (1960796241 : ℕ)^4207*25000000000000^3183 ≤ 2902295137359^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960796241 10000000000 2902295137359 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287701503/10000000000 : ℝ), (686783449/1250000000 : ℝ), (-1960796241/10000000000 : ℝ)] ![(43076398875639/100000000000000 : ℝ), (45314420557559/100000000000000 : ℝ), (2902295137359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287701503/10000000000 : ℝ)|^4207 ≤ (43076398875639/100000000000000 : ℝ)^3183
        have hw : |(5287701503/10000000000 : ℝ)|=(5287701503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686783449/1250000000 : ℝ)|^4207 ≤ (45314420557559/100000000000000 : ℝ)^3183
        have hw : |(686783449/1250000000 : ℝ)|=(686783449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1960796241/10000000000 : ℝ)|^4207 ≤ (2902295137359/25000000000000 : ℝ)^3183
        have hw : |(-1960796241/10000000000 : ℝ)|=(1960796241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s2_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543089061/1250000000 : ℝ)*x 0 + (2340224551/5000000000 : ℝ)*x 1 + (1008199997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543089061/1250000000 : ℝ)^4207 ≤ (4153362480747/12500000000000 : ℝ)^3183 := by
    have hnat : (543089061 : ℕ)^4207*12500000000000^3183 ≤ 4153362480747^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543089061 1250000000 4153362480747 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2340224551/5000000000 : ℝ)^4207 ≤ (7332397931943/20000000000000 : ℝ)^3183 := by
    have hnat : (2340224551 : ℕ)^4207*20000000000000^3183 ≤ 7332397931943^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340224551 5000000000 7332397931943 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008199997/2500000000 : ℝ)^4207 ≤ (30111110471861/100000000000000 : ℝ)^3183 := by
    have hnat : (1008199997 : ℕ)^4207*100000000000000^3183 ≤ 30111110471861^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008199997 2500000000 30111110471861 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543089061/1250000000 : ℝ), (2340224551/5000000000 : ℝ), (1008199997/2500000000 : ℝ)] ![(4153362480747/12500000000000 : ℝ), (7332397931943/20000000000000 : ℝ), (30111110471861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543089061/1250000000 : ℝ)|^4207 ≤ (4153362480747/12500000000000 : ℝ)^3183
        have hw : |(543089061/1250000000 : ℝ)|=(543089061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2340224551/5000000000 : ℝ)|^4207 ≤ (7332397931943/20000000000000 : ℝ)^3183
        have hw : |(2340224551/5000000000 : ℝ)|=(2340224551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1008199997/2500000000 : ℝ)|^4207 ≤ (30111110471861/100000000000000 : ℝ)^3183
        have hw : |(1008199997/2500000000 : ℝ)|=(1008199997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2511/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (38/625 : ℝ)*pair X i i ≤ pair X i h) :
    (9413/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16279/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2511/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (38/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2511/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (38/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2511/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (38/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2511/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (38/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2511/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (38/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2511/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (38/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (38/625 : ℝ) ^ (8413/2048 : ℝ) ≤ (1010148358204451/100000000000000000000 : ℝ) := by
    have hpowers : (38/625 : ℝ)^8413 ≤ (1010148358204451/100000000000000000000 : ℝ)^2048 := by
      have hnat : (38 : ℕ)^8413*100000000000000000000^2048 ≤ 1010148358204451^2048*625^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38 625 1010148358204451 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38/625 : ℝ)) (X := (1010148358204451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2511/12500 : ℝ) ^ (8413/2048 : ℝ) ≤ (136938822500704277/100000000000000000000 : ℝ) := by
    have hpowers : (2511/12500 : ℝ)^8413 ≤ (136938822500704277/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2511 : ℕ)^8413*100000000000000000000^2048 ≤ 136938822500704277^2048*12500^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2511 12500 136938822500704277 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2511/12500 : ℝ)) (X := (136938822500704277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001010148358204451/50000000000000000000 : ℝ) ≤ (10000049180269279/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50001010148358204451/50000000000000000000 : ℝ)^2048 ≤ (10000049180269279/10000000000000000 : ℝ)^8413 := by
      have hnat : (50001010148358204451 : ℕ)^2048*10000000000000000^8413 ≤ 10000049180269279^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001010148358204451 50000000000000000000 10000049180269279 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000049180269279/10000000000000000 : ℝ)) (X := (50001010148358204451/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12517243621357363591/12500000000000000000 : ℝ) ≤ (78151221712471/78125000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (12517243621357363591/12500000000000000000 : ℝ)^2048 ≤ (78151221712471/78125000000000 : ℝ)^8413 := by
      have hnat : (12517243621357363591 : ℕ)^2048*78125000000000^8413 ≤ 78151221712471^8413*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12517243621357363591 12500000000000000000 78151221712471 78125000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78151221712471/78125000000000 : ℝ)) (X := (12517243621357363591/12500000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50136938822500704277/50000000000000000000 : ℝ) ≤ (10006663578123297/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50136938822500704277/50000000000000000000 : ℝ)^2048 ≤ (10006663578123297/10000000000000000 : ℝ)^8413 := by
      have hnat : (50136938822500704277 : ℕ)^2048*10000000000000000^8413 ≤ 10006663578123297^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50136938822500704277 50000000000000000000 10006663578123297 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006663578123297/10000000000000000 : ℝ)) (X := (50136938822500704277/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1010148358204451/100000000000000000000 : ℝ) ≤ ((17505059172282453849/17510000000000000000 : ℝ)+2*(3307198927009/1400800000000000 : ℝ)*(38/625 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (17505059172282453849/17510000000000000000 : ℝ)+2*(3307198927009/1400800000000000 : ℝ)*(38/625 : ℝ)=(10000049180269279/10000000000000000 : ℝ) by norm_num, show 1+2*(1010148358204451/100000000000000000000 : ℝ)=(50001010148358204451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(136938822500704277/100000000000000000000 : ℝ)+(1010148358204451/100000000000000000000 : ℝ) ≤ ((17505059172282453849/17510000000000000000 : ℝ)+(3307198927009/1400800000000000 : ℝ)*((2511/12500 : ℝ)+(38/625 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (17505059172282453849/17510000000000000000 : ℝ)+(3307198927009/1400800000000000 : ℝ)*((2511/12500 : ℝ)+(38/625 : ℝ))=(78151221712471/78125000000000 : ℝ) by norm_num, show 1+(136938822500704277/100000000000000000000 : ℝ)+(1010148358204451/100000000000000000000 : ℝ)=(12517243621357363591/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(136938822500704277/100000000000000000000 : ℝ) ≤ ((17505059172282453849/17510000000000000000 : ℝ)+2*(3307198927009/1400800000000000 : ℝ)*(2511/12500 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (17505059172282453849/17510000000000000000 : ℝ)+2*(3307198927009/1400800000000000 : ℝ)*(2511/12500 : ℝ)=(10006663578123297/10000000000000000 : ℝ) by norm_num, show 1+2*(136938822500704277/100000000000000000000 : ℝ)=(50136938822500704277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17505059172282453849/17510000000000000000 : ℝ)*(X 1 0+X 2 0)+(3307198927009/1400800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (38/625 : ℝ)) (hi := (2511/12500 : ℝ)) (c := (17505059172282453849/17510000000000000000 : ℝ)) (alpha := (3307198927009/1400800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17505059172282453849/17510000000000000000 : ℝ)*(X 0 1+X 2 1)+(3307198927009/1400800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (38/625 : ℝ)) (hi := (2511/12500 : ℝ)) (c := (17505059172282453849/17510000000000000000 : ℝ)) (alpha := (3307198927009/1400800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17505059172282453849/17510000000000000000 : ℝ)*(X 0 2+X 1 2)+(3307198927009/1400800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (38/625 : ℝ)) (hi := (2511/12500 : ℝ)) (c := (17505059172282453849/17510000000000000000 : ℝ)) (alpha := (3307198927009/1400800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132193707/625000000 : ℝ)*X 0 0+(5496406379/10000000000 : ℝ)*X 0 1+(646448251/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685271301/5000000000 : ℝ)*X 1 0+(-1141739143/5000000000 : ℝ)*X 1 1+(2585792971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074108481/2000000000 : ℝ)*X 2 0+(1292896529/2500000000 : ℝ)*X 2 1+(-1141739159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086136379/2500000000 : ℝ)*X 0 0+(2014239527/5000000000 : ℝ)*X 0 1+(468472957/1000000000 : ℝ)*X 0 2+(1086136379/2500000000 : ℝ)*X 1 0+(2014239527/5000000000 : ℝ)*X 1 1+(468472957/1000000000 : ℝ)*X 1 2+(1086136379/2500000000 : ℝ)*X 2 0+(2014239527/5000000000 : ℝ)*X 2 1+(468472957/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115182217/10000000000 : ℝ)*X 0 0+(5173704747/10000000000 : ℝ)*X 0 1+(549426751/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287701321/10000000000 : ℝ)*X 1 0+(-1960796557/10000000000 : ℝ)*X 1 1+(1098853509/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287701503/10000000000 : ℝ)*X 2 0+(686783449/1250000000 : ℝ)*X 2 1+(-1960796241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543089061/1250000000 : ℝ)*X 0 0+(2340224551/5000000000 : ℝ)*X 0 1+(1008199997/2500000000 : ℝ)*X 0 2+(543089061/1250000000 : ℝ)*X 1 0+(2340224551/5000000000 : ℝ)*X 1 1+(1008199997/2500000000 : ℝ)*X 1 2+(543089061/1250000000 : ℝ)*X 2 0+(2340224551/5000000000 : ℝ)*X 2 1+(1008199997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35184818491481828155567137/5471875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1297625623/100000000000000 : ℝ)*(base19) + (1091573709/100000000000000 : ℝ)*(base23) + (50011649/100000000000000 : ℝ)*(lower2) + (106486997/50000000000000 : ℝ)*(upper3) + (88106187/100000000000000 : ℝ)*(upper5) + (14382730530093/625000000000 : ℝ)*(major0) + (14382730530093/625000000000 : ℝ)*(major1) + (14382730530093/625000000000 : ℝ)*(major2) + (24051868005881/781250000000 : ℝ)*(sp0) + (384831249274963/12500000000000 : ℝ)*(sp1) + (1539325100125809/50000000000000 : ℝ)*(sp2) + (380953681837789/25000000000000 : ℝ)*(sp3) + (12187072559/100000000000000 : ℝ)*(sp4) + (75361159/1000000000000 : ℝ)*(sp7) + (1523822263467057/100000000000000 : ℝ)*(f.failure) + (192415705739083/6250000000000 : ℝ)*(f.sum) + (5444205370821/1751000000000000000000000000 : ℝ)*base65 + (7083951766021707/10943750000000000000000000000000 : ℝ)*base67 + (25239988852052957/10943750000000000000000000000000 : ℝ)*base69 + (56012225366740457/10943750000000000000000000000000 : ℝ)*base71 + (1339258351617/437750000000000000000000000 : ℝ)*base73 + (63185987180590457/10943750000000000000000000000000 : ℝ)*base75 + (24154186835602957/10943750000000000000000000000000 : ℝ)*base77 + (77446890414190457/10943750000000000000000000000000 : ℝ)*base79 + (117461566297/109437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (648879/156250000000000000000 : ℝ)*base89 + (648879/156250000000000000000 : ℝ)*base91 + (648879/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3808892700692273194615754067/437750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2113985737/100000000000000 : ℝ)*(base19) + (2329402871/100000000000000 : ℝ)*(base23) + (14995009/100000000000000 : ℝ)*(upper2) + (273917949/100000000000000 : ℝ)*(upper3) + (10961751/6250000000000 : ℝ)*(upper5) + (1165889972828387/50000000000000 : ℝ)*(major0) + (1165889972828387/50000000000000 : ℝ)*(major1) + (1165889972828387/50000000000000 : ℝ)*(major2) + (21367990983/100000000000000 : ℝ)*(sp1) + (5290894267/20000000000000 : ℝ)*(sp2) + (623902495363751/20000000000000 : ℝ)*(sp4) + (779872248710509/25000000000000 : ℝ)*(sp5) + (62389673858891/2000000000000 : ℝ)*(sp6) + (1544047124459171/100000000000000 : ℝ)*(sp7) + (1544047124459171/100000000000000 : ℝ)*(f.failure) + (623902495363751/20000000000000 : ℝ)*(f.sum) + (178586494797223/35020000000000000000000000000 : ℝ)*base65 + (5402415895957850937/875500000000000000000000000000000 : ℝ)*base68 + (2964407168368350937/875500000000000000000000000000000 : ℝ)*base70 + (5815976131254350937/875500000000000000000000000000000 : ℝ)*base72 + (42397159399443/35020000000000000000000000000 : ℝ)*base73 + (14789726621146350937/875500000000000000000000000000000 : ℝ)*base76 + (1183033249880850937/875500000000000000000000000000000 : ℝ)*base78 + (16015120500820350937/875500000000000000000000000000000 : ℝ)*base80 + (15845359047123/35020000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (97637/156250000000000000000 : ℝ)*base89 + (97637/156250000000000000000 : ℝ)*base91 + (97637/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1221_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2511/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (38/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1221_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1221_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1221_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1221_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
