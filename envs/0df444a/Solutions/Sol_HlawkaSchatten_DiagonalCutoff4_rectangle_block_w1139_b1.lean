-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1139_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:51.029747+00:00
-- url     : https://prove2.me/submissions/d06ef0c0-7564-490b-9711-709f72fa4d05

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
theorem support_rectangle_w1139_s3_0 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-216448717/1000000000 : ℝ)*x 0 + (5429481673/10000000000 : ℝ)*x 1 + (2615903707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216448717/1000000000 : ℝ)^2083 ≤ (6572226524109/50000000000000 : ℝ)^1571 := by
    have hnat : (216448717 : ℕ)^2083*50000000000000^1571 ≤ 6572226524109^1571*1000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216448717 1000000000 6572226524109 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429481673/10000000000 : ℝ)^2083 ≤ (11123827855053/25000000000000 : ℝ)^1571 := by
    have hnat : (5429481673 : ℕ)^2083*25000000000000^1571 ≤ 11123827855053^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429481673 10000000000 11123827855053 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615903707/5000000000 : ℝ)^2083 ≤ (4236023551829/10000000000000 : ℝ)^1571 := by
    have hnat : (2615903707 : ℕ)^2083*10000000000000^1571 ≤ 4236023551829^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615903707 5000000000 4236023551829 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216448717/1000000000 : ℝ), (5429481673/10000000000 : ℝ), (2615903707/5000000000 : ℝ)] ![(6572226524109/50000000000000 : ℝ), (11123827855053/25000000000000 : ℝ), (4236023551829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216448717/1000000000 : ℝ)|^2083 ≤ (6572226524109/50000000000000 : ℝ)^1571
        have hw : |(-216448717/1000000000 : ℝ)|=(216448717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429481673/10000000000 : ℝ)|^2083 ≤ (11123827855053/25000000000000 : ℝ)^1571
        have hw : |(5429481673/10000000000 : ℝ)|=(5429481673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615903707/5000000000 : ℝ)|^2083 ≤ (4236023551829/10000000000000 : ℝ)^1571
        have hw : |(2615903707/5000000000 : ℝ)|=(2615903707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s3_1 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353864859/10000000000 : ℝ)*x 0 + (-2265538043/10000000000 : ℝ)*x 1 + (5231807261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353864859/10000000000 : ℝ)^2083 ≤ (545944138647/1250000000000 : ℝ)^1571 := by
    have hnat : (5353864859 : ℕ)^2083*1250000000000^1571 ≤ 545944138647^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353864859 10000000000 545944138647 1250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265538043/10000000000 : ℝ)^2083 ≤ (13964235011421/100000000000000 : ℝ)^1571 := by
    have hnat : (2265538043 : ℕ)^2083*100000000000000^1571 ≤ 13964235011421^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265538043 10000000000 13964235011421 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231807261/10000000000 : ℝ)^2083 ≤ (42360233875769/100000000000000 : ℝ)^1571 := by
    have hnat : (5231807261 : ℕ)^2083*100000000000000^1571 ≤ 42360233875769^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231807261 10000000000 42360233875769 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353864859/10000000000 : ℝ), (-2265538043/10000000000 : ℝ), (5231807261/10000000000 : ℝ)] ![(545944138647/1250000000000 : ℝ), (13964235011421/100000000000000 : ℝ), (42360233875769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353864859/10000000000 : ℝ)|^2083 ≤ (545944138647/1250000000000 : ℝ)^1571
        have hw : |(5353864859/10000000000 : ℝ)|=(5353864859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2265538043/10000000000 : ℝ)|^2083 ≤ (13964235011421/100000000000000 : ℝ)^1571
        have hw : |(-2265538043/10000000000 : ℝ)|=(2265538043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231807261/10000000000 : ℝ)|^2083 ≤ (42360233875769/100000000000000 : ℝ)^1571
        have hw : |(5231807261/10000000000 : ℝ)|=(5231807261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s3_2 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353864943/10000000000 : ℝ)*x 0 + (1046361469/2000000000 : ℝ)*x 1 + (-1132768911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353864943/10000000000 : ℝ)^2083 ≤ (2183776600017/5000000000000 : ℝ)^1571 := by
    have hnat : (5353864943 : ℕ)^2083*5000000000000^1571 ≤ 2183776600017^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353864943 10000000000 2183776600017 5000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046361469/2000000000 : ℝ)^2083 ≤ (8472046955509/20000000000000 : ℝ)^1571 := by
    have hnat : (1046361469 : ℕ)^2083*20000000000000^1571 ≤ 8472046955509^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046361469 2000000000 8472046955509 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132768911/5000000000 : ℝ)^2083 ≤ (6982116602641/50000000000000 : ℝ)^1571 := by
    have hnat : (1132768911 : ℕ)^2083*50000000000000^1571 ≤ 6982116602641^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132768911 5000000000 6982116602641 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353864943/10000000000 : ℝ), (1046361469/2000000000 : ℝ), (-1132768911/5000000000 : ℝ)] ![(2183776600017/5000000000000 : ℝ), (8472046955509/20000000000000 : ℝ), (6982116602641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353864943/10000000000 : ℝ)|^2083 ≤ (2183776600017/5000000000000 : ℝ)^1571
        have hw : |(5353864943/10000000000 : ℝ)|=(5353864943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046361469/2000000000 : ℝ)|^2083 ≤ (8472046955509/20000000000000 : ℝ)^1571
        have hw : |(1046361469/2000000000 : ℝ)|=(1046361469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1132768911/5000000000 : ℝ)|^2083 ≤ (6982116602641/50000000000000 : ℝ)^1571
        have hw : |(-1132768911/5000000000 : ℝ)|=(1132768911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s3_3 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181409791/5000000000 : ℝ)*x 0 + (521337841/1250000000 : ℝ)*x 1 + (36509911/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181409791/5000000000 : ℝ)^2083 ≤ (6658782847583/20000000000000 : ℝ)^1571 := by
    have hnat : (2181409791 : ℕ)^2083*20000000000000^1571 ≤ 6658782847583^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181409791 5000000000 6658782847583 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521337841/1250000000 : ℝ)^2083 ≤ (12545637481/40000000000 : ℝ)^1571 := by
    have hnat : (521337841 : ℕ)^2083*40000000000^1571 ≤ 12545637481^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521337841 1250000000 12545637481 40000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36509911/80000000 : ℝ)^2083 ≤ (17670996021517/50000000000000 : ℝ)^1571 := by
    have hnat : (36509911 : ℕ)^2083*50000000000000^1571 ≤ 17670996021517^1571*80000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36509911 80000000 17670996021517 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181409791/5000000000 : ℝ), (521337841/1250000000 : ℝ), (36509911/80000000 : ℝ)] ![(6658782847583/20000000000000 : ℝ), (12545637481/40000000000 : ℝ), (17670996021517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181409791/5000000000 : ℝ)|^2083 ≤ (6658782847583/20000000000000 : ℝ)^1571
        have hw : |(2181409791/5000000000 : ℝ)|=(2181409791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521337841/1250000000 : ℝ)|^2083 ≤ (12545637481/40000000000 : ℝ)^1571
        have hw : |(521337841/1250000000 : ℝ)|=(521337841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36509911/80000000 : ℝ)|^2083 ≤ (17670996021517/50000000000000 : ℝ)^1571
        have hw : |(36509911/80000000 : ℝ)|=(36509911/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s3_4 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164505389/10000000000 : ℝ)*x 0 + (5232576123/10000000000 : ℝ)*x 1 + (5428708663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164505389/10000000000 : ℝ)^2083 ≤ (13144599746733/100000000000000 : ℝ)^1571 := by
    have hnat : (2164505389 : ℕ)^2083*100000000000000^1571 ≤ 13144599746733^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164505389 10000000000 13144599746733 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232576123/10000000000 : ℝ)^2083 ≤ (42368488142423/100000000000000 : ℝ)^1571 := by
    have hnat : (5232576123 : ℕ)^2083*100000000000000^1571 ≤ 42368488142423^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232576123 10000000000 42368488142423 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428708663/10000000000 : ℝ)^2083 ≤ (1779476484107/4000000000000 : ℝ)^1571 := by
    have hnat : (5428708663 : ℕ)^2083*4000000000000^1571 ≤ 1779476484107^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428708663 10000000000 1779476484107 4000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164505389/10000000000 : ℝ), (5232576123/10000000000 : ℝ), (5428708663/10000000000 : ℝ)] ![(13144599746733/100000000000000 : ℝ), (42368488142423/100000000000000 : ℝ), (1779476484107/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164505389/10000000000 : ℝ)|^2083 ≤ (13144599746733/100000000000000 : ℝ)^1571
        have hw : |(-2164505389/10000000000 : ℝ)|=(2164505389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232576123/10000000000 : ℝ)|^2083 ≤ (42368488142423/100000000000000 : ℝ)^1571
        have hw : |(5232576123/10000000000 : ℝ)|=(5232576123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428708663/10000000000 : ℝ)|^2083 ≤ (1779476484107/4000000000000 : ℝ)^1571
        have hw : |(5428708663/10000000000 : ℝ)|=(5428708663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s3_5 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66297449/125000000 : ℝ)*x 0 + (-2068636543/10000000000 : ℝ)*x 1 + (5428708813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66297449/125000000 : ℝ)^2083 ≤ (10783697763741/25000000000000 : ℝ)^1571 := by
    have hnat : (66297449 : ℕ)^2083*25000000000000^1571 ≤ 10783697763741^1571*125000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66297449 125000000 10783697763741 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068636543/10000000000 : ℝ)^2083 ≤ (1237829519793/10000000000000 : ℝ)^1571 := by
    have hnat : (2068636543 : ℕ)^2083*10000000000000^1571 ≤ 1237829519793^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068636543 10000000000 1237829519793 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428708813/10000000000 : ℝ)^2083 ≤ (2780432108281/6250000000000 : ℝ)^1571 := by
    have hnat : (5428708813 : ℕ)^2083*6250000000000^1571 ≤ 2780432108281^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428708813 10000000000 2780432108281 6250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66297449/125000000 : ℝ), (-2068636543/10000000000 : ℝ), (5428708813/10000000000 : ℝ)] ![(10783697763741/25000000000000 : ℝ), (1237829519793/10000000000000 : ℝ), (2780432108281/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66297449/125000000 : ℝ)|^2083 ≤ (10783697763741/25000000000000 : ℝ)^1571
        have hw : |(66297449/125000000 : ℝ)|=(66297449/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068636543/10000000000 : ℝ)|^2083 ≤ (1237829519793/10000000000000 : ℝ)^1571
        have hw : |(-2068636543/10000000000 : ℝ)|=(2068636543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428708813/10000000000 : ℝ)|^2083 ≤ (2780432108281/6250000000000 : ℝ)^1571
        have hw : |(5428708813/10000000000 : ℝ)|=(5428708813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s3_6 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303795811/10000000000 : ℝ)*x 0 + (5428708987/10000000000 : ℝ)*x 1 + (-2068636453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303795811/10000000000 : ℝ)^2083 ≤ (21567394939789/50000000000000 : ℝ)^1571 := by
    have hnat : (5303795811 : ℕ)^2083*50000000000000^1571 ≤ 21567394939789^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303795811 10000000000 21567394939789 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428708987/10000000000 : ℝ)^2083 ≤ (44486915623089/100000000000000 : ℝ)^1571 := by
    have hnat : (5428708987 : ℕ)^2083*100000000000000^1571 ≤ 44486915623089^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428708987 10000000000 44486915623089 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068636453/10000000000 : ℝ)^2083 ≤ (6189147241937/50000000000000 : ℝ)^1571 := by
    have hnat : (2068636453 : ℕ)^2083*50000000000000^1571 ≤ 6189147241937^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068636453 10000000000 6189147241937 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303795811/10000000000 : ℝ), (5428708987/10000000000 : ℝ), (-2068636453/10000000000 : ℝ)] ![(21567394939789/50000000000000 : ℝ), (44486915623089/100000000000000 : ℝ), (6189147241937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303795811/10000000000 : ℝ)|^2083 ≤ (21567394939789/50000000000000 : ℝ)^1571
        have hw : |(5303795811/10000000000 : ℝ)|=(5303795811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428708987/10000000000 : ℝ)|^2083 ≤ (44486915623089/100000000000000 : ℝ)^1571
        have hw : |(5428708987/10000000000 : ℝ)|=(5428708987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068636453/10000000000 : ℝ)|^2083 ≤ (6189147241937/50000000000000 : ℝ)^1571
        have hw : |(-2068636453/10000000000 : ℝ)|=(2068636453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s3_7 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181427903/5000000000 : ℝ)*x 0 + (142569087/312500000 : ℝ)*x 1 + (834447879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181427903/5000000000 : ℝ)^2083 ≤ (33294280766357/100000000000000 : ℝ)^1571 := by
    have hnat : (2181427903 : ℕ)^2083*100000000000000^1571 ≤ 33294280766357^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181427903 5000000000 33294280766357 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142569087/312500000 : ℝ)^2083 ≤ (35326302552491/100000000000000 : ℝ)^1571 := by
    have hnat : (142569087 : ℕ)^2083*100000000000000^1571 ≤ 35326302552491^1571*312500000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142569087 312500000 35326302552491 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834447879/2000000000 : ℝ)^2083 ≤ (31379416654041/100000000000000 : ℝ)^1571 := by
    have hnat : (834447879 : ℕ)^2083*100000000000000^1571 ≤ 31379416654041^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834447879 2000000000 31379416654041 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181427903/5000000000 : ℝ), (142569087/312500000 : ℝ), (834447879/2000000000 : ℝ)] ![(33294280766357/100000000000000 : ℝ), (35326302552491/100000000000000 : ℝ), (31379416654041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181427903/5000000000 : ℝ)|^2083 ≤ (33294280766357/100000000000000 : ℝ)^1571
        have hw : |(2181427903/5000000000 : ℝ)|=(2181427903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142569087/312500000 : ℝ)|^2083 ≤ (35326302552491/100000000000000 : ℝ)^1571
        have hw : |(142569087/312500000 : ℝ)|=(142569087/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834447879/2000000000 : ℝ)|^2083 ≤ (31379416654041/100000000000000 : ℝ)^1571
        have hw : |(834447879/2000000000 : ℝ)|=(834447879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1139_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5313/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14809/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9057/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (2858359590914499/50000000000000000000 : ℝ) := by
    have hpowers : (9057/100000 : ℝ)^8331 ≤ (2858359590914499/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9057 : ℕ)^8331*50000000000000000000^2048 ≤ 2858359590914499^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9057 100000 2858359590914499 50000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9057/100000 : ℝ)) (X := (2858359590914499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16511/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (65766227910804811/100000000000000000000 : ℝ) := by
    have hpowers : (16511/100000 : ℝ)^8331 ≤ (65766227910804811/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16511 : ℕ)^8331*100000000000000000000^2048 ≤ 65766227910804811^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16511 100000 65766227910804811 100000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16511/100000 : ℝ)) (X := (65766227910804811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002858359590914499/25000000000000000000 : ℝ) ≤ (1250035131845361/1250000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (25002858359590914499/25000000000000000000 : ℝ)^2048 ≤ (1250035131845361/1250000000000000 : ℝ)^8331 := by
      have hnat : (25002858359590914499 : ℕ)^2048*1250000000000000^8331 ≤ 1250035131845361^8331*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002858359590914499 25000000000000000000 1250035131845361 1250000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035131845361/1250000000000000 : ℝ)) (X := (25002858359590914499/25000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100071482947092633809/100000000000000000000 : ℝ) ≤ (2500439195866413/2500000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (100071482947092633809/100000000000000000000 : ℝ)^2048 ≤ (2500439195866413/2500000000000000 : ℝ)^8331 := by
      have hnat : (100071482947092633809 : ℕ)^2048*2500000000000000^8331 ≤ 2500439195866413^8331*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100071482947092633809 100000000000000000000 2500439195866413 2500000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500439195866413/2500000000000000 : ℝ)) (X := (100071482947092633809/100000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50065766227910804811/50000000000000000000 : ℝ) ≤ (312601016005263/312500000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (50065766227910804811/50000000000000000000 : ℝ)^2048 ≤ (312601016005263/312500000000000 : ℝ)^8331 := by
      have hnat : (50065766227910804811 : ℕ)^2048*312500000000000^8331 ≤ 312601016005263^8331*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065766227910804811 50000000000000000000 312601016005263 312500000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312601016005263/312500000000000 : ℝ)) (X := (50065766227910804811/50000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2858359590914499/50000000000000000000 : ℝ) ≤ ((9314420454060087507/9317500000000000000 : ℝ)+2*(368932175691/186350000000000 : ℝ)*(9057/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (9314420454060087507/9317500000000000000 : ℝ)+2*(368932175691/186350000000000 : ℝ)*(9057/100000 : ℝ)=(1250035131845361/1250000000000000 : ℝ) by norm_num, show 1+2*(2858359590914499/50000000000000000000 : ℝ)=(25002858359590914499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65766227910804811/100000000000000000000 : ℝ)+(2858359590914499/50000000000000000000 : ℝ) ≤ ((9314420454060087507/9317500000000000000 : ℝ)+(368932175691/186350000000000 : ℝ)*((16511/100000 : ℝ)+(9057/100000 : ℝ)))^(8331/2048 : ℝ) := by
    rw [show (9314420454060087507/9317500000000000000 : ℝ)+(368932175691/186350000000000 : ℝ)*((16511/100000 : ℝ)+(9057/100000 : ℝ))=(2500439195866413/2500000000000000 : ℝ) by norm_num, show 1+(65766227910804811/100000000000000000000 : ℝ)+(2858359590914499/50000000000000000000 : ℝ)=(100071482947092633809/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65766227910804811/100000000000000000000 : ℝ) ≤ ((9314420454060087507/9317500000000000000 : ℝ)+2*(368932175691/186350000000000 : ℝ)*(16511/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (9314420454060087507/9317500000000000000 : ℝ)+2*(368932175691/186350000000000 : ℝ)*(16511/100000 : ℝ)=(312601016005263/312500000000000 : ℝ) by norm_num, show 1+2*(65766227910804811/100000000000000000000 : ℝ)=(50065766227910804811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9314420454060087507/9317500000000000000 : ℝ)*(X 1 0+X 2 0)+(368932175691/186350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (9057/100000 : ℝ)) (hi := (16511/100000 : ℝ)) (c := (9314420454060087507/9317500000000000000 : ℝ)) (alpha := (368932175691/186350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9314420454060087507/9317500000000000000 : ℝ)*(X 0 1+X 2 1)+(368932175691/186350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (9057/100000 : ℝ)) (hi := (16511/100000 : ℝ)) (c := (9314420454060087507/9317500000000000000 : ℝ)) (alpha := (368932175691/186350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9314420454060087507/9317500000000000000 : ℝ)*(X 0 2+X 1 2)+(368932175691/186350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (9057/100000 : ℝ)) (hi := (16511/100000 : ℝ)) (c := (9314420454060087507/9317500000000000000 : ℝ)) (alpha := (368932175691/186350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216448717/1000000000 : ℝ)*X 0 0+(5429481673/10000000000 : ℝ)*X 0 1+(2615903707/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353864859/10000000000 : ℝ)*X 1 0+(-2265538043/10000000000 : ℝ)*X 1 1+(5231807261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353864943/10000000000 : ℝ)*X 2 0+(1046361469/2000000000 : ℝ)*X 2 1+(-1132768911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181409791/5000000000 : ℝ)*X 0 0+(521337841/1250000000 : ℝ)*X 0 1+(36509911/80000000 : ℝ)*X 0 2+(2181409791/5000000000 : ℝ)*X 1 0+(521337841/1250000000 : ℝ)*X 1 1+(36509911/80000000 : ℝ)*X 1 2+(2181409791/5000000000 : ℝ)*X 2 0+(521337841/1250000000 : ℝ)*X 2 1+(36509911/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2164505389/10000000000 : ℝ)*X 0 0+(5232576123/10000000000 : ℝ)*X 0 1+(5428708663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66297449/125000000 : ℝ)*X 1 0+(-2068636543/10000000000 : ℝ)*X 1 1+(5428708813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303795811/10000000000 : ℝ)*X 2 0+(5428708987/10000000000 : ℝ)*X 2 1+(-2068636453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181427903/5000000000 : ℝ)*X 0 0+(142569087/312500000 : ℝ)*X 0 1+(834447879/2000000000 : ℝ)*X 0 2+(2181427903/5000000000 : ℝ)*X 1 0+(142569087/312500000 : ℝ)*X 1 1+(834447879/2000000000 : ℝ)*X 1 2+(2181427903/5000000000 : ℝ)*X 2 0+(142569087/312500000 : ℝ)*X 2 1+(834447879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1622724234354091390724331351/232937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (885920799/50000000000000 : ℝ)*(base19) + (1675421153/100000000000000 : ℝ)*(base23) + (11764607/12500000000000 : ℝ)*(lower2) + (51662941/50000000000000 : ℝ)*(upper3) + (217114141/100000000000000 : ℝ)*(upper5) + (1900803357596731/50000000000000 : ℝ)*(major0) + (1900803357596731/50000000000000 : ℝ)*(major1) + (1900803357596731/50000000000000 : ℝ)*(major2) + (5058855147136671/100000000000000 : ℝ)*(sp0) + (2529443551972773/50000000000000 : ℝ)*(sp1) + (505888720036599/10000000000000 : ℝ)*(sp2) + (1272155015619719/50000000000000 : ℝ)*(sp3) + (33728650471/100000000000000 : ℝ)*(sp4) + (2858229731/20000000000000 : ℝ)*(sp7) + (636081080597023/25000000000000 : ℝ)*(f.failure) + (5058888875787143/100000000000000 : ℝ)*(f.sum) + (40501231475211/18635000000000000000000000000 : ℝ)*base66 + (833300606404310383/465875000000000000000000000000000 : ℝ)*base68 + (902639025441439617/465875000000000000000000000000000 : ℝ)*base69 + (2659049338894310383/465875000000000000000000000000000 : ℝ)*base72 + (2477105721913/9317500000000000000000000000 : ℝ)*base74 + (13020315079077685383/465875000000000000000000000000000 : ℝ)*base76 + (1230298522079189617/465875000000000000000000000000000 : ℝ)*base77 + (2688490343994060383/465875000000000000000000000000000 : ℝ)*base80 + (83706956739341/18635000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (6092453/1250000000000000000000 : ℝ)*base90 + (6092453/1250000000000000000000 : ℝ)*base92 + (6092453/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13539868915335801261807/2329375000000000000000000000 : ℝ) := by norm_num
    linear_combination (545521513/50000000000000 : ℝ)*(base19) + (121336083/10000000000000 : ℝ)*(base23) + (170582053/100000000000000 : ℝ)*(upper3) + (42957931/50000000000000 : ℝ)*(lower4) + (94439591/100000000000000 : ℝ)*(upper5) + (59866248941353/1562500000000 : ℝ)*(major0) + (59866248941353/1562500000000 : ℝ)*(major1) + (59866248941353/1562500000000 : ℝ)*(major2) + (5137647593/25000000000000 : ℝ)*(sp1) + (5489539287/20000000000000 : ℝ)*(sp2) + (637323586338739/12500000000000 : ℝ)*(sp4) + (1019713409815303/20000000000000 : ℝ)*(sp5) + (2549280014826323/50000000000000 : ℝ)*(sp6) + (1282145490013937/50000000000000 : ℝ)*(sp7) + (1282145490013937/50000000000000 : ℝ)*(f.failure) + (637323586338739/12500000000000 : ℝ)*(f.sum) + (15841932576779/4658750000000000000000000000 : ℝ)*base66 + (37933625189533221/14558593750000000000000000000000 : ℝ)*base67 + (22631521450136683/29117187500000000000000000000000 : ℝ)*base70 + (98573113196404279/14558593750000000000000000000000 : ℝ)*base72 + (3973566929981/18635000000000000000000000000 : ℝ)*base74 + (608025491935226491/58234375000000000000000000000000 : ℝ)*base76 + (495931327015929759/58234375000000000000000000000000 : ℝ)*base77 + (714207895785836009/58234375000000000000000000000000 : ℝ)*base79 + (13303292032413/9317500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (9667893/2500000000000000000000 : ℝ)*base89 + (9667893/2500000000000000000000 : ℝ)*base91 + (9667893/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1139_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14809/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1139_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1139_s4_0 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083756533/5000000000 : ℝ)*x 0 + (21101697/39062500 : ℝ)*x 1 + (2628637643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083756533/5000000000 : ℝ)^2083 ≤ (823051433319/6250000000000 : ℝ)^1571 := by
    have hnat : (1083756533 : ℕ)^2083*6250000000000^1571 ≤ 823051433319^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083756533 5000000000 823051433319 6250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21101697/39062500 : ℝ)^2083 ≤ (44197316166113/100000000000000 : ℝ)^1571 := by
    have hnat : (21101697 : ℕ)^2083*100000000000000^1571 ≤ 44197316166113^1571*39062500^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21101697 39062500 44197316166113 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628637643/5000000000 : ℝ)^2083 ≤ (1065846521989/2500000000000 : ℝ)^1571 := by
    have hnat : (2628637643 : ℕ)^2083*2500000000000^1571 ≤ 1065846521989^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628637643 5000000000 1065846521989 2500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083756533/5000000000 : ℝ), (21101697/39062500 : ℝ), (2628637643/5000000000 : ℝ)] ![(823051433319/6250000000000 : ℝ), (44197316166113/100000000000000 : ℝ), (1065846521989/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083756533/5000000000 : ℝ)|^2083 ≤ (823051433319/6250000000000 : ℝ)^1571
        have hw : |(-1083756533/5000000000 : ℝ)|=(1083756533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21101697/39062500 : ℝ)|^2083 ≤ (44197316166113/100000000000000 : ℝ)^1571
        have hw : |(21101697/39062500 : ℝ)|=(21101697/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628637643/5000000000 : ℝ)|^2083 ≤ (1065846521989/2500000000000 : ℝ)^1571
        have hw : |(2628637643/5000000000 : ℝ)|=(2628637643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s4_1 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347011799/10000000000 : ℝ)*x 0 + (-560270311/2500000000 : ℝ)*x 1 + (2628637909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347011799/10000000000 : ℝ)^2083 ≤ (43601420925641/100000000000000 : ℝ)^1571 := by
    have hnat : (5347011799 : ℕ)^2083*100000000000000^1571 ≤ 43601420925641^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347011799 10000000000 43601420925641 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560270311/2500000000 : ℝ)^2083 ≤ (2752942492763/20000000000000 : ℝ)^1571 := by
    have hnat : (560270311 : ℕ)^2083*20000000000000^1571 ≤ 2752942492763^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560270311 2500000000 2752942492763 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628637909/5000000000 : ℝ)^2083 ≤ (21316933299929/50000000000000 : ℝ)^1571 := by
    have hnat : (2628637909 : ℕ)^2083*50000000000000^1571 ≤ 21316933299929^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628637909 5000000000 21316933299929 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347011799/10000000000 : ℝ), (-560270311/2500000000 : ℝ), (2628637909/5000000000 : ℝ)] ![(43601420925641/100000000000000 : ℝ), (2752942492763/20000000000000 : ℝ), (21316933299929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347011799/10000000000 : ℝ)|^2083 ≤ (43601420925641/100000000000000 : ℝ)^1571
        have hw : |(5347011799/10000000000 : ℝ)|=(5347011799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560270311/2500000000 : ℝ)|^2083 ≤ (2752942492763/20000000000000 : ℝ)^1571
        have hw : |(-560270311/2500000000 : ℝ)|=(560270311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628637909/5000000000 : ℝ)|^2083 ≤ (21316933299929/50000000000000 : ℝ)^1571
        have hw : |(2628637909/5000000000 : ℝ)|=(2628637909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s4_2 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336753087/2500000000 : ℝ)*x 0 + (2628637421/5000000000 : ℝ)*x 1 + (-2241081803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336753087/2500000000 : ℝ)^2083 ≤ (21800713430691/50000000000000 : ℝ)^1571 := by
    have hnat : (1336753087 : ℕ)^2083*50000000000000^1571 ≤ 21800713430691^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336753087 2500000000 21800713430691 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628637421/5000000000 : ℝ)^2083 ≤ (10658464026369/25000000000000 : ℝ)^1571 := by
    have hnat : (2628637421 : ℕ)^2083*25000000000000^1571 ≤ 10658464026369^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628637421 5000000000 10658464026369 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241081803/10000000000 : ℝ)^2083 ≤ (13764717016153/100000000000000 : ℝ)^1571 := by
    have hnat : (2241081803 : ℕ)^2083*100000000000000^1571 ≤ 13764717016153^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241081803 10000000000 13764717016153 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336753087/2500000000 : ℝ), (2628637421/5000000000 : ℝ), (-2241081803/10000000000 : ℝ)] ![(21800713430691/50000000000000 : ℝ), (10658464026369/25000000000000 : ℝ), (13764717016153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336753087/2500000000 : ℝ)|^2083 ≤ (21800713430691/50000000000000 : ℝ)^1571
        have hw : |(1336753087/2500000000 : ℝ)|=(1336753087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628637421/5000000000 : ℝ)|^2083 ≤ (10658464026369/25000000000000 : ℝ)^1571
        have hw : |(2628637421/5000000000 : ℝ)|=(2628637421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241081803/10000000000 : ℝ)|^2083 ≤ (13764717016153/100000000000000 : ℝ)^1571
        have hw : |(-2241081803/10000000000 : ℝ)|=(2241081803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s4_3 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4364625391/10000000000 : ℝ)*x 0 + (2111536383/5000000000 : ℝ)*x 1 + (4510900243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364625391/10000000000 : ℝ)^2083 ≤ (33312187319337/100000000000000 : ℝ)^1571 := by
    have hnat : (4364625391 : ℕ)^2083*100000000000000^1571 ≤ 33312187319337^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364625391 10000000000 33312187319337 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111536383/5000000000 : ℝ)^2083 ≤ (15943669127243/50000000000000 : ℝ)^1571 := by
    have hnat : (2111536383 : ℕ)^2083*50000000000000^1571 ≤ 15943669127243^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111536383 5000000000 15943669127243 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510900243/10000000000 : ℝ)^2083 ≤ (3480047441373/10000000000000 : ℝ)^1571 := by
    have hnat : (4510900243 : ℕ)^2083*10000000000000^1571 ≤ 3480047441373^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510900243 10000000000 3480047441373 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364625391/10000000000 : ℝ), (2111536383/5000000000 : ℝ), (4510900243/10000000000 : ℝ)] ![(33312187319337/100000000000000 : ℝ), (15943669127243/50000000000000 : ℝ), (3480047441373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364625391/10000000000 : ℝ)|^2083 ≤ (33312187319337/100000000000000 : ℝ)^1571
        have hw : |(4364625391/10000000000 : ℝ)|=(4364625391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111536383/5000000000 : ℝ)|^2083 ≤ (15943669127243/50000000000000 : ℝ)^1571
        have hw : |(2111536383/5000000000 : ℝ)|=(2111536383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510900243/10000000000 : ℝ)|^2083 ≤ (3480047441373/10000000000000 : ℝ)^1571
        have hw : |(4510900243/10000000000 : ℝ)|=(4510900243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s4_4 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083760217/5000000000 : ℝ)*x 0 + (5257688083/10000000000 : ℝ)*x 1 + (337601237/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083760217/5000000000 : ℝ)^2083 ≤ (1646110285857/12500000000000 : ℝ)^1571 := by
    have hnat : (1083760217 : ℕ)^2083*12500000000000^1571 ≤ 1646110285857^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083760217 5000000000 1646110285857 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257688083/10000000000 : ℝ)^2083 ≤ (10659574877837/25000000000000 : ℝ)^1571 := by
    have hnat : (5257688083 : ℕ)^2083*25000000000000^1571 ≤ 10659574877837^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257688083 10000000000 10659574877837 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337601237/625000000 : ℝ)^2083 ≤ (4419281818737/10000000000000 : ℝ)^1571 := by
    have hnat : (337601237 : ℕ)^2083*10000000000000^1571 ≤ 4419281818737^1571*625000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337601237 625000000 4419281818737 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083760217/5000000000 : ℝ), (5257688083/10000000000 : ℝ), (337601237/625000000 : ℝ)] ![(1646110285857/12500000000000 : ℝ), (10659574877837/25000000000000 : ℝ), (4419281818737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083760217/5000000000 : ℝ)|^2083 ≤ (1646110285857/12500000000000 : ℝ)^1571
        have hw : |(-1083760217/5000000000 : ℝ)|=(1083760217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257688083/10000000000 : ℝ)|^2083 ≤ (10659574877837/25000000000000 : ℝ)^1571
        have hw : |(5257688083/10000000000 : ℝ)|=(5257688083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337601237/625000000 : ℝ)|^2083 ≤ (4419281818737/10000000000000 : ℝ)^1571
        have hw : |(337601237/625000000 : ℝ)|=(337601237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s4_5 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310347667/10000000000 : ℝ)*x 0 + (-16380753/78125000 : ℝ)*x 1 + (2700809741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310347667/10000000000 : ℝ)^2083 ≤ (43205455098609/100000000000000 : ℝ)^1571 := by
    have hnat : (5310347667 : ℕ)^2083*100000000000000^1571 ≤ 43205455098609^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310347667 10000000000 43205455098609 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16380753/78125000 : ℝ)^2083 ≤ (3150432515059/25000000000000 : ℝ)^1571 := by
    have hnat : (16380753 : ℕ)^2083*25000000000000^1571 ≤ 3150432515059^1571*78125000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16380753 78125000 3150432515059 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700809741/5000000000 : ℝ)^2083 ≤ (44192814824559/100000000000000 : ℝ)^1571 := by
    have hnat : (2700809741 : ℕ)^2083*100000000000000^1571 ≤ 44192814824559^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700809741 5000000000 44192814824559 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310347667/10000000000 : ℝ), (-16380753/78125000 : ℝ), (2700809741/5000000000 : ℝ)] ![(43205455098609/100000000000000 : ℝ), (3150432515059/25000000000000 : ℝ), (44192814824559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310347667/10000000000 : ℝ)|^2083 ≤ (43205455098609/100000000000000 : ℝ)^1571
        have hw : |(5310347667/10000000000 : ℝ)|=(5310347667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16380753/78125000 : ℝ)|^2083 ≤ (3150432515059/25000000000000 : ℝ)^1571
        have hw : |(-16380753/78125000 : ℝ)|=(16380753/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700809741/5000000000 : ℝ)|^2083 ≤ (44192814824559/100000000000000 : ℝ)^1571
        have hw : |(2700809741/5000000000 : ℝ)|=(2700809741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s4_6 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310347041/10000000000 : ℝ)*x 0 + (5401620283/10000000000 : ℝ)*x 1 + (-1048368071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310347041/10000000000 : ℝ)^2083 ≤ (43205448345511/100000000000000 : ℝ)^1571 := by
    have hnat : (5310347041 : ℕ)^2083*100000000000000^1571 ≤ 43205448345511^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310347041 10000000000 43205448345511 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401620283/10000000000 : ℝ)^2083 ≤ (44192823513629/100000000000000 : ℝ)^1571 := by
    have hnat : (5401620283 : ℕ)^2083*100000000000000^1571 ≤ 44192823513629^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401620283 10000000000 44192823513629 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048368071/5000000000 : ℝ)^2083 ≤ (12601728131757/100000000000000 : ℝ)^1571 := by
    have hnat : (1048368071 : ℕ)^2083*100000000000000^1571 ≤ 12601728131757^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048368071 5000000000 12601728131757 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310347041/10000000000 : ℝ), (5401620283/10000000000 : ℝ), (-1048368071/5000000000 : ℝ)] ![(43205448345511/100000000000000 : ℝ), (44192823513629/100000000000000 : ℝ), (12601728131757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310347041/10000000000 : ℝ)|^2083 ≤ (43205448345511/100000000000000 : ℝ)^1571
        have hw : |(5310347041/10000000000 : ℝ)|=(5310347041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401620283/10000000000 : ℝ)|^2083 ≤ (44192823513629/100000000000000 : ℝ)^1571
        have hw : |(5401620283/10000000000 : ℝ)|=(5401620283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048368071/5000000000 : ℝ)|^2083 ≤ (12601728131757/100000000000000 : ℝ)^1571
        have hw : |(-1048368071/5000000000 : ℝ)|=(1048368071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s4_7 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2182319491/5000000000 : ℝ)*x 0 + (4510079481/10000000000 : ℝ)*x 1 + (2111948783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182319491/5000000000 : ℝ)^2083 ≤ (33312324856763/100000000000000 : ℝ)^1571 := by
    have hnat : (2182319491 : ℕ)^2083*100000000000000^1571 ≤ 33312324856763^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182319491 5000000000 33312324856763 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510079481/10000000000 : ℝ)^2083 ≤ (17396039526223/50000000000000 : ℝ)^1571 := by
    have hnat : (4510079481 : ℕ)^2083*50000000000000^1571 ≤ 17396039526223^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510079481 10000000000 17396039526223 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111948783/5000000000 : ℝ)^2083 ≤ (15947798035819/50000000000000 : ℝ)^1571 := by
    have hnat : (2111948783 : ℕ)^2083*50000000000000^1571 ≤ 15947798035819^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111948783 5000000000 15947798035819 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182319491/5000000000 : ℝ), (4510079481/10000000000 : ℝ), (2111948783/5000000000 : ℝ)] ![(33312324856763/100000000000000 : ℝ), (17396039526223/50000000000000 : ℝ), (15947798035819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182319491/5000000000 : ℝ)|^2083 ≤ (33312324856763/100000000000000 : ℝ)^1571
        have hw : |(2182319491/5000000000 : ℝ)|=(2182319491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510079481/10000000000 : ℝ)|^2083 ≤ (17396039526223/50000000000000 : ℝ)^1571
        have hw : |(4510079481/10000000000 : ℝ)|=(4510079481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111948783/5000000000 : ℝ)|^2083 ≤ (15947798035819/50000000000000 : ℝ)^1571
        have hw : |(2111948783/5000000000 : ℝ)|=(2111948783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1139_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1117/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14809/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5313/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14809/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5313/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14809/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5313/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14809/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5313/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14809/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5313/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14809/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5313/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5313/50000 : ℝ) ^ (8331/2048 : ℝ) ≤ (171087360642773/1562500000000000000 : ℝ) := by
    have hpowers : (5313/50000 : ℝ)^8331 ≤ (171087360642773/1562500000000000000 : ℝ)^2048 := by
      have hnat : (5313 : ℕ)^8331*1562500000000000000^2048 ≤ 171087360642773^2048*50000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5313 50000 171087360642773 1562500000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5313/50000 : ℝ)) (X := (171087360642773/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14809/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (42247946718225939/100000000000000000000 : ℝ) := by
    have hpowers : (14809/100000 : ℝ)^8331 ≤ (42247946718225939/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14809 : ℕ)^8331*100000000000000000000^2048 ≤ 42247946718225939^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14809 100000 42247946718225939 100000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14809/100000 : ℝ)) (X := (42247946718225939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (781421087360642773/781250000000000000 : ℝ) ≤ (625033643786707/625000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (781421087360642773/781250000000000000 : ℝ)^2048 ≤ (625033643786707/625000000000000 : ℝ)^8331 := by
      have hnat : (781421087360642773 : ℕ)^2048*625000000000000^8331 ≤ 625033643786707^8331*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781421087360642773 781250000000000000 625033643786707 625000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033643786707/625000000000000 : ℝ)) (X := (781421087360642773/781250000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053197537799363411/100000000000000000000 : ℝ) ≤ (10001307486605467/10000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (100053197537799363411/100000000000000000000 : ℝ)^2048 ≤ (10001307486605467/10000000000000000 : ℝ)^8331 := by
      have hnat : (100053197537799363411 : ℕ)^2048*10000000000000000^8331 ≤ 10001307486605467^8331*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053197537799363411 100000000000000000000 10001307486605467 10000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001307486605467/10000000000000000 : ℝ)) (X := (100053197537799363411/100000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042247946718225939/50000000000000000000 : ℝ) ≤ (5001038336311811/5000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (50042247946718225939/50000000000000000000 : ℝ)^2048 ≤ (5001038336311811/5000000000000000 : ℝ)^8331 := by
      have hnat : (50042247946718225939 : ℕ)^2048*5000000000000000^8331 ≤ 5001038336311811^8331*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042247946718225939 50000000000000000000 5001038336311811 5000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001038336311811/5000000000000000 : ℝ)) (X := (50042247946718225939/50000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(171087360642773/1562500000000000000 : ℝ) ≤ ((10453976242524724009/10457500000000000000 : ℝ)+2*(153837203631/83660000000000 : ℝ)*(5313/50000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (10453976242524724009/10457500000000000000 : ℝ)+2*(153837203631/83660000000000 : ℝ)*(5313/50000 : ℝ)=(625033643786707/625000000000000 : ℝ) by norm_num, show 1+2*(171087360642773/1562500000000000000 : ℝ)=(781421087360642773/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42247946718225939/100000000000000000000 : ℝ)+(171087360642773/1562500000000000000 : ℝ) ≤ ((10453976242524724009/10457500000000000000 : ℝ)+(153837203631/83660000000000 : ℝ)*((14809/100000 : ℝ)+(5313/50000 : ℝ)))^(8331/2048 : ℝ) := by
    rw [show (10453976242524724009/10457500000000000000 : ℝ)+(153837203631/83660000000000 : ℝ)*((14809/100000 : ℝ)+(5313/50000 : ℝ))=(10001307486605467/10000000000000000 : ℝ) by norm_num, show 1+(42247946718225939/100000000000000000000 : ℝ)+(171087360642773/1562500000000000000 : ℝ)=(100053197537799363411/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42247946718225939/100000000000000000000 : ℝ) ≤ ((10453976242524724009/10457500000000000000 : ℝ)+2*(153837203631/83660000000000 : ℝ)*(14809/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (10453976242524724009/10457500000000000000 : ℝ)+2*(153837203631/83660000000000 : ℝ)*(14809/100000 : ℝ)=(5001038336311811/5000000000000000 : ℝ) by norm_num, show 1+2*(42247946718225939/100000000000000000000 : ℝ)=(50042247946718225939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10453976242524724009/10457500000000000000 : ℝ)*(X 1 0+X 2 0)+(153837203631/83660000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (5313/50000 : ℝ)) (hi := (14809/100000 : ℝ)) (c := (10453976242524724009/10457500000000000000 : ℝ)) (alpha := (153837203631/83660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10453976242524724009/10457500000000000000 : ℝ)*(X 0 1+X 2 1)+(153837203631/83660000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (5313/50000 : ℝ)) (hi := (14809/100000 : ℝ)) (c := (10453976242524724009/10457500000000000000 : ℝ)) (alpha := (153837203631/83660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10453976242524724009/10457500000000000000 : ℝ)*(X 0 2+X 1 2)+(153837203631/83660000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (5313/50000 : ℝ)) (hi := (14809/100000 : ℝ)) (c := (10453976242524724009/10457500000000000000 : ℝ)) (alpha := (153837203631/83660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1083756533/5000000000 : ℝ)*X 0 0+(21101697/39062500 : ℝ)*X 0 1+(2628637643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347011799/10000000000 : ℝ)*X 1 0+(-560270311/2500000000 : ℝ)*X 1 1+(2628637909/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336753087/2500000000 : ℝ)*X 2 0+(2628637421/5000000000 : ℝ)*X 2 1+(-2241081803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364625391/10000000000 : ℝ)*X 0 0+(2111536383/5000000000 : ℝ)*X 0 1+(4510900243/10000000000 : ℝ)*X 0 2+(4364625391/10000000000 : ℝ)*X 1 0+(2111536383/5000000000 : ℝ)*X 1 1+(4510900243/10000000000 : ℝ)*X 1 2+(4364625391/10000000000 : ℝ)*X 2 0+(2111536383/5000000000 : ℝ)*X 2 1+(4510900243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1083760217/5000000000 : ℝ)*X 0 0+(5257688083/10000000000 : ℝ)*X 0 1+(337601237/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310347667/10000000000 : ℝ)*X 1 0+(-16380753/78125000 : ℝ)*X 1 1+(2700809741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310347041/10000000000 : ℝ)*X 2 0+(5401620283/10000000000 : ℝ)*X 2 1+(-1048368071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182319491/5000000000 : ℝ)*X 0 0+(4510079481/10000000000 : ℝ)*X 0 1+(2111948783/5000000000 : ℝ)*X 0 2+(2182319491/5000000000 : ℝ)*X 1 0+(4510079481/10000000000 : ℝ)*X 1 1+(2111948783/5000000000 : ℝ)*X 1 2+(2182319491/5000000000 : ℝ)*X 2 0+(4510079481/10000000000 : ℝ)*X 2 1+(2111948783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250585858006000322088707571/65359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49562423/50000000000000 : ℝ)*(base15) + (560542357/100000000000000 : ℝ)*(base29) + (178488011/50000000000000 : ℝ)*(lower2) + (21732119/100000000000000 : ℝ)*(upper3) + (2991499/2000000000000 : ℝ)*(lower4) + (1038234636075927/20000000000000 : ℝ)*(major0) + (648896717615249/12500000000000 : ℝ)*(major1) + (648896717615249/12500000000000 : ℝ)*(major2) + (1381603820557319/20000000000000 : ℝ)*(sp0) + (6908018443119391/100000000000000 : ℝ)*(sp1) + (172699606298461/2500000000000 : ℝ)*(sp2) + (1737156967141479/50000000000000 : ℝ)*(sp3) + (8572576449/25000000000000 : ℝ)*(sp6) + (715848771/5000000000000 : ℝ)*(sp7) + (1737164125629189/50000000000000 : ℝ)*(f.failure) + (1381603820557319/20000000000000 : ℝ)*(f.sum) + (3639054647483/1045750000000000000000000000 : ℝ)*base66 + (2376637769782311759/130718750000000000000000000000000 : ℝ)*base68 + (1998750751865686759/130718750000000000000000000000000 : ℝ)*base70 + (8099055302510581343/209150000000000000000000000000000 : ℝ)*base71 + (26458630122867/8366000000000000000000000000 : ℝ)*base74 + (11332604562513953/734375000000000000000000000000 : ℝ)*base76 + (18326401414864468657/209150000000000000000000000000000 : ℝ)*base78 + (80505116701453/734375000000000000000000000000 : ℝ)*base80 + (30153844509531/1673200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (18215321/2500000000000000000000 : ℝ)*base89 + (18215321/2500000000000000000000 : ℝ)*base91 + (18215321/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86447301633666278987772423/13071875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138854629/20000000000000 : ℝ)*(base19) + (284582227/100000000000000 : ℝ)*(base23) + (27311527/100000000000000 : ℝ)*(upper3) + (159365373/100000000000000 : ℝ)*(lower4) + (130525342392849/2500000000000 : ℝ)*(major0) + (130525342392849/2500000000000 : ℝ)*(major1) + (130525342392849/2500000000000 : ℝ)*(major2) + (1326038847/25000000000000 : ℝ)*(sp1) + (21123366487/100000000000000 : ℝ)*(sp2) + (11301385259/100000000000000 : ℝ)*(sp3) + (6947727752681557/100000000000000 : ℝ)*(sp4) + (217116304820407/3125000000000 : ℝ)*(sp5) + (6947706344732843/100000000000000 : ℝ)*(sp6) + (54598251826877/1562500000000 : ℝ)*(sp7) + (873574854576347/25000000000000 : ℝ)*(f.failure) + (6947727752681557/100000000000000 : ℝ)*(f.sum) + (36015409624219/4183000000000000000000000000 : ℝ)*base65 + (295340794981907109/26143750000000000000000000000000 : ℝ)*base68 + (323726824772457109/26143750000000000000000000000000 : ℝ)*base70 + (507760596130992891/26143750000000000000000000000000 : ℝ)*base71 + (2557966263391/2091500000000000000000000000 : ℝ)*base74 + (524459708721607109/26143750000000000000000000000000 : ℝ)*base76 + (262337946428011641/26143750000000000000000000000000 : ℝ)*base77 + (344577042024007109/26143750000000000000000000000000 : ℝ)*base80 + (14858379764833/2091500000000000000000000000 : ℝ)*base81 + (797383/1250000000000000000000 : ℝ)*base89 + (797383/1250000000000000000000 : ℝ)*base91 + (797383/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1139_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1139_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1139_s5_0 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084078159/5000000000 : ℝ)*x 0 + (1348747317/2500000000 : ℝ)*x 1 + (1315974571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084078159/5000000000 : ℝ)^2083 ≤ (411687655299/3125000000000 : ℝ)^1571 := by
    have hnat : (1084078159 : ℕ)^2083*3125000000000^1571 ≤ 411687655299^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084078159 5000000000 411687655299 3125000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348747317/2500000000 : ℝ)^2083 ≤ (22060453064593/50000000000000 : ℝ)^1571 := by
    have hnat : (1348747317 : ℕ)^2083*50000000000000^1571 ≤ 22060453064593^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348747317 2500000000 22060453064593 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315974571/2500000000 : ℝ)^2083 ≤ (10676272220867/25000000000000 : ℝ)^1571 := by
    have hnat : (1315974571 : ℕ)^2083*25000000000000^1571 ≤ 10676272220867^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315974571 2500000000 10676272220867 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084078159/5000000000 : ℝ), (1348747317/2500000000 : ℝ), (1315974571/2500000000 : ℝ)] ![(411687655299/3125000000000 : ℝ), (22060453064593/50000000000000 : ℝ), (10676272220867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084078159/5000000000 : ℝ)|^2083 ≤ (411687655299/3125000000000 : ℝ)^1571
        have hw : |(-1084078159/5000000000 : ℝ)|=(1084078159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348747317/2500000000 : ℝ)|^2083 ≤ (22060453064593/50000000000000 : ℝ)^1571
        have hw : |(1348747317/2500000000 : ℝ)|=(1348747317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315974571/2500000000 : ℝ)|^2083 ≤ (10676272220867/25000000000000 : ℝ)^1571
        have hw : |(1315974571/2500000000 : ℝ)|=(1315974571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s5_1 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672623329/5000000000 : ℝ)*x 0 + (-2234675821/10000000000 : ℝ)*x 1 + (2631949183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672623329/5000000000 : ℝ)^2083 ≤ (43582337399543/100000000000000 : ℝ)^1571 := by
    have hnat : (2672623329 : ℕ)^2083*100000000000000^1571 ≤ 43582337399543^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672623329 5000000000 43582337399543 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2234675821/10000000000 : ℝ)^2083 ≤ (1714071603519/12500000000000 : ℝ)^1571 := by
    have hnat : (2234675821 : ℕ)^2083*12500000000000^1571 ≤ 1714071603519^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234675821 10000000000 1714071603519 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631949183/5000000000 : ℝ)^2083 ≤ (4270508976553/10000000000000 : ℝ)^1571 := by
    have hnat : (2631949183 : ℕ)^2083*10000000000000^1571 ≤ 4270508976553^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631949183 5000000000 4270508976553 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672623329/5000000000 : ℝ), (-2234675821/10000000000 : ℝ), (2631949183/5000000000 : ℝ)] ![(43582337399543/100000000000000 : ℝ), (1714071603519/12500000000000 : ℝ), (4270508976553/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672623329/5000000000 : ℝ)|^2083 ≤ (43582337399543/100000000000000 : ℝ)^1571
        have hw : |(2672623329/5000000000 : ℝ)|=(2672623329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2234675821/10000000000 : ℝ)|^2083 ≤ (1714071603519/12500000000000 : ℝ)^1571
        have hw : |(-2234675821/10000000000 : ℝ)|=(2234675821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631949183/5000000000 : ℝ)|^2083 ≤ (4270508976553/10000000000000 : ℝ)^1571
        have hw : |(2631949183/5000000000 : ℝ)|=(2631949183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s5_2 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345246373/10000000000 : ℝ)*x 0 + (2631949323/5000000000 : ℝ)*x 1 + (-558668957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345246373/10000000000 : ℝ)^2083 ≤ (43582334318479/100000000000000 : ℝ)^1571 := by
    have hnat : (5345246373 : ℕ)^2083*100000000000000^1571 ≤ 43582334318479^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345246373 10000000000 43582334318479 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631949323/5000000000 : ℝ)^2083 ≤ (42705092777449/100000000000000 : ℝ)^1571 := by
    have hnat : (2631949323 : ℕ)^2083*100000000000000^1571 ≤ 42705092777449^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631949323 5000000000 42705092777449 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558668957/2500000000 : ℝ)^2083 ≤ (857035805319/6250000000000 : ℝ)^1571 := by
    have hnat : (558668957 : ℕ)^2083*6250000000000^1571 ≤ 857035805319^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558668957 2500000000 857035805319 6250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345246373/10000000000 : ℝ), (2631949323/5000000000 : ℝ), (-558668957/2500000000 : ℝ)] ![(43582334318479/100000000000000 : ℝ), (42705092777449/100000000000000 : ℝ), (857035805319/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345246373/10000000000 : ℝ)|^2083 ≤ (43582334318479/100000000000000 : ℝ)^1571
        have hw : |(5345246373/10000000000 : ℝ)|=(5345246373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631949323/5000000000 : ℝ)|^2083 ≤ (42705092777449/100000000000000 : ℝ)^1571
        have hw : |(2631949323/5000000000 : ℝ)|=(2631949323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558668957/2500000000 : ℝ)|^2083 ≤ (857035805319/6250000000000 : ℝ)^1571
        have hw : |(-558668957/2500000000 : ℝ)|=(558668957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s5_3 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4365000743/10000000000 : ℝ)*x 0 + (1059153491/2500000000 : ℝ)*x 1 + (562157741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365000743/10000000000 : ℝ)^2083 ≤ (8328996459097/25000000000000 : ℝ)^1571 := by
    have hnat : (4365000743 : ℕ)^2083*25000000000000^1571 ≤ 8328996459097^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365000743 10000000000 8328996459097 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059153491/2500000000 : ℝ)^2083 ≤ (16011488939199/50000000000000 : ℝ)^1571 := by
    have hnat : (1059153491 : ℕ)^2083*50000000000000^1571 ≤ 16011488939199^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059153491 2500000000 16011488939199 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562157741/1250000000 : ℝ)^2083 ≤ (17330518137233/50000000000000 : ℝ)^1571 := by
    have hnat : (562157741 : ℕ)^2083*50000000000000^1571 ≤ 17330518137233^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562157741 1250000000 17330518137233 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365000743/10000000000 : ℝ), (1059153491/2500000000 : ℝ), (562157741/1250000000 : ℝ)] ![(8328996459097/25000000000000 : ℝ), (16011488939199/50000000000000 : ℝ), (17330518137233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365000743/10000000000 : ℝ)|^2083 ≤ (8328996459097/25000000000000 : ℝ)^1571
        have hw : |(4365000743/10000000000 : ℝ)|=(4365000743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059153491/2500000000 : ℝ)|^2083 ≤ (16011488939199/50000000000000 : ℝ)^1571
        have hw : |(1059153491/2500000000 : ℝ)|=(1059153491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562157741/1250000000 : ℝ)|^2083 ≤ (17330518137233/50000000000000 : ℝ)^1571
        have hw : |(562157741/1250000000 : ℝ)|=(562157741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s5_4 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168161487/10000000000 : ℝ)*x 0 + (1052847461/2000000000 : ℝ)*x 1 + (5394649107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168161487/10000000000 : ℝ)^2083 ≤ (13174046613049/100000000000000 : ℝ)^1571 := by
    have hnat : (2168161487 : ℕ)^2083*100000000000000^1571 ≤ 13174046613049^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168161487 10000000000 13174046613049 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052847461/2000000000 : ℝ)^2083 ≤ (2135436786037/5000000000000 : ℝ)^1571 := by
    have hnat : (1052847461 : ℕ)^2083*5000000000000^1571 ≤ 2135436786037^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052847461 2000000000 2135436786037 5000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394649107/10000000000 : ℝ)^2083 ≤ (4411721765303/10000000000000 : ℝ)^1571 := by
    have hnat : (5394649107 : ℕ)^2083*10000000000000^1571 ≤ 4411721765303^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394649107 10000000000 4411721765303 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168161487/10000000000 : ℝ), (1052847461/2000000000 : ℝ), (5394649107/10000000000 : ℝ)] ![(13174046613049/100000000000000 : ℝ), (2135436786037/5000000000000 : ℝ), (4411721765303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168161487/10000000000 : ℝ)|^2083 ≤ (13174046613049/100000000000000 : ℝ)^1571
        have hw : |(-2168161487/10000000000 : ℝ)|=(2168161487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052847461/2000000000 : ℝ)|^2083 ≤ (2135436786037/5000000000000 : ℝ)^1571
        have hw : |(1052847461/2000000000 : ℝ)|=(1052847461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394649107/10000000000 : ℝ)|^2083 ≤ (4411721765303/10000000000000 : ℝ)^1571
        have hw : |(5394649107/10000000000 : ℝ)|=(5394649107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s5_5 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328010489/2500000000 : ℝ)*x 0 + (-2103925179/10000000000 : ℝ)*x 1 + (1348662273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328010489/2500000000 : ℝ)^2083 ≤ (540296669051/1250000000000 : ℝ)^1571 := by
    have hnat : (1328010489 : ℕ)^2083*1250000000000^1571 ≤ 540296669051^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328010489 2500000000 540296669051 1250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103925179/10000000000 : ℝ)^2083 ≤ (12659048968461/100000000000000 : ℝ)^1571 := by
    have hnat : (2103925179 : ℕ)^2083*100000000000000^1571 ≤ 12659048968461^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103925179 10000000000 12659048968461 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348662273/2500000000 : ℝ)^2083 ≤ (22058608745191/50000000000000 : ℝ)^1571 := by
    have hnat : (1348662273 : ℕ)^2083*50000000000000^1571 ≤ 22058608745191^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348662273 2500000000 22058608745191 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328010489/2500000000 : ℝ), (-2103925179/10000000000 : ℝ), (1348662273/2500000000 : ℝ)] ![(540296669051/1250000000000 : ℝ), (12659048968461/100000000000000 : ℝ), (22058608745191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328010489/2500000000 : ℝ)|^2083 ≤ (540296669051/1250000000000 : ℝ)^1571
        have hw : |(1328010489/2500000000 : ℝ)|=(1328010489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103925179/10000000000 : ℝ)|^2083 ≤ (12659048968461/100000000000000 : ℝ)^1571
        have hw : |(-2103925179/10000000000 : ℝ)|=(2103925179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348662273/2500000000 : ℝ)|^2083 ≤ (22058608745191/50000000000000 : ℝ)^1571
        have hw : |(1348662273/2500000000 : ℝ)|=(1348662273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s5_6 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106240839/200000000 : ℝ)*x 0 + (674331137/1250000000 : ℝ)*x 1 + (-1051962591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106240839/200000000 : ℝ)^2083 ≤ (43223733459347/100000000000000 : ℝ)^1571 := by
    have hnat : (106240839 : ℕ)^2083*100000000000000^1571 ≤ 43223733459347^1571*200000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106240839 200000000 43223733459347 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674331137/1250000000 : ℝ)^2083 ≤ (8823443506751/20000000000000 : ℝ)^1571 := by
    have hnat : (674331137 : ℕ)^2083*20000000000000^1571 ≤ 8823443506751^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674331137 1250000000 8823443506751 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051962591/5000000000 : ℝ)^2083 ≤ (6329524496197/50000000000000 : ℝ)^1571 := by
    have hnat : (1051962591 : ℕ)^2083*50000000000000^1571 ≤ 6329524496197^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051962591 5000000000 6329524496197 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106240839/200000000 : ℝ), (674331137/1250000000 : ℝ), (-1051962591/5000000000 : ℝ)] ![(43223733459347/100000000000000 : ℝ), (8823443506751/20000000000000 : ℝ), (6329524496197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106240839/200000000 : ℝ)|^2083 ≤ (43223733459347/100000000000000 : ℝ)^1571
        have hw : |(106240839/200000000 : ℝ)|=(106240839/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674331137/1250000000 : ℝ)|^2083 ≤ (8823443506751/20000000000000 : ℝ)^1571
        have hw : |(674331137/1250000000 : ℝ)|=(674331137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051962591/5000000000 : ℝ)|^2083 ≤ (6329524496197/50000000000000 : ℝ)^1571
        have hw : |(-1051962591/5000000000 : ℝ)|=(1051962591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s5_7 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4365011329/10000000000 : ℝ)*x 0 + (4496588331/10000000000 : ℝ)*x 1 + (4237290071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365011329/10000000000 : ℝ)^2083 ≤ (33316092966977/100000000000000 : ℝ)^1571 := by
    have hnat : (4365011329 : ℕ)^2083*100000000000000^1571 ≤ 33316092966977^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365011329 10000000000 33316092966977 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496588331/10000000000 : ℝ)^2083 ≤ (346541529857/1000000000000 : ℝ)^1571 := by
    have hnat : (4496588331 : ℕ)^2083*1000000000000^1571 ≤ 346541529857^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496588331 10000000000 346541529857 1000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237290071/10000000000 : ℝ)^2083 ≤ (8007438505623/25000000000000 : ℝ)^1571 := by
    have hnat : (4237290071 : ℕ)^2083*25000000000000^1571 ≤ 8007438505623^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237290071 10000000000 8007438505623 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365011329/10000000000 : ℝ), (4496588331/10000000000 : ℝ), (4237290071/10000000000 : ℝ)] ![(33316092966977/100000000000000 : ℝ), (346541529857/1000000000000 : ℝ), (8007438505623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365011329/10000000000 : ℝ)|^2083 ≤ (33316092966977/100000000000000 : ℝ)^1571
        have hw : |(4365011329/10000000000 : ℝ)|=(4365011329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496588331/10000000000 : ℝ)|^2083 ≤ (346541529857/1000000000000 : ℝ)^1571
        have hw : |(4496588331/10000000000 : ℝ)|=(4496588331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237290071/10000000000 : ℝ)|^2083 ≤ (8007438505623/25000000000000 : ℝ)^1571
        have hw : |(4237290071/10000000000 : ℝ)|=(4237290071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1139_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1117/10000 : ℝ) ^ (8331/2048 : ℝ) ≤ (6707690637161513/50000000000000000000 : ℝ) := by
    have hpowers : (1117/10000 : ℝ)^8331 ≤ (6707690637161513/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1117 : ℕ)^8331*50000000000000000000^2048 ≤ 6707690637161513^2048*10000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1117 10000 6707690637161513 50000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1117/10000 : ℝ)) (X := (6707690637161513/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8331/2048 : ℝ) ≤ (17986113755687019/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8331 ≤ (17986113755687019/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8331*50000000000000000000^2048 ≤ 17986113755687019^2048*20000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17986113755687019 50000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17986113755687019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006707690637161513/25000000000000000000 : ℝ) ≤ (10000659510779851/10000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (25006707690637161513/25000000000000000000 : ℝ)^2048 ≤ (10000659510779851/10000000000000000 : ℝ)^8331 := by
      have hnat : (25006707690637161513 : ℕ)^2048*10000000000000000^8331 ≤ 10000659510779851^8331*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006707690637161513 25000000000000000000 10000659510779851 10000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000659510779851/10000000000000000 : ℝ)) (X := (25006707690637161513/25000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506173451098212133/12500000000000000000 : ℝ) ≤ (10001213863779679/10000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (12506173451098212133/12500000000000000000 : ℝ)^2048 ≤ (10001213863779679/10000000000000000 : ℝ)^8331 := by
      have hnat : (12506173451098212133 : ℕ)^2048*10000000000000000^8331 ≤ 10001213863779679^8331*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506173451098212133 12500000000000000000 10001213863779679 10000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001213863779679/10000000000000000 : ℝ)) (X := (12506173451098212133/12500000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017986113755687019/25000000000000000000 : ℝ) ≤ (10001768216779507/10000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (25017986113755687019/25000000000000000000 : ℝ)^2048 ≤ (10001768216779507/10000000000000000 : ℝ)^8331 := by
      have hnat : (25017986113755687019 : ℕ)^2048*10000000000000000^8331 ≤ 10001768216779507^8331*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017986113755687019 25000000000000000000 10001768216779507 10000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001768216779507/10000000000000000 : ℝ)) (X := (25017986113755687019/25000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6707690637161513/50000000000000000000 : ℝ) ≤ ((6127927430904817159/6130000000000000000 : ℝ)+2*(138588249957/76625000000000 : ℝ)*(1117/10000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (6127927430904817159/6130000000000000000 : ℝ)+2*(138588249957/76625000000000 : ℝ)*(1117/10000 : ℝ)=(10000659510779851/10000000000000000 : ℝ) by norm_num, show 1+2*(6707690637161513/50000000000000000000 : ℝ)=(25006707690637161513/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17986113755687019/50000000000000000000 : ℝ)+(6707690637161513/50000000000000000000 : ℝ) ≤ ((6127927430904817159/6130000000000000000 : ℝ)+(138588249957/76625000000000 : ℝ)*((2847/20000 : ℝ)+(1117/10000 : ℝ)))^(8331/2048 : ℝ) := by
    rw [show (6127927430904817159/6130000000000000000 : ℝ)+(138588249957/76625000000000 : ℝ)*((2847/20000 : ℝ)+(1117/10000 : ℝ))=(10001213863779679/10000000000000000 : ℝ) by norm_num, show 1+(17986113755687019/50000000000000000000 : ℝ)+(6707690637161513/50000000000000000000 : ℝ)=(12506173451098212133/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17986113755687019/50000000000000000000 : ℝ) ≤ ((6127927430904817159/6130000000000000000 : ℝ)+2*(138588249957/76625000000000 : ℝ)*(2847/20000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (6127927430904817159/6130000000000000000 : ℝ)+2*(138588249957/76625000000000 : ℝ)*(2847/20000 : ℝ)=(10001768216779507/10000000000000000 : ℝ) by norm_num, show 1+2*(17986113755687019/50000000000000000000 : ℝ)=(25017986113755687019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6127927430904817159/6130000000000000000 : ℝ)*(X 1 0+X 2 0)+(138588249957/76625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (6127927430904817159/6130000000000000000 : ℝ)) (alpha := (138588249957/76625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6127927430904817159/6130000000000000000 : ℝ)*(X 0 1+X 2 1)+(138588249957/76625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (6127927430904817159/6130000000000000000 : ℝ)) (alpha := (138588249957/76625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6127927430904817159/6130000000000000000 : ℝ)*(X 0 2+X 1 2)+(138588249957/76625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (6127927430904817159/6130000000000000000 : ℝ)) (alpha := (138588249957/76625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1084078159/5000000000 : ℝ)*X 0 0+(1348747317/2500000000 : ℝ)*X 0 1+(1315974571/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672623329/5000000000 : ℝ)*X 1 0+(-2234675821/10000000000 : ℝ)*X 1 1+(2631949183/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345246373/10000000000 : ℝ)*X 2 0+(2631949323/5000000000 : ℝ)*X 2 1+(-558668957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365000743/10000000000 : ℝ)*X 0 0+(1059153491/2500000000 : ℝ)*X 0 1+(562157741/1250000000 : ℝ)*X 0 2+(4365000743/10000000000 : ℝ)*X 1 0+(1059153491/2500000000 : ℝ)*X 1 1+(562157741/1250000000 : ℝ)*X 1 2+(4365000743/10000000000 : ℝ)*X 2 0+(1059153491/2500000000 : ℝ)*X 2 1+(562157741/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2168161487/10000000000 : ℝ)*X 0 0+(1052847461/2000000000 : ℝ)*X 0 1+(5394649107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328010489/2500000000 : ℝ)*X 1 0+(-2103925179/10000000000 : ℝ)*X 1 1+(1348662273/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106240839/200000000 : ℝ)*X 2 0+(674331137/1250000000 : ℝ)*X 2 1+(-1051962591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365011329/10000000000 : ℝ)*X 0 0+(4496588331/10000000000 : ℝ)*X 0 1+(4237290071/10000000000 : ℝ)*X 0 2+(4365011329/10000000000 : ℝ)*X 1 0+(4496588331/10000000000 : ℝ)*X 1 1+(4237290071/10000000000 : ℝ)*X 1 2+(4365011329/10000000000 : ℝ)*X 2 0+(4496588331/10000000000 : ℝ)*X 2 1+(4237290071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22751741122436178534227697/4789062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (700850103/50000000000000 : ℝ)*(base19) + (83806117/10000000000000 : ℝ)*(base23) + (129340143/50000000000000 : ℝ)*(upper3) + (41935189/50000000000000 : ℝ)*(upper4) + (57308233/100000000000000 : ℝ)*(upper5) + (349883915706/6103515625 : ℝ)*(major0) + (349883915706/6103515625 : ℝ)*(major1) + (349883915706/6103515625 : ℝ)*(major2) + (7628336555955313/100000000000000 : ℝ)*(sp0) + (3814185463509397/50000000000000 : ℝ)*(sp1) + (762837149065783/10000000000000 : ℝ)*(sp2) + (191830332367341/5000000000000 : ℝ)*(sp3) + (35772763687/100000000000000 : ℝ)*(sp4) + (17015429331/100000000000000 : ℝ)*(sp7) + (76732473255523/2000000000000 : ℝ)*(f.failure) + (7628372328719/100000000000 : ℝ)*(f.sum) + (10284951416239/1915625000000000000000000000 : ℝ)*base65 + (39571419042360869/2394531250000000000000000000000 : ℝ)*base68 + (6022274849450137/4789062500000000000000000000000 : ℝ)*base69 + (67037672868634649/9578125000000000000000000000000 : ℝ)*base71 + (64042157096163/15325000000000000000000000000 : ℝ)*base74 + (121186500526709101/9578125000000000000000000000000 : ℝ)*base76 + (111688800015646601/9578125000000000000000000000000 : ℝ)*base78 + (386331002974021601/9578125000000000000000000000000 : ℝ)*base80 + (64012381448713/15325000000000000000000000000 : ℝ)*base82 + (264047/100000000000000000000 : ℝ)*base89 + (264047/100000000000000000000 : ℝ)*base91 + (264047/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84681287562516082465611/7662500000000000000000000000 : ℝ) := by norm_num
    linear_combination (208736291/10000000000000 : ℝ)*(base19) + (2254035779/100000000000000 : ℝ)*(base23) + (44348583/20000000000000 : ℝ)*(upper3) + (1600217/2000000000000 : ℝ)*(lower4) + (222046649/100000000000000 : ℝ)*(upper5) + (2881144463893729/50000000000000 : ℝ)*(major0) + (2881144463893729/50000000000000 : ℝ)*(major1) + (2881144463893729/50000000000000 : ℝ)*(major2) + (11136594847/20000000000000 : ℝ)*(sp1) + (14909229243/25000000000000 : ℝ)*(sp2) + (383400776005941/5000000000000 : ℝ)*(sp4) + (306718309991267/4000000000000 : ℝ)*(sp5) + (1916988407291517/25000000000000 : ℝ)*(sp6) + (385656196707637/10000000000000 : ℝ)*(sp7) + (385656196707637/10000000000000 : ℝ)*(f.failure) + (383400776005941/5000000000000 : ℝ)*(f.sum) + (13835793915237/7662500000000000000000000000 : ℝ)*base65 + (4287871724181064089/306500000000000000000000000000000 : ℝ)*base68 + (3259011739541064089/306500000000000000000000000000000 : ℝ)*base70 + (1937044336766064089/306500000000000000000000000000000 : ℝ)*base72 + (51692077199263/7662500000000000000000000000 : ℝ)*base74 + (1943306129553935911/306500000000000000000000000000000 : ℝ)*base75 + (11105760964935911/306500000000000000000000000000000 : ℝ)*base77 + (2388092330608935911/306500000000000000000000000000000 : ℝ)*base79 + (37755318131563/7662500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8157193/500000000000000000000 : ℝ)*base89 + (8157193/500000000000000000000 : ℝ)*base91 + (8157193/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1139_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1139_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1139_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1139_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1139_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1139_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1139_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
