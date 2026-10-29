-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1647_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:12:30.886782+00:00
-- url     : https://prove2.me/submissions/12ec174a-f0b1-4663-9535-5dc0799cad88

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
theorem support_rectangle_w1647_s3_0 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1615362899/10000000000 : ℝ)*x 0 + (2724252381/5000000000 : ℝ)*x 1 + (323977333/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1615362899/10000000000 : ℝ)^4907 ≤ (998803704039/10000000000000 : ℝ)^3883 := by
    have hnat : (1615362899 : ℕ)^4907*10000000000000^3883 ≤ 998803704039^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615362899 10000000000 998803704039 10000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724252381/5000000000 : ℝ)^4907 ≤ (11605666428057/25000000000000 : ℝ)^3883 := by
    have hnat : (2724252381 : ℕ)^4907*25000000000000^3883 ≤ 11605666428057^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724252381 5000000000 11605666428057 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323977333/625000000 : ℝ)^4907 ≤ (43589297238493/100000000000000 : ℝ)^3883 := by
    have hnat : (323977333 : ℕ)^4907*100000000000000^3883 ≤ 43589297238493^3883*625000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323977333 625000000 43589297238493 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1615362899/10000000000 : ℝ), (2724252381/5000000000 : ℝ), (323977333/625000000 : ℝ)] ![(998803704039/10000000000000 : ℝ), (11605666428057/25000000000000 : ℝ), (43589297238493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1615362899/10000000000 : ℝ)|^4907 ≤ (998803704039/10000000000000 : ℝ)^3883
        have hw : |(-1615362899/10000000000 : ℝ)|=(1615362899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724252381/5000000000 : ℝ)|^4907 ≤ (11605666428057/25000000000000 : ℝ)^3883
        have hw : |(2724252381/5000000000 : ℝ)|=(2724252381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323977333/625000000 : ℝ)|^4907 ≤ (43589297238493/100000000000000 : ℝ)^3883
        have hw : |(323977333/625000000 : ℝ)|=(323977333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s3_1 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348217089/10000000000 : ℝ)*x 0 + (-218966589/1250000000 : ℝ)*x 1 + (5183637297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348217089/10000000000 : ℝ)^4907 ≤ (22672742176511/50000000000000 : ℝ)^3883 := by
    have hnat : (5348217089 : ℕ)^4907*50000000000000^3883 ≤ 22672742176511^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348217089 10000000000 22672742176511 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218966589/1250000000 : ℝ)^4907 ≤ (11065218723067/100000000000000 : ℝ)^3883 := by
    have hnat : (218966589 : ℕ)^4907*100000000000000^3883 ≤ 11065218723067^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218966589 1250000000 11065218723067 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183637297/10000000000 : ℝ)^4907 ≤ (43589296909069/100000000000000 : ℝ)^3883 := by
    have hnat : (5183637297 : ℕ)^4907*100000000000000^3883 ≤ 43589296909069^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183637297 10000000000 43589296909069 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348217089/10000000000 : ℝ), (-218966589/1250000000 : ℝ), (5183637297/10000000000 : ℝ)] ![(22672742176511/50000000000000 : ℝ), (11065218723067/100000000000000 : ℝ), (43589296909069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348217089/10000000000 : ℝ)|^4907 ≤ (22672742176511/50000000000000 : ℝ)^3883
        have hw : |(5348217089/10000000000 : ℝ)|=(5348217089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218966589/1250000000 : ℝ)|^4907 ≤ (11065218723067/100000000000000 : ℝ)^3883
        have hw : |(-218966589/1250000000 : ℝ)|=(218966589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183637297/10000000000 : ℝ)|^4907 ≤ (43589296909069/100000000000000 : ℝ)^3883
        have hw : |(5183637297/10000000000 : ℝ)|=(5183637297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s3_2 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534821707/1000000000 : ℝ)*x 0 + (5183637271/10000000000 : ℝ)*x 1 + (-437933193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534821707/1000000000 : ℝ)^4907 ≤ (9069096829889/20000000000000 : ℝ)^3883 := by
    have hnat : (534821707 : ℕ)^4907*20000000000000^3883 ≤ 9069096829889^3883*1000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534821707 1000000000 9069096829889 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183637271/10000000000 : ℝ)^4907 ≤ (21794648316389/50000000000000 : ℝ)^3883 := by
    have hnat : (5183637271 : ℕ)^4907*50000000000000^3883 ≤ 21794648316389^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183637271 10000000000 21794648316389 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437933193/2500000000 : ℝ)^4907 ≤ (11065219202019/100000000000000 : ℝ)^3883 := by
    have hnat : (437933193 : ℕ)^4907*100000000000000^3883 ≤ 11065219202019^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437933193 2500000000 11065219202019 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534821707/1000000000 : ℝ), (5183637271/10000000000 : ℝ), (-437933193/2500000000 : ℝ)] ![(9069096829889/20000000000000 : ℝ), (21794648316389/50000000000000 : ℝ), (11065219202019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534821707/1000000000 : ℝ)|^4907 ≤ (9069096829889/20000000000000 : ℝ)^3883
        have hw : |(534821707/1000000000 : ℝ)|=(534821707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183637271/10000000000 : ℝ)|^4907 ≤ (21794648316389/50000000000000 : ℝ)^3883
        have hw : |(5183637271/10000000000 : ℝ)|=(5183637271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437933193/2500000000 : ℝ)|^4907 ≤ (11065219202019/100000000000000 : ℝ)^3883
        have hw : |(-437933193/2500000000 : ℝ)|=(437933193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s3_3 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183021273/10000000000 : ℝ)*x 0 + (192591083/500000000 : ℝ)*x 1 + (566813899/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183021273/10000000000 : ℝ)^4907 ≤ (2077551825369/6250000000000 : ℝ)^3883 := by
    have hnat : (4183021273 : ℕ)^4907*6250000000000^3883 ≤ 2077551825369^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183021273 10000000000 2077551825369 6250000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192591083/500000000 : ℝ)^4907 ≤ (748756670261/2500000000000 : ℝ)^3883 := by
    have hnat : (192591083 : ℕ)^4907*2500000000000^3883 ≤ 748756670261^3883*500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192591083 500000000 748756670261 2500000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566813899/1250000000 : ℝ)^4907 ≤ (36808903969801/100000000000000 : ℝ)^3883 := by
    have hnat : (566813899 : ℕ)^4907*100000000000000^3883 ≤ 36808903969801^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566813899 1250000000 36808903969801 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183021273/10000000000 : ℝ), (192591083/500000000 : ℝ), (566813899/1250000000 : ℝ)] ![(2077551825369/6250000000000 : ℝ), (748756670261/2500000000000 : ℝ), (36808903969801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183021273/10000000000 : ℝ)|^4907 ≤ (2077551825369/6250000000000 : ℝ)^3883
        have hw : |(4183021273/10000000000 : ℝ)|=(4183021273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192591083/500000000 : ℝ)|^4907 ≤ (748756670261/2500000000000 : ℝ)^3883
        have hw : |(192591083/500000000 : ℝ)|=(192591083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566813899/1250000000 : ℝ)|^4907 ≤ (36808903969801/100000000000000 : ℝ)^3883
        have hw : |(566813899/1250000000 : ℝ)|=(566813899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s3_4 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-807713917/5000000000 : ℝ)*x 0 + (51856401/100000000 : ℝ)*x 1 + (1089296163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807713917/5000000000 : ℝ)^4907 ≤ (2497136106999/25000000000000 : ℝ)^3883 := by
    have hnat : (807713917 : ℕ)^4907*25000000000000^3883 ≤ 2497136106999^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807713917 5000000000 2497136106999 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51856401/100000000 : ℝ)^4907 ≤ (109026452399/250000000000 : ℝ)^3883 := by
    have hnat : (51856401 : ℕ)^4907*250000000000^3883 ≤ 109026452399^3883*100000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51856401 100000000 109026452399 250000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089296163/2000000000 : ℝ)^4907 ≤ (23200437303221/50000000000000 : ℝ)^3883 := by
    have hnat : (1089296163 : ℕ)^4907*50000000000000^3883 ≤ 23200437303221^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089296163 2000000000 23200437303221 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-807713917/5000000000 : ℝ), (51856401/100000000 : ℝ), (1089296163/2000000000 : ℝ)] ![(2497136106999/25000000000000 : ℝ), (109026452399/250000000000 : ℝ), (23200437303221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-807713917/5000000000 : ℝ)|^4907 ≤ (2497136106999/25000000000000 : ℝ)^3883
        have hw : |(-807713917/5000000000 : ℝ)|=(807713917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51856401/100000000 : ℝ)|^4907 ≤ (109026452399/250000000000 : ℝ)^3883
        have hw : |(51856401/100000000 : ℝ)|=(51856401/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089296163/2000000000 : ℝ)|^4907 ≤ (23200437303221/50000000000000 : ℝ)^3883
        have hw : |(1089296163/2000000000 : ℝ)|=(1089296163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s3_5 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42219857/80000000 : ℝ)*x 0 + (-744444577/5000000000 : ℝ)*x 1 + (1361620159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42219857/80000000 : ℝ)^4907 ≤ (22294458752463/50000000000000 : ℝ)^3883 := by
    have hnat : (42219857 : ℕ)^4907*50000000000000^3883 ≤ 22294458752463^3883*80000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42219857 80000000 22294458752463 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744444577/5000000000 : ℝ)^4907 ≤ (281569056397/3125000000000 : ℝ)^3883 := by
    have hnat : (744444577 : ℕ)^4907*3125000000000^3883 ≤ 281569056397^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744444577 5000000000 281569056397 3125000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361620159/2500000000 : ℝ)^4907 ≤ (11600218169827/25000000000000 : ℝ)^3883 := by
    have hnat : (1361620159 : ℕ)^4907*25000000000000^3883 ≤ 11600218169827^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361620159 2500000000 11600218169827 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42219857/80000000 : ℝ), (-744444577/5000000000 : ℝ), (1361620159/2500000000 : ℝ)] ![(22294458752463/50000000000000 : ℝ), (281569056397/3125000000000 : ℝ), (11600218169827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42219857/80000000 : ℝ)|^4907 ≤ (22294458752463/50000000000000 : ℝ)^3883
        have hw : |(42219857/80000000 : ℝ)|=(42219857/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-744444577/5000000000 : ℝ)|^4907 ≤ (281569056397/3125000000000 : ℝ)^3883
        have hw : |(-744444577/5000000000 : ℝ)|=(744444577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361620159/2500000000 : ℝ)|^4907 ≤ (11600218169827/25000000000000 : ℝ)^3883
        have hw : |(1361620159/2500000000 : ℝ)|=(1361620159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s3_6 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055496431/2000000000 : ℝ)*x 0 + (5446480429/10000000000 : ℝ)*x 1 + (-372222351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055496431/2000000000 : ℝ)^4907 ≤ (8917783565047/20000000000000 : ℝ)^3883 := by
    have hnat : (1055496431 : ℕ)^4907*20000000000000^3883 ≤ 8917783565047^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055496431 2000000000 8917783565047 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446480429/10000000000 : ℝ)^4907 ≤ (46400870450723/100000000000000 : ℝ)^3883 := by
    have hnat : (5446480429 : ℕ)^4907*100000000000000^3883 ≤ 46400870450723^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446480429 10000000000 46400870450723 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372222351/2500000000 : ℝ)^4907 ≤ (9010211716587/100000000000000 : ℝ)^3883 := by
    have hnat : (372222351 : ℕ)^4907*100000000000000^3883 ≤ 9010211716587^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372222351 2500000000 9010211716587 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055496431/2000000000 : ℝ), (5446480429/10000000000 : ℝ), (-372222351/2500000000 : ℝ)] ![(8917783565047/20000000000000 : ℝ), (46400870450723/100000000000000 : ℝ), (9010211716587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055496431/2000000000 : ℝ)|^4907 ≤ (8917783565047/20000000000000 : ℝ)^3883
        have hw : |(1055496431/2000000000 : ℝ)|=(1055496431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446480429/10000000000 : ℝ)|^4907 ≤ (46400870450723/100000000000000 : ℝ)^3883
        have hw : |(5446480429/10000000000 : ℝ)|=(5446480429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-372222351/2500000000 : ℝ)|^4907 ≤ (9010211716587/100000000000000 : ℝ)^3883
        have hw : |(-372222351/2500000000 : ℝ)|=(372222351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s3_7 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183188627/10000000000 : ℝ)*x 0 + (2264673849/5000000000 : ℝ)*x 1 + (771407883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183188627/10000000000 : ℝ)^4907 ≤ (3324250982321/10000000000000 : ℝ)^3883 := by
    have hnat : (4183188627 : ℕ)^4907*10000000000000^3883 ≤ 3324250982321^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183188627 10000000000 3324250982321 10000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264673849/5000000000 : ℝ)^4907 ≤ (36755943781453/100000000000000 : ℝ)^3883 := by
    have hnat : (2264673849 : ℕ)^4907*100000000000000^3883 ≤ 36755943781453^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264673849 5000000000 36755943781453 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771407883/2000000000 : ℝ)^4907 ≤ (3000154638509/10000000000000 : ℝ)^3883 := by
    have hnat : (771407883 : ℕ)^4907*10000000000000^3883 ≤ 3000154638509^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771407883 2000000000 3000154638509 10000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183188627/10000000000 : ℝ), (2264673849/5000000000 : ℝ), (771407883/2000000000 : ℝ)] ![(3324250982321/10000000000000 : ℝ), (36755943781453/100000000000000 : ℝ), (3000154638509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183188627/10000000000 : ℝ)|^4907 ≤ (3324250982321/10000000000000 : ℝ)^3883
        have hw : |(4183188627/10000000000 : ℝ)|=(4183188627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264673849/5000000000 : ℝ)|^4907 ≤ (36755943781453/100000000000000 : ℝ)^3883
        have hw : |(2264673849/5000000000 : ℝ)|=(2264673849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(771407883/2000000000 : ℝ)|^4907 ≤ (3000154638509/10000000000000 : ℝ)^3883
        have hw : |(771407883/2000000000 : ℝ)|=(771407883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1647_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (213/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16279/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10581/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10581/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10581/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10581/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10581/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10581/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10581/100000 : ℝ) ^ (4903/1024 : ℝ) ≤ (2134765024212139/100000000000000000000 : ℝ) := by
    have hpowers : (10581/100000 : ℝ)^4903 ≤ (2134765024212139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10581 : ℕ)^4903*100000000000000000000^1024 ≤ 2134765024212139^1024*100000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10581 100000 2134765024212139 100000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10581/100000 : ℝ)) (X := (2134765024212139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4089/25000 : ℝ) ^ (4903/1024 : ℝ) ≤ (8589905647636841/50000000000000000000 : ℝ) := by
    have hpowers : (4089/25000 : ℝ)^4903 ≤ (8589905647636841/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4089 : ℕ)^4903*50000000000000000000^1024 ≤ 8589905647636841^1024*25000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4089 25000 8589905647636841 50000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4089/25000 : ℝ)) (X := (8589905647636841/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002134765024212139/50000000000000000000 : ℝ) ≤ (5000044584182461/5000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (50002134765024212139/50000000000000000000 : ℝ)^1024 ≤ (5000044584182461/5000000000000000 : ℝ)^4903 := by
      have hnat : (50002134765024212139 : ℕ)^1024*5000000000000000^4903 ≤ 5000044584182461^4903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002134765024212139 50000000000000000000 5000044584182461 5000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000044584182461/5000000000000000 : ℝ)) (X := (50002134765024212139/50000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019314576319485821/100000000000000000000 : ℝ) ≤ (5000201678719233/5000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (100019314576319485821/100000000000000000000 : ℝ)^1024 ≤ (5000201678719233/5000000000000000 : ℝ)^4903 := by
      have hnat : (100019314576319485821 : ℕ)^1024*5000000000000000^4903 ≤ 5000201678719233^4903*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019314576319485821 100000000000000000000 5000201678719233 5000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000201678719233/5000000000000000 : ℝ)) (X := (100019314576319485821/100000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008589905647636841/25000000000000000000 : ℝ) ≤ (1000071754651201/1000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (25008589905647636841/25000000000000000000 : ℝ)^1024 ≤ (1000071754651201/1000000000000000 : ℝ)^4903 := by
      have hnat : (25008589905647636841 : ℕ)^1024*1000000000000000^4903 ≤ 1000071754651201^4903*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008589905647636841 25000000000000000000 1000071754651201 1000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000071754651201/1000000000000000 : ℝ)) (X := (25008589905647636841/25000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2134765024212139/100000000000000000000 : ℝ) ≤ ((9623977679688847737/9625000000000000000 : ℝ)+2*(39273634193/72187500000000 : ℝ)*(10581/100000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (9623977679688847737/9625000000000000000 : ℝ)+2*(39273634193/72187500000000 : ℝ)*(10581/100000 : ℝ)=(5000044584182461/5000000000000000 : ℝ) by norm_num, show 1+2*(2134765024212139/100000000000000000000 : ℝ)=(50002134765024212139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8589905647636841/50000000000000000000 : ℝ)+(2134765024212139/100000000000000000000 : ℝ) ≤ ((9623977679688847737/9625000000000000000 : ℝ)+(39273634193/72187500000000 : ℝ)*((4089/25000 : ℝ)+(10581/100000 : ℝ)))^(4903/1024 : ℝ) := by
    rw [show (9623977679688847737/9625000000000000000 : ℝ)+(39273634193/72187500000000 : ℝ)*((4089/25000 : ℝ)+(10581/100000 : ℝ))=(5000201678719233/5000000000000000 : ℝ) by norm_num, show 1+(8589905647636841/50000000000000000000 : ℝ)+(2134765024212139/100000000000000000000 : ℝ)=(100019314576319485821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8589905647636841/50000000000000000000 : ℝ) ≤ ((9623977679688847737/9625000000000000000 : ℝ)+2*(39273634193/72187500000000 : ℝ)*(4089/25000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (9623977679688847737/9625000000000000000 : ℝ)+2*(39273634193/72187500000000 : ℝ)*(4089/25000 : ℝ)=(1000071754651201/1000000000000000 : ℝ) by norm_num, show 1+2*(8589905647636841/50000000000000000000 : ℝ)=(25008589905647636841/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9623977679688847737/9625000000000000000 : ℝ)*(X 1 0+X 2 0)+(39273634193/72187500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (10581/100000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (9623977679688847737/9625000000000000000 : ℝ)) (alpha := (39273634193/72187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9623977679688847737/9625000000000000000 : ℝ)*(X 0 1+X 2 1)+(39273634193/72187500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (10581/100000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (9623977679688847737/9625000000000000000 : ℝ)) (alpha := (39273634193/72187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9623977679688847737/9625000000000000000 : ℝ)*(X 0 2+X 1 2)+(39273634193/72187500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (10581/100000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (9623977679688847737/9625000000000000000 : ℝ)) (alpha := (39273634193/72187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1615362899/10000000000 : ℝ)*X 0 0+(2724252381/5000000000 : ℝ)*X 0 1+(323977333/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348217089/10000000000 : ℝ)*X 1 0+(-218966589/1250000000 : ℝ)*X 1 1+(5183637297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534821707/1000000000 : ℝ)*X 2 0+(5183637271/10000000000 : ℝ)*X 2 1+(-437933193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183021273/10000000000 : ℝ)*X 0 0+(192591083/500000000 : ℝ)*X 0 1+(566813899/1250000000 : ℝ)*X 0 2+(4183021273/10000000000 : ℝ)*X 1 0+(192591083/500000000 : ℝ)*X 1 1+(566813899/1250000000 : ℝ)*X 1 2+(4183021273/10000000000 : ℝ)*X 2 0+(192591083/500000000 : ℝ)*X 2 1+(566813899/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-807713917/5000000000 : ℝ)*X 0 0+(51856401/100000000 : ℝ)*X 0 1+(1089296163/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42219857/80000000 : ℝ)*X 1 0+(-744444577/5000000000 : ℝ)*X 1 1+(1361620159/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055496431/2000000000 : ℝ)*X 2 0+(5446480429/10000000000 : ℝ)*X 2 1+(-372222351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4183188627/10000000000 : ℝ)*X 0 0+(2264673849/5000000000 : ℝ)*X 0 1+(771407883/2000000000 : ℝ)*X 0 2+(4183188627/10000000000 : ℝ)*X 1 0+(2264673849/5000000000 : ℝ)*X 1 1+(771407883/2000000000 : ℝ)*X 1 2+(4183188627/10000000000 : ℝ)*X 2 0+(2264673849/5000000000 : ℝ)*X 2 1+(771407883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1590228061846797530328481353/240625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1032718033/100000000000000 : ℝ)*(base19) + (476201657/50000000000000 : ℝ)*(base23) + (8945153/25000000000000 : ℝ)*(lower2) + (182934063/100000000000000 : ℝ)*(upper3) + (85575251/100000000000000 : ℝ)*(upper5) + (2620151710887477/100000000000000 : ℝ)*(major0) + (2620151710887477/100000000000000 : ℝ)*(major1) + (2620151710887477/100000000000000 : ℝ)*(major2) + (1887743385423099/50000000000000 : ℝ)*(sp0) + (1887748628315679/50000000000000 : ℝ)*(sp1) + (3775497336946077/100000000000000 : ℝ)*(sp2) + (91549957086027/6250000000000 : ℝ)*(sp3) + (11518503193/100000000000000 : ℝ)*(sp4) + (5598757791/100000000000000 : ℝ)*(sp7) + (91550307008389/6250000000000 : ℝ)*(f.failure) + (3775498289349391/100000000000000 : ℝ)*(f.sum) + (61152514177871/9625000000000000000000000000 : ℝ)*base65 + (957267419792889549/962500000000000000000000000000000 : ℝ)*base67 + (3102858912067889549/962500000000000000000000000000000 : ℝ)*base69 + (6221241745919610451/962500000000000000000000000000000 : ℝ)*base72 + (11202333226373/4812500000000000000000000000 : ℝ)*base73 + (7320401003330389549/962500000000000000000000000000000 : ℝ)*base75 + (9898652883380389549/962500000000000000000000000000000 : ℝ)*base77 + (2994878292205389549/962500000000000000000000000000000 : ℝ)*base79 + (26662050131371/9625000000000000000000000000 : ℝ)*base81 + (1386487/312500000000000000000 : ℝ)*base89 + (1386487/312500000000000000000 : ℝ)*base91 + (1386487/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (329613335641625513849848297/43750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1517070127/100000000000000 : ℝ)*(base19) + (376049533/25000000000000 : ℝ)*(base23) + (10207551/25000000000000 : ℝ)*(upper3) + (7722473/20000000000000 : ℝ)*(lower4) + (322802473/100000000000000 : ℝ)*(upper5) + (2660586958788103/100000000000000 : ℝ)*(major0) + (2660586958788103/100000000000000 : ℝ)*(major1) + (2660586958788103/100000000000000 : ℝ)*(major2) + (1105879753/5000000000000 : ℝ)*(sp1) + (14072527943/100000000000000 : ℝ)*(sp2) + (958440822140653/25000000000000 : ℝ)*(sp4) + (239608728368589/6250000000000 : ℝ)*(sp5) + (479218463979567/12500000000000 : ℝ)*(sp6) + (743705188939809/50000000000000 : ℝ)*(sp7) + (743705188939809/50000000000000 : ℝ)*(f.failure) + (958440822140653/25000000000000 : ℝ)*(f.sum) + (1305699622391/14437500000000000000000000000 : ℝ)*base65 + (3169297835843818733/2887500000000000000000000000000000 : ℝ)*base67 + (14468047907481181267/2887500000000000000000000000000000 : ℝ)*base70 + (28535204954318818733/2887500000000000000000000000000000 : ℝ)*base71 + (7875098955883/7218750000000000000000000000 : ℝ)*base73 + (15790221372218818733/2887500000000000000000000000000000 : ℝ)*base75 + (15240936226193818733/2887500000000000000000000000000000 : ℝ)*base77 + (12270096221743681267/2887500000000000000000000000000000 : ℝ)*base80 + (15523644428359/14437500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16575347/2500000000000000000000 : ℝ)*base89 + (16575347/2500000000000000000000 : ℝ)*base91 + (16575347/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1647_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1647_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1647_s4_0 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-403852993/2500000000 : ℝ)*x 0 + (5448257517/10000000000 : ℝ)*x 1 + (5183851757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403852993/2500000000 : ℝ)^4907 ≤ (998842048537/10000000000000 : ℝ)^3883 := by
    have hnat : (403852993 : ℕ)^4907*10000000000000^3883 ≤ 998842048537^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403852993 2500000000 998842048537 10000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448257517/10000000000 : ℝ)^4907 ≤ (9284000720041/20000000000000 : ℝ)^3883 := by
    have hnat : (5448257517 : ℕ)^4907*20000000000000^3883 ≤ 9284000720041^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448257517 10000000000 9284000720041 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183851757/10000000000 : ℝ)^4907 ≤ (10897893974999/25000000000000 : ℝ)^3883 := by
    have hnat : (5183851757 : ℕ)^4907*25000000000000^3883 ≤ 10897893974999^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183851757 10000000000 10897893974999 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403852993/2500000000 : ℝ), (5448257517/10000000000 : ℝ), (5183851757/10000000000 : ℝ)] ![(998842048537/10000000000000 : ℝ), (9284000720041/20000000000000 : ℝ), (10897893974999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403852993/2500000000 : ℝ)|^4907 ≤ (998842048537/10000000000000 : ℝ)^3883
        have hw : |(-403852993/2500000000 : ℝ)|=(403852993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448257517/10000000000 : ℝ)|^4907 ≤ (9284000720041/20000000000000 : ℝ)^3883
        have hw : |(5448257517/10000000000 : ℝ)|=(5448257517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183851757/10000000000 : ℝ)|^4907 ≤ (10897893974999/25000000000000 : ℝ)^3883
        have hw : |(5183851757/10000000000 : ℝ)|=(5183851757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s4_1 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069629999/2000000000 : ℝ)*x 0 + (-875768507/5000000000 : ℝ)*x 1 + (1295962987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069629999/2000000000 : ℝ)^4907 ≤ (1417023921019/3125000000000 : ℝ)^3883 := by
    have hnat : (1069629999 : ℕ)^4907*3125000000000^3883 ≤ 1417023921019^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069629999 2000000000 1417023921019 3125000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (875768507/5000000000 : ℝ)^4907 ≤ (11063656579949/100000000000000 : ℝ)^3883 := by
    have hnat : (875768507 : ℕ)^4907*100000000000000^3883 ≤ 11063656579949^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875768507 5000000000 11063656579949 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295962987/2500000000 : ℝ)^4907 ≤ (43591577929697/100000000000000 : ℝ)^3883 := by
    have hnat : (1295962987 : ℕ)^4907*100000000000000^3883 ≤ 43591577929697^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295962987 2500000000 43591577929697 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069629999/2000000000 : ℝ), (-875768507/5000000000 : ℝ), (1295962987/2500000000 : ℝ)] ![(1417023921019/3125000000000 : ℝ), (11063656579949/100000000000000 : ℝ), (43591577929697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069629999/2000000000 : ℝ)|^4907 ≤ (1417023921019/3125000000000 : ℝ)^3883
        have hw : |(1069629999/2000000000 : ℝ)|=(1069629999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-875768507/5000000000 : ℝ)|^4907 ≤ (11063656579949/100000000000000 : ℝ)^3883
        have hw : |(-875768507/5000000000 : ℝ)|=(875768507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295962987/2500000000 : ℝ)|^4907 ≤ (43591577929697/100000000000000 : ℝ)^3883
        have hw : |(1295962987/2500000000 : ℝ)|=(1295962987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s4_2 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348149863/10000000000 : ℝ)*x 0 + (161995373/312500000 : ℝ)*x 1 + (-218942151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348149863/10000000000 : ℝ)^4907 ≤ (45344764058293/100000000000000 : ℝ)^3883 := by
    have hnat : (5348149863 : ℕ)^4907*100000000000000^3883 ≤ 45344764058293^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348149863 10000000000 45344764058293 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161995373/312500000 : ℝ)^4907 ≤ (681118403159/1562500000000 : ℝ)^3883 := by
    have hnat : (161995373 : ℕ)^4907*1562500000000^3883 ≤ 681118403159^3883*312500000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161995373 312500000 681118403159 1562500000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218942151/1250000000 : ℝ)^4907 ≤ (2212731625703/20000000000000 : ℝ)^3883 := by
    have hnat : (218942151 : ℕ)^4907*20000000000000^3883 ≤ 2212731625703^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218942151 1250000000 2212731625703 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348149863/10000000000 : ℝ), (161995373/312500000 : ℝ), (-218942151/1250000000 : ℝ)] ![(45344764058293/100000000000000 : ℝ), (681118403159/1562500000000 : ℝ), (2212731625703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348149863/10000000000 : ℝ)|^4907 ≤ (45344764058293/100000000000000 : ℝ)^3883
        have hw : |(5348149863/10000000000 : ℝ)|=(5348149863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161995373/312500000 : ℝ)|^4907 ≤ (681118403159/1562500000000 : ℝ)^3883
        have hw : |(161995373/312500000 : ℝ)|=(161995373/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218942151/1250000000 : ℝ)|^4907 ≤ (2212731625703/20000000000000 : ℝ)^3883
        have hw : |(-218942151/1250000000 : ℝ)|=(218942151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s4_3 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183053117/10000000000 : ℝ)*x 0 + (1926206663/5000000000 : ℝ)*x 1 + (18135653/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183053117/10000000000 : ℝ)^4907 ≤ (33241148991203/100000000000000 : ℝ)^3883 := by
    have hnat : (4183053117 : ℕ)^4907*100000000000000^3883 ≤ 33241148991203^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183053117 10000000000 33241148991203 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926206663/5000000000 : ℝ)^4907 ≤ (29956080724411/100000000000000 : ℝ)^3883 := by
    have hnat : (1926206663 : ℕ)^4907*100000000000000^3883 ≤ 29956080724411^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926206663 5000000000 29956080724411 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18135653/40000000 : ℝ)^4907 ≤ (287521642727/781250000000 : ℝ)^3883 := by
    have hnat : (18135653 : ℕ)^4907*781250000000^3883 ≤ 287521642727^3883*40000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18135653 40000000 287521642727 781250000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183053117/10000000000 : ℝ), (1926206663/5000000000 : ℝ), (18135653/40000000 : ℝ)] ![(33241148991203/100000000000000 : ℝ), (29956080724411/100000000000000 : ℝ), (287521642727/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183053117/10000000000 : ℝ)|^4907 ≤ (33241148991203/100000000000000 : ℝ)^3883
        have hw : |(4183053117/10000000000 : ℝ)|=(4183053117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1926206663/5000000000 : ℝ)|^4907 ≤ (29956080724411/100000000000000 : ℝ)^3883
        have hw : |(1926206663/5000000000 : ℝ)|=(1926206663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18135653/40000000 : ℝ)|^4907 ≤ (287521642727/781250000000 : ℝ)^3883
        have hw : |(18135653/40000000 : ℝ)|=(18135653/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s4_4 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-201934549/1250000000 : ℝ)*x 0 + (40514437/78125000 : ℝ)*x 1 + (2723120203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201934549/1250000000 : ℝ)^4907 ≤ (2497230963223/25000000000000 : ℝ)^3883 := by
    have hnat : (201934549 : ℕ)^4907*25000000000000^3883 ≤ 2497230963223^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201934549 1250000000 2497230963223 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40514437/78125000 : ℝ)^4907 ≤ (43612789784239/100000000000000 : ℝ)^3883 := by
    have hnat : (40514437 : ℕ)^4907*100000000000000^3883 ≤ 43612789784239^3883*78125000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40514437 78125000 43612789784239 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723120203/5000000000 : ℝ)^4907 ≤ (46398286351511/100000000000000 : ℝ)^3883 := by
    have hnat : (2723120203 : ℕ)^4907*100000000000000^3883 ≤ 46398286351511^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723120203 5000000000 46398286351511 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201934549/1250000000 : ℝ), (40514437/78125000 : ℝ), (2723120203/5000000000 : ℝ)] ![(2497230963223/25000000000000 : ℝ), (43612789784239/100000000000000 : ℝ), (46398286351511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201934549/1250000000 : ℝ)|^4907 ≤ (2497230963223/25000000000000 : ℝ)^3883
        have hw : |(-201934549/1250000000 : ℝ)|=(201934549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40514437/78125000 : ℝ)|^4907 ≤ (43612789784239/100000000000000 : ℝ)^3883
        have hw : |(40514437/78125000 : ℝ)|=(40514437/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723120203/5000000000 : ℝ)|^4907 ≤ (46398286351511/100000000000000 : ℝ)^3883
        have hw : |(2723120203/5000000000 : ℝ)|=(2723120203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s4_5 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319384647/2500000000 : ℝ)*x 0 + (-372287127/2500000000 : ℝ)*x 1 + (2723120203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319384647/2500000000 : ℝ)^4907 ≤ (5573690045081/12500000000000 : ℝ)^3883 := by
    have hnat : (1319384647 : ℕ)^4907*12500000000000^3883 ≤ 5573690045081^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319384647 2500000000 5573690045081 12500000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (372287127/2500000000 : ℝ)^4907 ≤ (360487730713/4000000000000 : ℝ)^3883 := by
    have hnat : (372287127 : ℕ)^4907*4000000000000^3883 ≤ 360487730713^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372287127 2500000000 360487730713 4000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723120203/5000000000 : ℝ)^4907 ≤ (46398286351511/100000000000000 : ℝ)^3883 := by
    have hnat : (2723120203 : ℕ)^4907*100000000000000^3883 ≤ 46398286351511^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723120203 5000000000 46398286351511 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319384647/2500000000 : ℝ), (-372287127/2500000000 : ℝ), (2723120203/5000000000 : ℝ)] ![(5573690045081/12500000000000 : ℝ), (360487730713/4000000000000 : ℝ), (46398286351511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319384647/2500000000 : ℝ)|^4907 ≤ (5573690045081/12500000000000 : ℝ)^3883
        have hw : |(1319384647/2500000000 : ℝ)|=(1319384647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-372287127/2500000000 : ℝ)|^4907 ≤ (360487730713/4000000000000 : ℝ)^3883
        have hw : |(-372287127/2500000000 : ℝ)|=(372287127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723120203/5000000000 : ℝ)|^4907 ≤ (46398286351511/100000000000000 : ℝ)^3883
        have hw : |(2723120203/5000000000 : ℝ)|=(2723120203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s4_6 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319384647/2500000000 : ℝ)*x 0 + (2723120203/5000000000 : ℝ)*x 1 + (-372287127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319384647/2500000000 : ℝ)^4907 ≤ (5573690045081/12500000000000 : ℝ)^3883 := by
    have hnat : (1319384647 : ℕ)^4907*12500000000000^3883 ≤ 5573690045081^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319384647 2500000000 5573690045081 12500000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723120203/5000000000 : ℝ)^4907 ≤ (46398286351511/100000000000000 : ℝ)^3883 := by
    have hnat : (2723120203 : ℕ)^4907*100000000000000^3883 ≤ 46398286351511^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723120203 5000000000 46398286351511 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372287127/2500000000 : ℝ)^4907 ≤ (360487730713/4000000000000 : ℝ)^3883 := by
    have hnat : (372287127 : ℕ)^4907*4000000000000^3883 ≤ 360487730713^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372287127 2500000000 360487730713 4000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319384647/2500000000 : ℝ), (2723120203/5000000000 : ℝ), (-372287127/2500000000 : ℝ)] ![(5573690045081/12500000000000 : ℝ), (46398286351511/100000000000000 : ℝ), (360487730713/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319384647/2500000000 : ℝ)|^4907 ≤ (5573690045081/12500000000000 : ℝ)^3883
        have hw : |(1319384647/2500000000 : ℝ)|=(1319384647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723120203/5000000000 : ℝ)|^4907 ≤ (46398286351511/100000000000000 : ℝ)^3883
        have hw : |(2723120203/5000000000 : ℝ)|=(2723120203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-372287127/2500000000 : ℝ)|^4907 ≤ (360487730713/4000000000000 : ℝ)^3883
        have hw : |(-372287127/2500000000 : ℝ)|=(372287127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s4_7 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2091609831/5000000000 : ℝ)*x 0 + (283047989/625000000 : ℝ)*x 1 + (3857612659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091609831/5000000000 : ℝ)^4907 ≤ (33242821487611/100000000000000 : ℝ)^3883 := by
    have hnat : (2091609831 : ℕ)^4907*100000000000000^3883 ≤ 33242821487611^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091609831 5000000000 33242821487611 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283047989/625000000 : ℝ)^4907 ≤ (18374998603299/50000000000000 : ℝ)^3883 := by
    have hnat : (283047989 : ℕ)^4907*50000000000000^3883 ≤ 18374998603299^3883*625000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283047989 625000000 18374998603299 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3857612659/10000000000 : ℝ)^4907 ≤ (6001436257137/20000000000000 : ℝ)^3883 := by
    have hnat : (3857612659 : ℕ)^4907*20000000000000^3883 ≤ 6001436257137^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3857612659 10000000000 6001436257137 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091609831/5000000000 : ℝ), (283047989/625000000 : ℝ), (3857612659/10000000000 : ℝ)] ![(33242821487611/100000000000000 : ℝ), (18374998603299/50000000000000 : ℝ), (6001436257137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091609831/5000000000 : ℝ)|^4907 ≤ (33242821487611/100000000000000 : ℝ)^3883
        have hw : |(2091609831/5000000000 : ℝ)|=(2091609831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283047989/625000000 : ℝ)|^4907 ≤ (18374998603299/50000000000000 : ℝ)^3883
        have hw : |(283047989/625000000 : ℝ)|=(283047989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3857612659/10000000000 : ℝ)|^4907 ≤ (6001436257137/20000000000000 : ℝ)^3883
        have hw : |(3857612659/10000000000 : ℝ)|=(3857612659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1647_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (2131/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8137/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (213/2000 : ℝ) ^ (4903/1024 : ℝ) ≤ (2202248561010837/100000000000000000000 : ℝ) := by
    have hpowers : (213/2000 : ℝ)^4903 ≤ (2202248561010837/100000000000000000000 : ℝ)^1024 := by
      have hnat : (213 : ℕ)^4903*100000000000000000000^1024 ≤ 2202248561010837^1024*2000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        213 2000 2202248561010837 100000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (213/2000 : ℝ)) (X := (2202248561010837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16279/100000 : ℝ) ^ (4903/1024 : ℝ) ≤ (8397998488280867/50000000000000000000 : ℝ) := by
    have hpowers : (16279/100000 : ℝ)^4903 ≤ (8397998488280867/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16279 : ℕ)^4903*50000000000000000000^1024 ≤ 8397998488280867^1024*100000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16279 100000 8397998488280867 50000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16279/100000 : ℝ)) (X := (8397998488280867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002202248561010837/50000000000000000000 : ℝ) ≤ (10000091987078799/10000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (50002202248561010837/50000000000000000000 : ℝ)^1024 ≤ (10000091987078799/10000000000000000 : ℝ)^4903 := by
      have hnat : (50002202248561010837 : ℕ)^1024*10000000000000000^4903 ≤ 10000091987078799^4903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002202248561010837 50000000000000000000 10000091987078799 10000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000091987078799/10000000000000000 : ℝ)) (X := (50002202248561010837/50000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018998245537572571/100000000000000000000 : ℝ) ≤ (10000396751816667/10000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (100018998245537572571/100000000000000000000 : ℝ)^1024 ≤ (10000396751816667/10000000000000000 : ℝ)^4903 := by
      have hnat : (100018998245537572571 : ℕ)^1024*10000000000000000^4903 ≤ 10000396751816667^4903*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018998245537572571 100000000000000000000 10000396751816667 10000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000396751816667/10000000000000000 : ℝ)) (X := (100018998245537572571/100000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008397998488280867/25000000000000000000 : ℝ) ≤ (2000140303310907/2000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (25008397998488280867/25000000000000000000 : ℝ)^1024 ≤ (2000140303310907/2000000000000000 : ℝ)^4903 := by
      have hnat : (25008397998488280867 : ℕ)^1024*2000000000000000^4903 ≤ 2000140303310907^4903*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008397998488280867 25000000000000000000 2000140303310907 2000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000140303310907/2000000000000000 : ℝ)) (X := (25008397998488280867/25000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2202248561010837/100000000000000000000 : ℝ) ≤ ((56284026306349971171/56290000000000000000 : ℝ)+2*(76191184467/140725000000000 : ℝ)*(213/2000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (56284026306349971171/56290000000000000000 : ℝ)+2*(76191184467/140725000000000 : ℝ)*(213/2000 : ℝ)=(10000091987078799/10000000000000000 : ℝ) by norm_num, show 1+2*(2202248561010837/100000000000000000000 : ℝ)=(50002202248561010837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8397998488280867/50000000000000000000 : ℝ)+(2202248561010837/100000000000000000000 : ℝ) ≤ ((56284026306349971171/56290000000000000000 : ℝ)+(76191184467/140725000000000 : ℝ)*((16279/100000 : ℝ)+(213/2000 : ℝ)))^(4903/1024 : ℝ) := by
    rw [show (56284026306349971171/56290000000000000000 : ℝ)+(76191184467/140725000000000 : ℝ)*((16279/100000 : ℝ)+(213/2000 : ℝ))=(10000396751816667/10000000000000000 : ℝ) by norm_num, show 1+(8397998488280867/50000000000000000000 : ℝ)+(2202248561010837/100000000000000000000 : ℝ)=(100018998245537572571/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8397998488280867/50000000000000000000 : ℝ) ≤ ((56284026306349971171/56290000000000000000 : ℝ)+2*(76191184467/140725000000000 : ℝ)*(16279/100000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (56284026306349971171/56290000000000000000 : ℝ)+2*(76191184467/140725000000000 : ℝ)*(16279/100000 : ℝ)=(2000140303310907/2000000000000000 : ℝ) by norm_num, show 1+2*(8397998488280867/50000000000000000000 : ℝ)=(25008397998488280867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56284026306349971171/56290000000000000000 : ℝ)*(X 1 0+X 2 0)+(76191184467/140725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (56284026306349971171/56290000000000000000 : ℝ)) (alpha := (76191184467/140725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56284026306349971171/56290000000000000000 : ℝ)*(X 0 1+X 2 1)+(76191184467/140725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (56284026306349971171/56290000000000000000 : ℝ)) (alpha := (76191184467/140725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56284026306349971171/56290000000000000000 : ℝ)*(X 0 2+X 1 2)+(76191184467/140725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (56284026306349971171/56290000000000000000 : ℝ)) (alpha := (76191184467/140725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-403852993/2500000000 : ℝ)*X 0 0+(5448257517/10000000000 : ℝ)*X 0 1+(5183851757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069629999/2000000000 : ℝ)*X 1 0+(-875768507/5000000000 : ℝ)*X 1 1+(1295962987/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348149863/10000000000 : ℝ)*X 2 0+(161995373/312500000 : ℝ)*X 2 1+(-218942151/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183053117/10000000000 : ℝ)*X 0 0+(1926206663/5000000000 : ℝ)*X 0 1+(18135653/40000000 : ℝ)*X 0 2+(4183053117/10000000000 : ℝ)*X 1 0+(1926206663/5000000000 : ℝ)*X 1 1+(18135653/40000000 : ℝ)*X 1 2+(4183053117/10000000000 : ℝ)*X 2 0+(1926206663/5000000000 : ℝ)*X 2 1+(18135653/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-201934549/1250000000 : ℝ)*X 0 0+(40514437/78125000 : ℝ)*X 0 1+(2723120203/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319384647/2500000000 : ℝ)*X 1 0+(-372287127/2500000000 : ℝ)*X 1 1+(2723120203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319384647/2500000000 : ℝ)*X 2 0+(2723120203/5000000000 : ℝ)*X 2 1+(-372287127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2091609831/5000000000 : ℝ)*X 0 0+(283047989/625000000 : ℝ)*X 0 1+(3857612659/10000000000 : ℝ)*X 0 2+(2091609831/5000000000 : ℝ)*X 1 0+(283047989/625000000 : ℝ)*X 1 1+(3857612659/10000000000 : ℝ)*X 1 2+(2091609831/5000000000 : ℝ)*X 2 0+(283047989/625000000 : ℝ)*X 2 1+(3857612659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (953058628257082662887396211/351812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286874579/100000000000000 : ℝ)*(base19) + (263434863/100000000000000 : ℝ)*(base23) + (48250829/100000000000000 : ℝ)*(upper2) + (118717589/100000000000000 : ℝ)*(upper3) + (10863331/100000000000000 : ℝ)*(upper4) + (328089619543249/12500000000000 : ℝ)*(major0) + (328089619543249/12500000000000 : ℝ)*(major1) + (328089619543249/12500000000000 : ℝ)*(major2) + (1891036599879749/50000000000000 : ℝ)*(sp0) + (236379775441091/6250000000000 : ℝ)*(sp1) + (945519107624293/25000000000000 : ℝ)*(sp2) + (1467354035340503/100000000000000 : ℝ)*(sp3) + (3494172537/100000000000000 : ℝ)*(sp4) + (3093119571/100000000000000 : ℝ)*(sp7) + (733678564230037/50000000000000 : ℝ)*(f.failure) + (1891038346966017/50000000000000 : ℝ)*(f.sum) + (341217047008571/28145000000000000000000000000 : ℝ)*base65 + (9433288035201625421/703625000000000000000000000000000 : ℝ)*base68 + (14236496473169500421/703625000000000000000000000000000 : ℝ)*base70 + (2575624387901250421/703625000000000000000000000000000 : ℝ)*base72 + (19202442458423/14072500000000000000000000000 : ℝ)*base73 + (8610209848184500421/703625000000000000000000000000000 : ℝ)*base76 + (8333088522446750421/703625000000000000000000000000000 : ℝ)*base78 + (7966050411242375421/703625000000000000000000000000000 : ℝ)*base80 + (28616470487079/28145000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4254671/2500000000000000000000 : ℝ)*base89 + (4254671/2500000000000000000000 : ℝ)*base91 + (4254671/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14303551140472444518154121031/1407250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1501388341/100000000000000 : ℝ)*(base19) + (1623392531/100000000000000 : ℝ)*(base23) + (470579071/100000000000000 : ℝ)*(lower1) + (106558543/50000000000000 : ℝ)*(upper3) + (54967229/100000000000000 : ℝ)*(lower4) + (26319569/12500000000000 : ℝ)*(upper5) + (2665149700754113/100000000000000 : ℝ)*(major0) + (2665149700754113/100000000000000 : ℝ)*(major1) + (2665149700754113/100000000000000 : ℝ)*(major2) + (266839749/20000000000000 : ℝ)*(sp2) + (960084467020679/25000000000000 : ℝ)*(sp4) + (480042045836797/12500000000000 : ℝ)*(sp5) + (48004186381143/1250000000000 : ℝ)*(sp6) + (148996119461929/10000000000000 : ℝ)*(sp7) + (148996119461929/10000000000000 : ℝ)*(f.failure) + (960084467020679/25000000000000 : ℝ)*(f.sum) + (396026269317/219882812500000000000000000 : ℝ)*base66 + (103916863643074076323/5629000000000000000000000000000000 : ℝ)*base67 + (2172600436644076323/5629000000000000000000000000000000 : ℝ)*base69 + (342248157172153923677/5629000000000000000000000000000000 : ℝ)*base72 + (8167865943011/7036250000000000000000000000 : ℝ)*base73 + (15711842975804076323/5629000000000000000000000000000000 : ℝ)*base75 + (3442087253203076323/5629000000000000000000000000000000 : ℝ)*base77 + (2165535399938076323/5629000000000000000000000000000000 : ℝ)*base79 + (97131999100133/14072500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1927307/500000000000000000000 : ℝ)*base89 + (1927307/500000000000000000000 : ℝ)*base91 + (1927307/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1647_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1647_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1647_s5_0 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1615414483/10000000000 : ℝ)*x 0 + (2724120623/5000000000 : ℝ)*x 1 + (5183866397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1615414483/10000000000 : ℝ)^4907 ≤ (9988440105821/100000000000000 : ℝ)^3883 := by
    have hnat : (1615414483 : ℕ)^4907*100000000000000^3883 ≤ 9988440105821^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615414483 10000000000 9988440105821 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724120623/5000000000 : ℝ)^4907 ≤ (46419828409813/100000000000000 : ℝ)^3883 := by
    have hnat : (2724120623 : ℕ)^4907*100000000000000^3883 ≤ 46419828409813^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724120623 5000000000 46419828409813 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183866397/10000000000 : ℝ)^4907 ≤ (43591731475029/100000000000000 : ℝ)^3883 := by
    have hnat : (5183866397 : ℕ)^4907*100000000000000^3883 ≤ 43591731475029^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183866397 10000000000 43591731475029 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1615414483/10000000000 : ℝ), (2724120623/5000000000 : ℝ), (5183866397/10000000000 : ℝ)] ![(9988440105821/100000000000000 : ℝ), (46419828409813/100000000000000 : ℝ), (43591731475029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1615414483/10000000000 : ℝ)|^4907 ≤ (9988440105821/100000000000000 : ℝ)^3883
        have hw : |(-1615414483/10000000000 : ℝ)|=(1615414483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724120623/5000000000 : ℝ)|^4907 ≤ (46419828409813/100000000000000 : ℝ)^3883
        have hw : |(2724120623/5000000000 : ℝ)|=(2724120623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183866397/10000000000 : ℝ)|^4907 ≤ (43591731475029/100000000000000 : ℝ)^3883
        have hw : |(5183866397/10000000000 : ℝ)|=(5183866397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s5_1 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348145663/10000000000 : ℝ)*x 0 + (-175152351/1000000000 : ℝ)*x 1 + (5183866459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348145663/10000000000 : ℝ)^4907 ≤ (45344719057363/100000000000000 : ℝ)^3883 := by
    have hnat : (5348145663 : ℕ)^4907*100000000000000^3883 ≤ 45344719057363^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348145663 10000000000 45344719057363 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175152351/1000000000 : ℝ)^4907 ≤ (5531774393541/50000000000000 : ℝ)^3883 := by
    have hnat : (175152351 : ℕ)^4907*50000000000000^3883 ≤ 5531774393541^3883*1000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175152351 1000000000 5531774393541 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183866459/10000000000 : ℝ)^4907 ≤ (8718346426777/20000000000000 : ℝ)^3883 := by
    have hnat : (5183866459 : ℕ)^4907*20000000000000^3883 ≤ 8718346426777^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183866459 10000000000 8718346426777 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348145663/10000000000 : ℝ), (-175152351/1000000000 : ℝ), (5183866459/10000000000 : ℝ)] ![(45344719057363/100000000000000 : ℝ), (5531774393541/50000000000000 : ℝ), (8718346426777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348145663/10000000000 : ℝ)|^4907 ≤ (45344719057363/100000000000000 : ℝ)^3883
        have hw : |(5348145663/10000000000 : ℝ)|=(5348145663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-175152351/1000000000 : ℝ)|^4907 ≤ (5531774393541/50000000000000 : ℝ)^3883
        have hw : |(-175152351/1000000000 : ℝ)|=(175152351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183866459/10000000000 : ℝ)|^4907 ≤ (8718346426777/20000000000000 : ℝ)^3883
        have hw : |(5183866459/10000000000 : ℝ)|=(5183866459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s5_2 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1615479143/10000000000 : ℝ)*x 0 + (2592930891/5000000000 : ℝ)*x 1 + (272311237/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1615479143/10000000000 : ℝ)^4907 ≤ (4994472674441/50000000000000 : ℝ)^3883 := by
    have hnat : (1615479143 : ℕ)^4907*50000000000000^3883 ≤ 4994472674441^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615479143 10000000000 4994472674441 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592930891/5000000000 : ℝ)^4907 ≤ (43612936936601/100000000000000 : ℝ)^3883 := by
    have hnat : (2592930891 : ℕ)^4907*100000000000000^3883 ≤ 43612936936601^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592930891 5000000000 43612936936601 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272311237/500000000 : ℝ)^4907 ≤ (23199058845821/50000000000000 : ℝ)^3883 := by
    have hnat : (272311237 : ℕ)^4907*50000000000000^3883 ≤ 23199058845821^3883*500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272311237 500000000 23199058845821 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1615479143/10000000000 : ℝ), (2592930891/5000000000 : ℝ), (272311237/500000000 : ℝ)] ![(4994472674441/50000000000000 : ℝ), (43612936936601/100000000000000 : ℝ), (23199058845821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1615479143/10000000000 : ℝ)|^4907 ≤ (4994472674441/50000000000000 : ℝ)^3883
        have hw : |(-1615479143/10000000000 : ℝ)|=(1615479143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592930891/5000000000 : ℝ)|^4907 ≤ (43612936936601/100000000000000 : ℝ)^3883
        have hw : |(2592930891/5000000000 : ℝ)|=(2592930891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272311237/500000000 : ℝ)|^4907 ≤ (23199058845821/50000000000000 : ℝ)^3883
        have hw : |(272311237/500000000 : ℝ)|=(272311237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s5_3 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277542371/10000000000 : ℝ)*x 0 + (-1489165233/10000000000 : ℝ)*x 1 + (2723112387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277542371/10000000000 : ℝ)^4907 ≤ (22294780375909/50000000000000 : ℝ)^3883 := by
    have hnat : (5277542371 : ℕ)^4907*50000000000000^3883 ≤ 22294780375909^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277542371 10000000000 22294780375909 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1489165233/10000000000 : ℝ)^4907 ≤ (4506160589417/50000000000000 : ℝ)^3883 := by
    have hnat : (1489165233 : ℕ)^4907*50000000000000^3883 ≤ 4506160589417^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489165233 10000000000 4506160589417 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723112387/5000000000 : ℝ)^4907 ≤ (9279623611537/20000000000000 : ℝ)^3883 := by
    have hnat : (2723112387 : ℕ)^4907*20000000000000^3883 ≤ 9279623611537^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723112387 5000000000 9279623611537 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277542371/10000000000 : ℝ), (-1489165233/10000000000 : ℝ), (2723112387/5000000000 : ℝ)] ![(22294780375909/50000000000000 : ℝ), (4506160589417/50000000000000 : ℝ), (9279623611537/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277542371/10000000000 : ℝ)|^4907 ≤ (22294780375909/50000000000000 : ℝ)^3883
        have hw : |(5277542371/10000000000 : ℝ)|=(5277542371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1489165233/10000000000 : ℝ)|^4907 ≤ (4506160589417/50000000000000 : ℝ)^3883
        have hw : |(-1489165233/10000000000 : ℝ)|=(1489165233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723112387/5000000000 : ℝ)|^4907 ≤ (9279623611537/20000000000000 : ℝ)^3883
        have hw : |(2723112387/5000000000 : ℝ)|=(2723112387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s5_4 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277542281/10000000000 : ℝ)*x 0 + (5446224651/10000000000 : ℝ)*x 1 + (-1489165533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277542281/10000000000 : ℝ)^4907 ≤ (22294779895443/50000000000000 : ℝ)^3883 := by
    have hnat : (5277542281 : ℕ)^4907*50000000000000^3883 ≤ 22294779895443^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277542281 10000000000 22294779895443 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446224651/10000000000 : ℝ)^4907 ≤ (4639811673347/10000000000000 : ℝ)^3883 := by
    have hnat : (5446224651 : ℕ)^4907*10000000000000^3883 ≤ 4639811673347^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446224651 10000000000 4639811673347 10000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489165533/10000000000 : ℝ)^4907 ≤ (1802464694641/20000000000000 : ℝ)^3883 := by
    have hnat : (1489165533 : ℕ)^4907*20000000000000^3883 ≤ 1802464694641^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489165533 10000000000 1802464694641 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277542281/10000000000 : ℝ), (5446224651/10000000000 : ℝ), (-1489165533/10000000000 : ℝ)] ![(22294779895443/50000000000000 : ℝ), (4639811673347/10000000000000 : ℝ), (1802464694641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277542281/10000000000 : ℝ)|^4907 ≤ (22294779895443/50000000000000 : ℝ)^3883
        have hw : |(5277542281/10000000000 : ℝ)|=(5277542281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446224651/10000000000 : ℝ)|^4907 ≤ (4639811673347/10000000000000 : ℝ)^3883
        have hw : |(5446224651/10000000000 : ℝ)|=(5446224651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1489165533/10000000000 : ℝ)|^4907 ≤ (1802464694641/20000000000000 : ℝ)^3883
        have hw : |(-1489165533/10000000000 : ℝ)|=(1489165533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s5_5 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2091610813/5000000000 : ℝ)*x 0 + (4528728923/10000000000 : ℝ)*x 1 + (771530247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091610813/5000000000 : ℝ)^4907 ≤ (8310710302703/25000000000000 : ℝ)^3883 := by
    have hnat : (2091610813 : ℕ)^4907*25000000000000^3883 ≤ 8310710302703^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091610813 5000000000 8310710302703 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528728923/10000000000 : ℝ)^4907 ≤ (9187399571561/25000000000000 : ℝ)^3883 := by
    have hnat : (4528728923 : ℕ)^4907*25000000000000^3883 ≤ 9187399571561^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528728923 10000000000 9187399571561 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771530247/2000000000 : ℝ)^4907 ≤ (15003780244889/50000000000000 : ℝ)^3883 := by
    have hnat : (771530247 : ℕ)^4907*50000000000000^3883 ≤ 15003780244889^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771530247 2000000000 15003780244889 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091610813/5000000000 : ℝ), (4528728923/10000000000 : ℝ), (771530247/2000000000 : ℝ)] ![(8310710302703/25000000000000 : ℝ), (9187399571561/25000000000000 : ℝ), (15003780244889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091610813/5000000000 : ℝ)|^4907 ≤ (8310710302703/25000000000000 : ℝ)^3883
        have hw : |(2091610813/5000000000 : ℝ)|=(2091610813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528728923/10000000000 : ℝ)|^4907 ≤ (9187399571561/25000000000000 : ℝ)^3883
        have hw : |(4528728923/10000000000 : ℝ)|=(4528728923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(771530247/2000000000 : ℝ)|^4907 ≤ (15003780244889/50000000000000 : ℝ)^3883
        have hw : |(771530247/2000000000 : ℝ)|=(771530247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1647_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2131/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16273/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8137/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2131/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8137/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2131/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8137/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2131/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8137/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2131/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8137/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2131/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8137/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2131/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2131/20000 : ℝ) ^ (4903/1024 : ℝ) ≤ (220720346049863/10000000000000000000 : ℝ) := by
    have hpowers : (2131/20000 : ℝ)^4903 ≤ (220720346049863/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2131 : ℕ)^4903*10000000000000000000^1024 ≤ 220720346049863^1024*20000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2131 20000 220720346049863 10000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2131/20000 : ℝ)) (X := (220720346049863/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8137/50000 : ℝ) ^ (4903/1024 : ℝ) ≤ (16771310599629781/100000000000000000000 : ℝ) := by
    have hpowers : (8137/50000 : ℝ)^4903 ≤ (16771310599629781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8137 : ℕ)^4903*100000000000000000000^1024 ≤ 16771310599629781^1024*50000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8137 50000 16771310599629781 100000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8137/50000 : ℝ)) (X := (16771310599629781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000220720346049863/5000000000000000000 : ℝ) ≤ (5000046097019719/5000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (5000220720346049863/5000000000000000000 : ℝ)^1024 ≤ (5000046097019719/5000000000000000 : ℝ)^4903 := by
      have hnat : (5000220720346049863 : ℕ)^1024*5000000000000000^4903 ≤ 5000046097019719^4903*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000220720346049863 5000000000000000000 5000046097019719 5000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000046097019719/5000000000000000 : ℝ)) (X := (5000220720346049863/5000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018978514060128411/100000000000000000000 : ℝ) ≤ (10000396339783257/10000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (100018978514060128411/100000000000000000000 : ℝ)^1024 ≤ (10000396339783257/10000000000000000 : ℝ)^4903 := by
      have hnat : (100018978514060128411 : ℕ)^1024*10000000000000000^4903 ≤ 10000396339783257^4903*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018978514060128411 100000000000000000000 10000396339783257 10000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000396339783257/10000000000000000 : ℝ)) (X := (100018978514060128411/100000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016771310599629781/50000000000000000000 : ℝ) ≤ (2500175121381769/2500000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (50016771310599629781/50000000000000000000 : ℝ)^1024 ≤ (2500175121381769/2500000000000000 : ℝ)^4903 := by
      have hnat : (50016771310599629781 : ℕ)^1024*2500000000000000^4903 ≤ 2500175121381769^4903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016771310599629781 50000000000000000000 2500175121381769 2500000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500175121381769/2500000000000000 : ℝ)) (X := (50016771310599629781/50000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(220720346049863/10000000000000000000 : ℝ) ≤ ((1755751146640838101/1755937500000000000 : ℝ)+2*(304145743819/561900000000000 : ℝ)*(2131/20000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (1755751146640838101/1755937500000000000 : ℝ)+2*(304145743819/561900000000000 : ℝ)*(2131/20000 : ℝ)=(5000046097019719/5000000000000000 : ℝ) by norm_num, show 1+2*(220720346049863/10000000000000000000 : ℝ)=(5000220720346049863/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16771310599629781/100000000000000000000 : ℝ)+(220720346049863/10000000000000000000 : ℝ) ≤ ((1755751146640838101/1755937500000000000 : ℝ)+(304145743819/561900000000000 : ℝ)*((8137/50000 : ℝ)+(2131/20000 : ℝ)))^(4903/1024 : ℝ) := by
    rw [show (1755751146640838101/1755937500000000000 : ℝ)+(304145743819/561900000000000 : ℝ)*((8137/50000 : ℝ)+(2131/20000 : ℝ))=(10000396339783257/10000000000000000 : ℝ) by norm_num, show 1+(16771310599629781/100000000000000000000 : ℝ)+(220720346049863/10000000000000000000 : ℝ)=(100018978514060128411/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16771310599629781/100000000000000000000 : ℝ) ≤ ((1755751146640838101/1755937500000000000 : ℝ)+2*(304145743819/561900000000000 : ℝ)*(8137/50000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (1755751146640838101/1755937500000000000 : ℝ)+2*(304145743819/561900000000000 : ℝ)*(8137/50000 : ℝ)=(2500175121381769/2500000000000000 : ℝ) by norm_num, show 1+2*(16771310599629781/100000000000000000000 : ℝ)=(50016771310599629781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1755751146640838101/1755937500000000000 : ℝ)*(X 1 0+X 2 0)+(304145743819/561900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2131/20000 : ℝ)) (hi := (8137/50000 : ℝ)) (c := (1755751146640838101/1755937500000000000 : ℝ)) (alpha := (304145743819/561900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1755751146640838101/1755937500000000000 : ℝ)*(X 0 1+X 2 1)+(304145743819/561900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2131/20000 : ℝ)) (hi := (8137/50000 : ℝ)) (c := (1755751146640838101/1755937500000000000 : ℝ)) (alpha := (304145743819/561900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1755751146640838101/1755937500000000000 : ℝ)*(X 0 2+X 1 2)+(304145743819/561900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2131/20000 : ℝ)) (hi := (8137/50000 : ℝ)) (c := (1755751146640838101/1755937500000000000 : ℝ)) (alpha := (304145743819/561900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1615414483/10000000000 : ℝ)*X 0 0+(2724120623/5000000000 : ℝ)*X 0 1+(5183866397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348145663/10000000000 : ℝ)*X 1 0+(-175152351/1000000000 : ℝ)*X 1 1+(5183866459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1615479143/10000000000 : ℝ)*X 0 0+(2592930891/5000000000 : ℝ)*X 0 1+(272311237/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s5_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5277542371/10000000000 : ℝ)*X 1 0+(-1489165233/10000000000 : ℝ)*X 1 1+(2723112387/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s5_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5277542281/10000000000 : ℝ)*X 2 0+(5446224651/10000000000 : ℝ)*X 2 1+(-1489165533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s5_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2091610813/5000000000 : ℝ)*X 0 0+(4528728923/10000000000 : ℝ)*X 0 1+(771530247/2000000000 : ℝ)*X 0 2+(2091610813/5000000000 : ℝ)*X 1 0+(4528728923/10000000000 : ℝ)*X 1 1+(771530247/2000000000 : ℝ)*X 1 2+(2091610813/5000000000 : ℝ)*X 2 0+(4528728923/10000000000 : ℝ)*X 2 1+(771530247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1978178829050341352406927/585312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (262036413/100000000000000 : ℝ)*(base19) + (131877897/100000000000000 : ℝ)*(base23) + (2378421/25000000000000 : ℝ)*(upper2) + (17930223/100000000000000 : ℝ)*(upper3) + (115446949/100000000000000 : ℝ)*(upper5) + (53309369108159/2000000000000 : ℝ)*(major0) + (53309369108159/2000000000000 : ℝ)*(major1) + (53309369108159/2000000000000 : ℝ)*(major2) + (363651147/20000000000000 : ℝ)*(sp0) + (1545190569/25000000000000 : ℝ)*(sp1) + (3840795584388239/100000000000000 : ℝ)*(sp2) + (1920395479922643/50000000000000 : ℝ)*(sp3) + (3840797270766077/100000000000000 : ℝ)*(sp4) + (298027879103071/20000000000000 : ℝ)*(sp5) + (298027879103071/20000000000000 : ℝ)*(f.failure) + (1920398701321987/50000000000000 : ℝ)*(f.sum) + (49594383889751/2809500000000000000000000000 : ℝ)*base66 + (8629932307565897/1170625000000000000000000000000 : ℝ)*base68 + (2915387465986943/292656250000000000000000000000 : ℝ)*base70 + (314803794479071/36582031250000000000000000000 : ℝ)*base72 + (7928364886063/5619000000000000000000000000 : ℝ)*base74 + (10026592235253397/1170625000000000000000000000000 : ℝ)*base76 + (9763481850854647/1170625000000000000000000000000 : ℝ)*base78 + (556225063264443/292656250000000000000000000000 : ℝ)*base80 + (11632226978243/2809500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5967693/1000000000000000000000 : ℝ)*base89 + (5967693/1000000000000000000000 : ℝ)*base91 + (5967693/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1647_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1647_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1647_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1647_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1647_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1647_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1647_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
