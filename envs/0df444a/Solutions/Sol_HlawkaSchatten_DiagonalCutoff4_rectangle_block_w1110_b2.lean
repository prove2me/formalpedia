-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:56.603148+00:00
-- url     : https://prove2.me/submissions/98b7cb7d-59ae-4af3-8f12-5bcfad96b7bc

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
theorem support_rectangle_w1110_s6_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436449401/2000000000 : ℝ)*x 0 + (2697013691/5000000000 : ℝ)*x 1 + (5264811883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436449401/2000000000 : ℝ)^8303 ≤ (13257117390181/100000000000000 : ℝ)^6255 := by
    have hnat : (436449401 : ℕ)^8303*100000000000000^6255 ≤ 13257117390181^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436449401 2000000000 13257117390181 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697013691/5000000000 : ℝ)^8303 ≤ (2754334520413/6250000000000 : ℝ)^6255 := by
    have hnat : (2697013691 : ℕ)^8303*6250000000000^6255 ≤ 2754334520413^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697013691 5000000000 2754334520413 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264811883/10000000000 : ℝ)^8303 ≤ (8534706053421/20000000000000 : ℝ)^6255 := by
    have hnat : (5264811883 : ℕ)^8303*20000000000000^6255 ≤ 8534706053421^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264811883 10000000000 8534706053421 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436449401/2000000000 : ℝ), (2697013691/5000000000 : ℝ), (5264811883/10000000000 : ℝ)] ![(13257117390181/100000000000000 : ℝ), (2754334520413/6250000000000 : ℝ), (8534706053421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436449401/2000000000 : ℝ)|^8303 ≤ (13257117390181/100000000000000 : ℝ)^6255
        have hw : |(-436449401/2000000000 : ℝ)|=(436449401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697013691/5000000000 : ℝ)|^8303 ≤ (2754334520413/6250000000000 : ℝ)^6255
        have hw : |(2697013691/5000000000 : ℝ)|=(2697013691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264811883/10000000000 : ℝ)|^8303 ≤ (8534706053421/20000000000000 : ℝ)^6255
        have hw : |(5264811883/10000000000 : ℝ)|=(5264811883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s6_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534497169/1000000000 : ℝ)*x 0 + (-449560317/2000000000 : ℝ)*x 1 + (526481187/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534497169/1000000000 : ℝ)^8303 ≤ (170070839767/390625000000 : ℝ)^6255 := by
    have hnat : (534497169 : ℕ)^8303*390625000000^6255 ≤ 170070839767^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534497169 1000000000 170070839767 390625000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449560317/2000000000 : ℝ)^8303 ≤ (2757666976037/20000000000000 : ℝ)^6255 := by
    have hnat : (449560317 : ℕ)^8303*20000000000000^6255 ≤ 2757666976037^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449560317 2000000000 2757666976037 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526481187/1000000000 : ℝ)^8303 ≤ (21336765063617/50000000000000 : ℝ)^6255 := by
    have hnat : (526481187 : ℕ)^8303*50000000000000^6255 ≤ 21336765063617^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526481187 1000000000 21336765063617 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534497169/1000000000 : ℝ), (-449560317/2000000000 : ℝ), (526481187/1000000000 : ℝ)] ![(170070839767/390625000000 : ℝ), (2757666976037/20000000000000 : ℝ), (21336765063617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534497169/1000000000 : ℝ)|^8303 ≤ (170070839767/390625000000 : ℝ)^6255
        have hw : |(534497169/1000000000 : ℝ)|=(534497169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449560317/2000000000 : ℝ)|^8303 ≤ (2757666976037/20000000000000 : ℝ)^6255
        have hw : |(-449560317/2000000000 : ℝ)|=(449560317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526481187/1000000000 : ℝ)|^8303 ≤ (21336765063617/50000000000000 : ℝ)^6255
        have hw : |(526481187/1000000000 : ℝ)|=(526481187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s6_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336242927/2500000000 : ℝ)*x 0 + (1316202967/2500000000 : ℝ)*x 1 + (-2247801563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336242927/2500000000 : ℝ)^8303 ≤ (2176906758749/5000000000000 : ℝ)^6255 := by
    have hnat : (1336242927 : ℕ)^8303*5000000000000^6255 ≤ 2176906758749^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336242927 2500000000 2176906758749 5000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316202967/2500000000 : ℝ)^8303 ≤ (8534706021143/20000000000000 : ℝ)^6255 := by
    have hnat : (1316202967 : ℕ)^8303*20000000000000^6255 ≤ 8534706021143^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316202967 2500000000 8534706021143 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247801563/10000000000 : ℝ)^8303 ≤ (1723541837631/12500000000000 : ℝ)^6255 := by
    have hnat : (2247801563 : ℕ)^8303*12500000000000^6255 ≤ 1723541837631^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247801563 10000000000 1723541837631 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336242927/2500000000 : ℝ), (1316202967/2500000000 : ℝ), (-2247801563/10000000000 : ℝ)] ![(2176906758749/5000000000000 : ℝ), (8534706021143/20000000000000 : ℝ), (1723541837631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336242927/2500000000 : ℝ)|^8303 ≤ (2176906758749/5000000000000 : ℝ)^6255
        have hw : |(1336242927/2500000000 : ℝ)|=(1336242927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316202967/2500000000 : ℝ)|^8303 ≤ (8534706021143/20000000000000 : ℝ)^6255
        have hw : |(1316202967/2500000000 : ℝ)|=(1316202967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247801563/10000000000 : ℝ)|^8303 ≤ (1723541837631/12500000000000 : ℝ)^6255
        have hw : |(-2247801563/10000000000 : ℝ)|=(2247801563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s6_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174767199/400000000 : ℝ)*x 0 + (1060830647/2500000000 : ℝ)*x 1 + (899756201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174767199/400000000 : ℝ)^8303 ≤ (8329144284533/25000000000000 : ℝ)^6255 := by
    have hnat : (174767199 : ℕ)^8303*25000000000000^6255 ≤ 8329144284533^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174767199 400000000 8329144284533 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060830647/2500000000 : ℝ)^8303 ≤ (4006086265521/12500000000000 : ℝ)^6255 := by
    have hnat : (1060830647 : ℕ)^8303*12500000000000^6255 ≤ 4006086265521^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060830647 2500000000 4006086265521 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899756201/2000000000 : ℝ)^8303 ≤ (6926946544779/20000000000000 : ℝ)^6255 := by
    have hnat : (899756201 : ℕ)^8303*20000000000000^6255 ≤ 6926946544779^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899756201 2000000000 6926946544779 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174767199/400000000 : ℝ), (1060830647/2500000000 : ℝ), (899756201/2000000000 : ℝ)] ![(8329144284533/25000000000000 : ℝ), (4006086265521/12500000000000 : ℝ), (6926946544779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174767199/400000000 : ℝ)|^8303 ≤ (8329144284533/25000000000000 : ℝ)^6255
        have hw : |(174767199/400000000 : ℝ)|=(174767199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060830647/2500000000 : ℝ)|^8303 ≤ (4006086265521/12500000000000 : ℝ)^6255
        have hw : |(1060830647/2500000000 : ℝ)|=(1060830647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899756201/2000000000 : ℝ)|^8303 ≤ (6926946544779/20000000000000 : ℝ)^6255
        have hw : |(899756201/2000000000 : ℝ)|=(899756201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s6_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182252087/10000000000 : ℝ)*x 0 + (1316284539/2500000000 : ℝ)*x 1 + (5393699903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182252087/10000000000 : ℝ)^8303 ≤ (13257158371671/100000000000000 : ℝ)^6255 := by
    have hnat : (2182252087 : ℕ)^8303*100000000000000^6255 ≤ 13257158371671^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182252087 10000000000 13257158371671 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316284539/2500000000 : ℝ)^8303 ≤ (4267704076713/10000000000000 : ℝ)^6255 := by
    have hnat : (1316284539 : ℕ)^8303*10000000000000^6255 ≤ 4267704076713^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316284539 2500000000 4267704076713 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393699903/10000000000 : ℝ)^8303 ≤ (44065800838343/100000000000000 : ℝ)^6255 := by
    have hnat : (5393699903 : ℕ)^8303*100000000000000^6255 ≤ 44065800838343^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393699903 10000000000 44065800838343 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182252087/10000000000 : ℝ), (1316284539/2500000000 : ℝ), (5393699903/10000000000 : ℝ)] ![(13257158371671/100000000000000 : ℝ), (4267704076713/10000000000000 : ℝ), (44065800838343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182252087/10000000000 : ℝ)|^8303 ≤ (13257158371671/100000000000000 : ℝ)^6255
        have hw : |(-2182252087/10000000000 : ℝ)|=(2182252087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316284539/2500000000 : ℝ)|^8303 ≤ (4267704076713/10000000000000 : ℝ)^6255
        have hw : |(1316284539/2500000000 : ℝ)|=(1316284539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393699903/10000000000 : ℝ)|^8303 ≤ (44065800838343/100000000000000 : ℝ)^6255
        have hw : |(5393699903/10000000000 : ℝ)|=(5393699903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s6_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656156583/5000000000 : ℝ)*x 0 + (-105945677/500000000 : ℝ)*x 1 + (5393699867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656156583/5000000000 : ℝ)^8303 ≤ (43185363509299/100000000000000 : ℝ)^6255 := by
    have hnat : (2656156583 : ℕ)^8303*100000000000000^6255 ≤ 43185363509299^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656156583 5000000000 43185363509299 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105945677/500000000 : ℝ)^8303 ≤ (12748836032423/100000000000000 : ℝ)^6255 := by
    have hnat : (105945677 : ℕ)^8303*100000000000000^6255 ≤ 12748836032423^6255*500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105945677 500000000 12748836032423 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393699867/10000000000 : ℝ)^8303 ≤ (44065800447929/100000000000000 : ℝ)^6255 := by
    have hnat : (5393699867 : ℕ)^8303*100000000000000^6255 ≤ 44065800447929^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393699867 10000000000 44065800447929 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656156583/5000000000 : ℝ), (-105945677/500000000 : ℝ), (5393699867/10000000000 : ℝ)] ![(43185363509299/100000000000000 : ℝ), (12748836032423/100000000000000 : ℝ), (44065800447929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656156583/5000000000 : ℝ)|^8303 ≤ (43185363509299/100000000000000 : ℝ)^6255
        have hw : |(2656156583/5000000000 : ℝ)|=(2656156583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105945677/500000000 : ℝ)|^8303 ≤ (12748836032423/100000000000000 : ℝ)^6255
        have hw : |(-105945677/500000000 : ℝ)|=(105945677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393699867/10000000000 : ℝ)|^8303 ≤ (44065800447929/100000000000000 : ℝ)^6255
        have hw : |(5393699867/10000000000 : ℝ)|=(5393699867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s6_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656156593/5000000000 : ℝ)*x 0 + (5393699829/10000000000 : ℝ)*x 1 + (-529728391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656156593/5000000000 : ℝ)^8303 ≤ (43185363725119/100000000000000 : ℝ)^6255 := by
    have hnat : (2656156593 : ℕ)^8303*100000000000000^6255 ≤ 43185363725119^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656156593 5000000000 43185363725119 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393699829/10000000000 : ℝ)^8303 ≤ (22032900017913/50000000000000 : ℝ)^6255 := by
    have hnat : (5393699829 : ℕ)^8303*50000000000000^6255 ≤ 22032900017913^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393699829 10000000000 22032900017913 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529728391/2500000000 : ℝ)^8303 ≤ (6374418112051/50000000000000 : ℝ)^6255 := by
    have hnat : (529728391 : ℕ)^8303*50000000000000^6255 ≤ 6374418112051^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529728391 2500000000 6374418112051 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656156593/5000000000 : ℝ), (5393699829/10000000000 : ℝ), (-529728391/2500000000 : ℝ)] ![(43185363725119/100000000000000 : ℝ), (22032900017913/50000000000000 : ℝ), (6374418112051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656156593/5000000000 : ℝ)|^8303 ≤ (43185363725119/100000000000000 : ℝ)^6255
        have hw : |(2656156593/5000000000 : ℝ)|=(2656156593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393699829/10000000000 : ℝ)|^8303 ≤ (22032900017913/50000000000000 : ℝ)^6255
        have hw : |(5393699829/10000000000 : ℝ)|=(5393699829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529728391/2500000000 : ℝ)|^8303 ≤ (6374418112051/50000000000000 : ℝ)^6255
        have hw : |(-529728391/2500000000 : ℝ)|=(529728391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s6_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184594977/5000000000 : ℝ)*x 0 + (2249067923/5000000000 : ℝ)*x 1 + (1060992527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184594977/5000000000 : ℝ)^8303 ≤ (16658339073017/50000000000000 : ℝ)^6255 := by
    have hnat : (2184594977 : ℕ)^8303*50000000000000^6255 ≤ 16658339073017^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184594977 5000000000 16658339073017 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249067923/5000000000 : ℝ)^8303 ≤ (34628139751227/100000000000000 : ℝ)^6255 := by
    have hnat : (2249067923 : ℕ)^8303*100000000000000^6255 ≤ 34628139751227^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249067923 5000000000 34628139751227 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060992527/2500000000 : ℝ)^8303 ≤ (641103641731/2000000000000 : ℝ)^6255 := by
    have hnat : (1060992527 : ℕ)^8303*2000000000000^6255 ≤ 641103641731^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060992527 2500000000 641103641731 2000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184594977/5000000000 : ℝ), (2249067923/5000000000 : ℝ), (1060992527/2500000000 : ℝ)] ![(16658339073017/50000000000000 : ℝ), (34628139751227/100000000000000 : ℝ), (641103641731/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184594977/5000000000 : ℝ)|^8303 ≤ (16658339073017/50000000000000 : ℝ)^6255
        have hw : |(2184594977/5000000000 : ℝ)|=(2184594977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249067923/5000000000 : ℝ)|^8303 ≤ (34628139751227/100000000000000 : ℝ)^6255
        have hw : |(2249067923/5000000000 : ℝ)|=(2249067923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060992527/2500000000 : ℝ)|^8303 ≤ (641103641731/2000000000000 : ℝ)^6255
        have hw : |(1060992527/2500000000 : ℝ)|=(1060992527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5651/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14039/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11267/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (14331937705876469/100000000000000000000 : ℝ) := by
    have hpowers : (11267/100000 : ℝ)^4151 ≤ (14331937705876469/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11267 : ℕ)^4151*100000000000000000000^1024 ≤ 14331937705876469^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11267 100000 14331937705876469 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11267/100000 : ℝ)) (X := (14331937705876469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/25000 : ℝ) ^ (4151/1024 : ℝ) ≤ (4416630510937753/12500000000000000000 : ℝ) := by
    have hpowers : (3519/25000 : ℝ)^4151 ≤ (4416630510937753/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3519 : ℕ)^4151*12500000000000000000^1024 ≤ 4416630510937753^1024*25000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 25000 4416630510937753 12500000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/25000 : ℝ)) (X := (4416630510937753/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014331937705876469/50000000000000000000 : ℝ) ≤ (10000707025777061/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50014331937705876469/50000000000000000000 : ℝ)^1024 ≤ (10000707025777061/10000000000000000 : ℝ)^4151 := by
      have hnat : (50014331937705876469 : ℕ)^1024*10000000000000000^4151 ≤ 10000707025777061^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014331937705876469 50000000000000000000 10000707025777061 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000707025777061/10000000000000000 : ℝ)) (X := (50014331937705876469/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049664981793378493/100000000000000000000 : ℝ) ≤ (10001224944121893/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (100049664981793378493/100000000000000000000 : ℝ)^1024 ≤ (10001224944121893/10000000000000000 : ℝ)^4151 := by
      have hnat : (100049664981793378493 : ℕ)^1024*10000000000000000^4151 ≤ 10001224944121893^4151*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049664981793378493 100000000000000000000 10001224944121893 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001224944121893/10000000000000000 : ℝ)) (X := (100049664981793378493/100000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254416630510937753/6250000000000000000 : ℝ) ≤ (400069714498669/400000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (6254416630510937753/6250000000000000000 : ℝ)^1024 ≤ (400069714498669/400000000000000 : ℝ)^4151 := by
      have hnat : (6254416630510937753 : ℕ)^1024*400000000000000^4151 ≤ 400069714498669^4151*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254416630510937753 6250000000000000000 400069714498669 400000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400069714498669/400000000000000 : ℝ)) (X := (6254416630510937753/6250000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14331937705876469/100000000000000000000 : ℝ) ≤ ((28080315263425320061/28090000000000000000 : ℝ)+2*(4046237069/2194531250000 : ℝ)*(11267/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (28080315263425320061/28090000000000000000 : ℝ)+2*(4046237069/2194531250000 : ℝ)*(11267/100000 : ℝ)=(10000707025777061/10000000000000000 : ℝ) by norm_num, show 1+2*(14331937705876469/100000000000000000000 : ℝ)=(50014331937705876469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4416630510937753/12500000000000000000 : ℝ)+(14331937705876469/100000000000000000000 : ℝ) ≤ ((28080315263425320061/28090000000000000000 : ℝ)+(4046237069/2194531250000 : ℝ)*((3519/25000 : ℝ)+(11267/100000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (28080315263425320061/28090000000000000000 : ℝ)+(4046237069/2194531250000 : ℝ)*((3519/25000 : ℝ)+(11267/100000 : ℝ))=(10001224944121893/10000000000000000 : ℝ) by norm_num, show 1+(4416630510937753/12500000000000000000 : ℝ)+(14331937705876469/100000000000000000000 : ℝ)=(100049664981793378493/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4416630510937753/12500000000000000000 : ℝ) ≤ ((28080315263425320061/28090000000000000000 : ℝ)+2*(4046237069/2194531250000 : ℝ)*(3519/25000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (28080315263425320061/28090000000000000000 : ℝ)+2*(4046237069/2194531250000 : ℝ)*(3519/25000 : ℝ)=(400069714498669/400000000000000 : ℝ) by norm_num, show 1+2*(4416630510937753/12500000000000000000 : ℝ)=(6254416630510937753/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28080315263425320061/28090000000000000000 : ℝ)*(X 1 0+X 2 0)+(4046237069/2194531250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (28080315263425320061/28090000000000000000 : ℝ)) (alpha := (4046237069/2194531250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28080315263425320061/28090000000000000000 : ℝ)*(X 0 1+X 2 1)+(4046237069/2194531250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (28080315263425320061/28090000000000000000 : ℝ)) (alpha := (4046237069/2194531250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28080315263425320061/28090000000000000000 : ℝ)*(X 0 2+X 1 2)+(4046237069/2194531250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (28080315263425320061/28090000000000000000 : ℝ)) (alpha := (4046237069/2194531250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-436449401/2000000000 : ℝ)*X 0 0+(2697013691/5000000000 : ℝ)*X 0 1+(5264811883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534497169/1000000000 : ℝ)*X 1 0+(-449560317/2000000000 : ℝ)*X 1 1+(526481187/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336242927/2500000000 : ℝ)*X 2 0+(1316202967/2500000000 : ℝ)*X 2 1+(-2247801563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174767199/400000000 : ℝ)*X 0 0+(1060830647/2500000000 : ℝ)*X 0 1+(899756201/2000000000 : ℝ)*X 0 2+(174767199/400000000 : ℝ)*X 1 0+(1060830647/2500000000 : ℝ)*X 1 1+(899756201/2000000000 : ℝ)*X 1 2+(174767199/400000000 : ℝ)*X 2 0+(1060830647/2500000000 : ℝ)*X 2 1+(899756201/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2182252087/10000000000 : ℝ)*X 0 0+(1316284539/2500000000 : ℝ)*X 0 1+(5393699903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656156583/5000000000 : ℝ)*X 1 0+(-105945677/500000000 : ℝ)*X 1 1+(5393699867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656156593/5000000000 : ℝ)*X 2 0+(5393699829/10000000000 : ℝ)*X 2 1+(-529728391/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184594977/5000000000 : ℝ)*X 0 0+(2249067923/5000000000 : ℝ)*X 0 1+(1060992527/2500000000 : ℝ)*X 0 2+(2184594977/5000000000 : ℝ)*X 1 0+(2249067923/5000000000 : ℝ)*X 1 1+(1060992527/2500000000 : ℝ)*X 1 2+(2184594977/5000000000 : ℝ)*X 2 0+(2249067923/5000000000 : ℝ)*X 2 1+(1060992527/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126963960576931047987249/14045000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374423743/20000000000000 : ℝ)*(base19) + (353618183/20000000000000 : ℝ)*(base23) + (34766481/50000000000000 : ℝ)*(lower2) + (221840447/100000000000000 : ℝ)*(upper3) + (164429241/100000000000000 : ℝ)*(upper5) + (728355994438757/12500000000000 : ℝ)*(major0) + (728355994438757/12500000000000 : ℝ)*(major1) + (5826847955510057/100000000000000 : ℝ)*(major2) + (7739060739870339/100000000000000 : ℝ)*(sp0) + (1934777413659813/25000000000000 : ℝ)*(sp1) + (7739109758667051/100000000000000 : ℝ)*(sp2) + (3914556683177129/100000000000000 : ℝ)*(sp3) + (50786887627/100000000000000 : ℝ)*(sp4) + (5479951683/20000000000000 : ℝ)*(sp7) + (489323010366943/12500000000000 : ℝ)*(f.failure) + (3869555763378983/50000000000000 : ℝ)*(f.sum) + (4359438280837/14045000000000000000000000000 : ℝ)*base66 + (1022707163997304177/351125000000000000000000000000000 : ℝ)*base67 + (9284287276541553477/2809000000000000000000000000000000 : ℝ)*base69 + (1724627671154820823/351125000000000000000000000000000 : ℝ)*base72 + (43676664558259/7022500000000000000000000000 : ℝ)*base73 + (31247567889556446523/2809000000000000000000000000000000 : ℝ)*base76 + (426327199646720823/351125000000000000000000000000000 : ℝ)*base78 + (4925046938559154177/351125000000000000000000000000000 : ℝ)*base79 + (1450076995547/877812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2423781/1250000000000000000000 : ℝ)*base90 + (2423781/1250000000000000000000 : ℝ)*base92 + (14923781/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4294969966824291736898285427/1404500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (841921927/100000000000000 : ℝ)*(base19) + (852444083/100000000000000 : ℝ)*(base23) + (375113/50000000000000 : ℝ)*(upper2) + (6780373/12500000000000 : ℝ)*(upper3) + (26169889/25000000000000 : ℝ)*(upper5) + (5856402896218331/100000000000000 : ℝ)*(major0) + (5856402896218331/100000000000000 : ℝ)*(major1) + (5856402896218331/100000000000000 : ℝ)*(major2) + (11854067653/50000000000000 : ℝ)*(sp1) + (10213262677/50000000000000 : ℝ)*(sp2) + (7778366052496951/100000000000000 : ℝ)*(sp4) + (7778341502439717/100000000000000 : ℝ)*(sp5) + (7778344773527513/100000000000000 : ℝ)*(sp6) + (3934439638006157/100000000000000 : ℝ)*(sp7) + (3934439638006157/100000000000000 : ℝ)*(f.failure) + (7778366052496951/100000000000000 : ℝ)*(f.sum) + (37763062239547/14045000000000000000000000000 : ℝ)*base65 + (22589180832252561809/2809000000000000000000000000000000 : ℝ)*base68 + (3939343679831561809/2809000000000000000000000000000000 : ℝ)*base70 + (9443863698289438191/2809000000000000000000000000000000 : ℝ)*base71 + (3161614046003/877812500000000000000000000 : ℝ)*base74 + (27418073586414438191/2809000000000000000000000000000000 : ℝ)*base75 + (15290881782897438191/2809000000000000000000000000000000 : ℝ)*base77 + (60126784319610438191/2809000000000000000000000000000000 : ℝ)*base79 + (4651430153549/7022500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21806081/10000000000000000000000 : ℝ)*base89 + (21806081/10000000000000000000000 : ℝ)*base91 + (21806081/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1110_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1110_s7_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-545570207/2500000000 : ℝ)*x 0 + (1348412453/2500000000 : ℝ)*x 1 + (20567059/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545570207/2500000000 : ℝ)^8303 ≤ (13257390141053/100000000000000 : ℝ)^6255 := by
    have hnat : (545570207 : ℕ)^8303*100000000000000^6255 ≤ 13257390141053^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545570207 2500000000 13257390141053 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348412453/2500000000 : ℝ)^8303 ≤ (550815720137/1250000000000 : ℝ)^6255 := by
    have hnat : (1348412453 : ℕ)^8303*1250000000000^6255 ≤ 550815720137^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348412453 2500000000 550815720137 1250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20567059/39062500 : ℝ)^8303 ≤ (42677352233531/100000000000000 : ℝ)^6255 := by
    have hnat : (20567059 : ℕ)^8303*100000000000000^6255 ≤ 42677352233531^6255*39062500^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20567059 39062500 42677352233531 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545570207/2500000000 : ℝ), (1348412453/2500000000 : ℝ), (20567059/39062500 : ℝ)] ![(13257390141053/100000000000000 : ℝ), (550815720137/1250000000000 : ℝ), (42677352233531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545570207/2500000000 : ℝ)|^8303 ≤ (13257390141053/100000000000000 : ℝ)^6255
        have hw : |(-545570207/2500000000 : ℝ)|=(545570207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348412453/2500000000 : ℝ)|^8303 ≤ (550815720137/1250000000000 : ℝ)^6255
        have hw : |(1348412453/2500000000 : ℝ)|=(1348412453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20567059/39062500 : ℝ)|^8303 ≤ (42677352233531/100000000000000 : ℝ)^6255
        have hw : |(20567059/39062500 : ℝ)|=(20567059/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s7_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344876621/10000000000 : ℝ)*x 0 + (-2247458303/10000000000 : ℝ)*x 1 + (5265167193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344876621/10000000000 : ℝ)^8303 ≤ (5442138379443/12500000000000 : ℝ)^6255 := by
    have hnat : (5344876621 : ℕ)^8303*12500000000000^6255 ≤ 5442138379443^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344876621 10000000000 5442138379443 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247458303/10000000000 : ℝ)^8303 ≤ (13785539751889/100000000000000 : ℝ)^6255 := by
    have hnat : (2247458303 : ℕ)^8303*100000000000000^6255 ≤ 13785539751889^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247458303 10000000000 13785539751889 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265167193/10000000000 : ℝ)^8303 ≤ (5334669148891/12500000000000 : ℝ)^6255 := by
    have hnat : (5265167193 : ℕ)^8303*12500000000000^6255 ≤ 5334669148891^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265167193 10000000000 5334669148891 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344876621/10000000000 : ℝ), (-2247458303/10000000000 : ℝ), (5265167193/10000000000 : ℝ)] ![(5442138379443/12500000000000 : ℝ), (13785539751889/100000000000000 : ℝ), (5334669148891/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344876621/10000000000 : ℝ)|^8303 ≤ (5442138379443/12500000000000 : ℝ)^6255
        have hw : |(5344876621/10000000000 : ℝ)|=(5344876621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2247458303/10000000000 : ℝ)|^8303 ≤ (13785539751889/100000000000000 : ℝ)^6255
        have hw : |(-2247458303/10000000000 : ℝ)|=(2247458303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265167193/10000000000 : ℝ)|^8303 ≤ (5334669148891/12500000000000 : ℝ)^6255
        have hw : |(5265167193/10000000000 : ℝ)|=(5265167193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s7_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672438423/5000000000 : ℝ)*x 0 + (2632583521/5000000000 : ℝ)*x 1 + (-449491641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672438423/5000000000 : ℝ)^8303 ≤ (5442138683547/12500000000000 : ℝ)^6255 := by
    have hnat : (2672438423 : ℕ)^8303*12500000000000^6255 ≤ 5442138683547^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672438423 5000000000 5442138683547 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632583521/5000000000 : ℝ)^8303 ≤ (1066933789161/2500000000000 : ℝ)^6255 := by
    have hnat : (2632583521 : ℕ)^8303*2500000000000^6255 ≤ 1066933789161^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632583521 5000000000 1066933789161 2500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449491641/2000000000 : ℝ)^8303 ≤ (13785538953957/100000000000000 : ℝ)^6255 := by
    have hnat : (449491641 : ℕ)^8303*100000000000000^6255 ≤ 13785538953957^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449491641 2000000000 13785538953957 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672438423/5000000000 : ℝ), (2632583521/5000000000 : ℝ), (-449491641/2000000000 : ℝ)] ![(5442138683547/12500000000000 : ℝ), (1066933789161/2500000000000 : ℝ), (13785538953957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672438423/5000000000 : ℝ)|^8303 ≤ (5442138683547/12500000000000 : ℝ)^6255
        have hw : |(2672438423/5000000000 : ℝ)|=(2672438423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632583521/5000000000 : ℝ)|^8303 ≤ (1066933789161/2500000000000 : ℝ)^6255
        have hw : |(2632583521/5000000000 : ℝ)|=(2632583521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449491641/2000000000 : ℝ)|^8303 ≤ (13785538953957/100000000000000 : ℝ)^6255
        have hw : |(-449491641/2000000000 : ℝ)|=(449491641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s7_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184599367/5000000000 : ℝ)*x 0 + (2122022347/5000000000 : ℝ)*x 1 + (449805397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184599367/5000000000 : ℝ)^8303 ≤ (6663353403533/20000000000000 : ℝ)^6255 := by
    have hnat : (2184599367 : ℕ)^8303*20000000000000^6255 ≤ 6663353403533^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184599367 5000000000 6663353403533 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122022347/5000000000 : ℝ)^8303 ≤ (2003495618637/6250000000000 : ℝ)^6255 := by
    have hnat : (2122022347 : ℕ)^8303*6250000000000^6255 ≤ 2003495618637^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122022347 5000000000 2003495618637 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449805397/1000000000 : ℝ)^8303 ≤ (17313651535369/50000000000000 : ℝ)^6255 := by
    have hnat : (449805397 : ℕ)^8303*50000000000000^6255 ≤ 17313651535369^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449805397 1000000000 17313651535369 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184599367/5000000000 : ℝ), (2122022347/5000000000 : ℝ), (449805397/1000000000 : ℝ)] ![(6663353403533/20000000000000 : ℝ), (2003495618637/6250000000000 : ℝ), (17313651535369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184599367/5000000000 : ℝ)|^8303 ≤ (6663353403533/20000000000000 : ℝ)^6255
        have hw : |(2184599367/5000000000 : ℝ)|=(2184599367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122022347/5000000000 : ℝ)|^8303 ≤ (2003495618637/6250000000000 : ℝ)^6255
        have hw : |(2122022347/5000000000 : ℝ)|=(2122022347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449805397/1000000000 : ℝ)|^8303 ≤ (17313651535369/50000000000000 : ℝ)^6255
        have hw : |(449805397/1000000000 : ℝ)|=(449805397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s7_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182285913/10000000000 : ℝ)*x 0 + (5265489749/10000000000 : ℝ)*x 1 + (5393325917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182285913/10000000000 : ℝ)^8303 ≤ (13257431146943/100000000000000 : ℝ)^6255 := by
    have hnat : (2182285913 : ℕ)^8303*100000000000000^6255 ≤ 13257431146943^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182285913 10000000000 13257431146943 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265489749/10000000000 : ℝ)^8303 ≤ (10670205943691/25000000000000 : ℝ)^6255 := by
    have hnat : (5265489749 : ℕ)^8303*25000000000000^6255 ≤ 10670205943691^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265489749 10000000000 10670205943691 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393325917/10000000000 : ℝ)^8303 ≤ (22030872535533/50000000000000 : ℝ)^6255 := by
    have hnat : (5393325917 : ℕ)^8303*50000000000000^6255 ≤ 22030872535533^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393325917 10000000000 22030872535533 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182285913/10000000000 : ℝ), (5265489749/10000000000 : ℝ), (5393325917/10000000000 : ℝ)] ![(13257431146943/100000000000000 : ℝ), (10670205943691/25000000000000 : ℝ), (22030872535533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182285913/10000000000 : ℝ)|^8303 ≤ (13257431146943/100000000000000 : ℝ)^6255
        have hw : |(-2182285913/10000000000 : ℝ)|=(2182285913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265489749/10000000000 : ℝ)|^8303 ≤ (10670205943691/25000000000000 : ℝ)^6255
        have hw : |(5265489749/10000000000 : ℝ)|=(5265489749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393325917/10000000000 : ℝ)|^8303 ≤ (22030872535533/50000000000000 : ℝ)^6255
        have hw : |(5393325917/10000000000 : ℝ)|=(5393325917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s7_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312403277/10000000000 : ℝ)*x 0 + (-2119299529/10000000000 : ℝ)*x 1 + (5393325929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312403277/10000000000 : ℝ)^8303 ≤ (43186335897431/100000000000000 : ℝ)^6255 := by
    have hnat : (5312403277 : ℕ)^8303*100000000000000^6255 ≤ 43186335897431^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312403277 10000000000 43186335897431 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119299529/10000000000 : ℝ)^8303 ≤ (1275191888603/10000000000000 : ℝ)^6255 := by
    have hnat : (2119299529 : ℕ)^8303*10000000000000^6255 ≤ 1275191888603^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119299529 10000000000 1275191888603 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393325929/10000000000 : ℝ)^8303 ≤ (44061745201201/100000000000000 : ℝ)^6255 := by
    have hnat : (5393325929 : ℕ)^8303*100000000000000^6255 ≤ 44061745201201^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393325929 10000000000 44061745201201 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312403277/10000000000 : ℝ), (-2119299529/10000000000 : ℝ), (5393325929/10000000000 : ℝ)] ![(43186335897431/100000000000000 : ℝ), (1275191888603/10000000000000 : ℝ), (44061745201201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312403277/10000000000 : ℝ)|^8303 ≤ (43186335897431/100000000000000 : ℝ)^6255
        have hw : |(5312403277/10000000000 : ℝ)|=(5312403277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119299529/10000000000 : ℝ)|^8303 ≤ (1275191888603/10000000000000 : ℝ)^6255
        have hw : |(-2119299529/10000000000 : ℝ)|=(2119299529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393325929/10000000000 : ℝ)|^8303 ≤ (44061745201201/100000000000000 : ℝ)^6255
        have hw : |(5393325929/10000000000 : ℝ)|=(5393325929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s7_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328100817/2500000000 : ℝ)*x 0 + (5393325927/10000000000 : ℝ)*x 1 + (-2119299543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328100817/2500000000 : ℝ)^8303 ≤ (5398291975039/12500000000000 : ℝ)^6255 := by
    have hnat : (1328100817 : ℕ)^8303*12500000000000^6255 ≤ 5398291975039^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328100817 2500000000 5398291975039 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393325927/10000000000 : ℝ)^8303 ≤ (5507718147439/12500000000000 : ℝ)^6255 := by
    have hnat : (5393325927 : ℕ)^8303*12500000000000^6255 ≤ 5507718147439^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393325927 10000000000 5507718147439 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119299543/10000000000 : ℝ)^8303 ≤ (255038379957/2000000000000 : ℝ)^6255 := by
    have hnat : (2119299543 : ℕ)^8303*2000000000000^6255 ≤ 255038379957^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119299543 10000000000 255038379957 2000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328100817/2500000000 : ℝ), (5393325927/10000000000 : ℝ), (-2119299543/10000000000 : ℝ)] ![(5398291975039/12500000000000 : ℝ), (5507718147439/12500000000000 : ℝ), (255038379957/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328100817/2500000000 : ℝ)|^8303 ≤ (5398291975039/12500000000000 : ℝ)^6255
        have hw : |(1328100817/2500000000 : ℝ)|=(1328100817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393325927/10000000000 : ℝ)|^8303 ≤ (5507718147439/12500000000000 : ℝ)^6255
        have hw : |(5393325927/10000000000 : ℝ)|=(5393325927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119299543/10000000000 : ℝ)|^8303 ≤ (255038379957/2000000000000 : ℝ)^6255
        have hw : |(-2119299543/10000000000 : ℝ)|=(2119299543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s7_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184604251/5000000000 : ℝ)*x 0 + (2248708119/5000000000 : ℝ)*x 1 + (1061171197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184604251/5000000000 : ℝ)^8303 ≤ (16658432944977/50000000000000 : ℝ)^6255 := by
    have hnat : (2184604251 : ℕ)^8303*50000000000000^6255 ≤ 16658432944977^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184604251 5000000000 16658432944977 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248708119/5000000000 : ℝ)^8303 ≤ (34620786338773/100000000000000 : ℝ)^6255 := by
    have hnat : (2248708119 : ℕ)^8303*100000000000000^6255 ≤ 34620786338773^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248708119 5000000000 34620786338773 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061171197/2500000000 : ℝ)^8303 ≤ (32062347764023/100000000000000 : ℝ)^6255 := by
    have hnat : (1061171197 : ℕ)^8303*100000000000000^6255 ≤ 32062347764023^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061171197 2500000000 32062347764023 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184604251/5000000000 : ℝ), (2248708119/5000000000 : ℝ), (1061171197/2500000000 : ℝ)] ![(16658432944977/50000000000000 : ℝ), (34620786338773/100000000000000 : ℝ), (32062347764023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184604251/5000000000 : ℝ)|^8303 ≤ (16658432944977/50000000000000 : ℝ)^6255
        have hw : |(2184604251/5000000000 : ℝ)|=(2184604251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248708119/5000000000 : ℝ)|^8303 ≤ (34620786338773/100000000000000 : ℝ)^6255
        have hw : |(2248708119/5000000000 : ℝ)|=(2248708119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061171197/2500000000 : ℝ)|^8303 ≤ (32062347764023/100000000000000 : ℝ)^6255
        have hw : |(1061171197/2500000000 : ℝ)|=(1061171197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1131/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5651/50000 : ℝ) ^ (4151/1024 : ℝ) ≤ (14513270691658363/100000000000000000000 : ℝ) := by
    have hpowers : (5651/50000 : ℝ)^4151 ≤ (14513270691658363/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5651 : ℕ)^4151*100000000000000000000^1024 ≤ 14513270691658363^1024*50000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5651 50000 14513270691658363 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5651/50000 : ℝ)) (X := (14513270691658363/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14039/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (34958059939941529/100000000000000000000 : ℝ) := by
    have hpowers : (14039/100000 : ℝ)^4151 ≤ (34958059939941529/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14039 : ℕ)^4151*100000000000000000000^1024 ≤ 34958059939941529^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14039 100000 34958059939941529 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14039/100000 : ℝ)) (X := (34958059939941529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014513270691658363/50000000000000000000 : ℝ) ≤ (10000715970351347/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50014513270691658363/50000000000000000000 : ℝ)^1024 ≤ (10000715970351347/10000000000000000 : ℝ)^4151 := by
      have hnat : (50014513270691658363 : ℕ)^1024*10000000000000000^4151 ≤ 10000715970351347^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014513270691658363 50000000000000000000 10000715970351347 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000715970351347/10000000000000000 : ℝ)) (X := (50014513270691658363/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012367832657899973/25000000000000000000 : ℝ) ≤ (10001220168771943/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (25012367832657899973/25000000000000000000 : ℝ)^1024 ≤ (10001220168771943/10000000000000000 : ℝ)^4151 := by
      have hnat : (25012367832657899973 : ℕ)^1024*10000000000000000^4151 ≤ 10001220168771943^4151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012367832657899973 25000000000000000000 10001220168771943 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001220168771943/10000000000000000 : ℝ)) (X := (25012367832657899973/25000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034958059939941529/50000000000000000000 : ℝ) ≤ (10001724367192539/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50034958059939941529/50000000000000000000 : ℝ)^1024 ≤ (10001724367192539/10000000000000000 : ℝ)^4151 := by
      have hnat : (50034958059939941529 : ℕ)^1024*10000000000000000^4151 ≤ 10001724367192539^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034958059939941529 50000000000000000000 10001724367192539 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001724367192539/10000000000000000 : ℝ)) (X := (50034958059939941529/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14513270691658363/100000000000000000000 : ℝ) ≤ ((5472112541950496951/5474000000000000000 : ℝ)+2*(126049605149/68425000000000 : ℝ)*(5651/50000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (5472112541950496951/5474000000000000000 : ℝ)+2*(126049605149/68425000000000 : ℝ)*(5651/50000 : ℝ)=(10000715970351347/10000000000000000 : ℝ) by norm_num, show 1+2*(14513270691658363/100000000000000000000 : ℝ)=(50014513270691658363/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34958059939941529/100000000000000000000 : ℝ)+(14513270691658363/100000000000000000000 : ℝ) ≤ ((5472112541950496951/5474000000000000000 : ℝ)+(126049605149/68425000000000 : ℝ)*((14039/100000 : ℝ)+(5651/50000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (5472112541950496951/5474000000000000000 : ℝ)+(126049605149/68425000000000 : ℝ)*((14039/100000 : ℝ)+(5651/50000 : ℝ))=(10001220168771943/10000000000000000 : ℝ) by norm_num, show 1+(34958059939941529/100000000000000000000 : ℝ)+(14513270691658363/100000000000000000000 : ℝ)=(25012367832657899973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34958059939941529/100000000000000000000 : ℝ) ≤ ((5472112541950496951/5474000000000000000 : ℝ)+2*(126049605149/68425000000000 : ℝ)*(14039/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (5472112541950496951/5474000000000000000 : ℝ)+2*(126049605149/68425000000000 : ℝ)*(14039/100000 : ℝ)=(10001724367192539/10000000000000000 : ℝ) by norm_num, show 1+2*(34958059939941529/100000000000000000000 : ℝ)=(50034958059939941529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5472112541950496951/5474000000000000000 : ℝ)*(X 1 0+X 2 0)+(126049605149/68425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (5472112541950496951/5474000000000000000 : ℝ)) (alpha := (126049605149/68425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5472112541950496951/5474000000000000000 : ℝ)*(X 0 1+X 2 1)+(126049605149/68425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (5472112541950496951/5474000000000000000 : ℝ)) (alpha := (126049605149/68425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5472112541950496951/5474000000000000000 : ℝ)*(X 0 2+X 1 2)+(126049605149/68425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (5472112541950496951/5474000000000000000 : ℝ)) (alpha := (126049605149/68425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-545570207/2500000000 : ℝ)*X 0 0+(1348412453/2500000000 : ℝ)*X 0 1+(20567059/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344876621/10000000000 : ℝ)*X 1 0+(-2247458303/10000000000 : ℝ)*X 1 1+(5265167193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672438423/5000000000 : ℝ)*X 2 0+(2632583521/5000000000 : ℝ)*X 2 1+(-449491641/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184599367/5000000000 : ℝ)*X 0 0+(2122022347/5000000000 : ℝ)*X 0 1+(449805397/1000000000 : ℝ)*X 0 2+(2184599367/5000000000 : ℝ)*X 1 0+(2122022347/5000000000 : ℝ)*X 1 1+(449805397/1000000000 : ℝ)*X 1 2+(2184599367/5000000000 : ℝ)*X 2 0+(2122022347/5000000000 : ℝ)*X 2 1+(449805397/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2182285913/10000000000 : ℝ)*X 0 0+(5265489749/10000000000 : ℝ)*X 0 1+(5393325917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312403277/10000000000 : ℝ)*X 1 0+(-2119299529/10000000000 : ℝ)*X 1 1+(5393325929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328100817/2500000000 : ℝ)*X 2 0+(5393325927/10000000000 : ℝ)*X 2 1+(-2119299543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184604251/5000000000 : ℝ)*X 0 0+(2248708119/5000000000 : ℝ)*X 0 1+(1061171197/2500000000 : ℝ)*X 0 2+(2184604251/5000000000 : ℝ)*X 1 0+(2248708119/5000000000 : ℝ)*X 1 1+(1061171197/2500000000 : ℝ)*X 1 2+(2184604251/5000000000 : ℝ)*X 2 0+(2248708119/5000000000 : ℝ)*X 2 1+(1061171197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66601991447761288618017/13685000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1082715403/100000000000000 : ℝ)*(base19) + (1145626113/100000000000000 : ℝ)*(base23) + (70748719/50000000000000 : ℝ)*(lower2) + (50343/78125000000 : ℝ)*(upper3) + (10769347/12500000000000 : ℝ)*(upper5) + (2930028973999117/50000000000000 : ℝ)*(major0) + (2930028973999117/50000000000000 : ℝ)*(major1) + (2930028973999117/50000000000000 : ℝ)*(major2) + (7783180186497037/100000000000000 : ℝ)*(sp0) + (7783219481751243/100000000000000 : ℝ)*(sp1) + (1945804854710133/25000000000000 : ℝ)*(sp2) + (1968439120135721/50000000000000 : ℝ)*(sp3) + (5047246201/12500000000000 : ℝ)*(sp4) + (1692903211/10000000000000 : ℝ)*(sp7) + (3844624188773/97656250000 : ℝ)*(f.failure) + (3891610282233323/50000000000000 : ℝ)*(f.sum) + (26496699322129/3421250000000000000000000000 : ℝ)*base66 + (1944371820433032267/273700000000000000000000000000000 : ℝ)*base67 + (156978776605032267/273700000000000000000000000000000 : ℝ)*base69 + (2416807001648867733/273700000000000000000000000000000 : ℝ)*base72 + (42153390785649/13685000000000000000000000000 : ℝ)*base73 + (2904935120349532267/273700000000000000000000000000000 : ℝ)*base75 + (2637062196304167733/273700000000000000000000000000000 : ℝ)*base78 + (253162991086567733/273700000000000000000000000000000 : ℝ)*base80 + (8997656285571/855312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (217093/19531250000000000000 : ℝ)*base89 + (217093/19531250000000000000 : ℝ)*base91 + (217093/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92964120799949328488458899/34212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (580703681/100000000000000 : ℝ)*(base19) + (296905167/50000000000000 : ℝ)*(base23) + (34560077/50000000000000 : ℝ)*(upper3) + (13625827/100000000000000 : ℝ)*(lower4) + (14890879/25000000000000 : ℝ)*(upper5) + (736205035250283/12500000000000 : ℝ)*(major0) + (736205035250283/12500000000000 : ℝ)*(major1) + (736205035250283/12500000000000 : ℝ)*(major2) + (16212559807/100000000000000 : ℝ)*(sp1) + (1632860403/10000000000000 : ℝ)*(sp2) + (1955627836433273/25000000000000 : ℝ)*(sp4) + (1955623638117401/25000000000000 : ℝ)*(sp5) + (7822494423318727/100000000000000 : ℝ)*(sp6) + (989192281924057/25000000000000 : ℝ)*(sp7) + (989192281924057/25000000000000 : ℝ)*(f.failure) + (1955627836433273/25000000000000 : ℝ)*(f.sum) + (443992997311/3421250000000000000000000000 : ℝ)*base65 + (720705518882352867/68425000000000000000000000000000 : ℝ)*base68 + (209823999954152867/68425000000000000000000000000000 : ℝ)*base70 + (180590583301572133/68425000000000000000000000000000 : ℝ)*base71 + (120662474487151/13685000000000000000000000000 : ℝ)*base74 + (1178463935271927867/68425000000000000000000000000000 : ℝ)*base76 + (259972315969852867/68425000000000000000000000000000 : ℝ)*base78 + (1091048874890222133/68425000000000000000000000000000 : ℝ)*base79 + (62012198210461/13685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10726781/2500000000000000000000 : ℝ)*base89 + (10726781/2500000000000000000000 : ℝ)*base91 + (10726781/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1110_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1110_s8_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-136392919/625000000 : ℝ)*x 0 + (168548973/312500000 : ℝ)*x 1 + (5265246031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136392919/625000000 : ℝ)^8303 ≤ (331435938141/2500000000000 : ℝ)^6255 := by
    have hnat : (136392919 : ℕ)^8303*2500000000000^6255 ≤ 331435938141^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136392919 625000000 331435938141 2500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168548973/312500000 : ℝ)^8303 ≤ (22032180504527/50000000000000 : ℝ)^6255 := by
    have hnat : (168548973 : ℕ)^8303*50000000000000^6255 ≤ 22032180504527^6255*312500000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168548973 312500000 22032180504527 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265246031/10000000000 : ℝ)^8303 ≤ (21339100726257/50000000000000 : ℝ)^6255 := by
    have hnat : (5265246031 : ℕ)^8303*50000000000000^6255 ≤ 21339100726257^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265246031 10000000000 21339100726257 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136392919/625000000 : ℝ), (168548973/312500000 : ℝ), (5265246031/10000000000 : ℝ)] ![(331435938141/2500000000000 : ℝ), (22032180504527/50000000000000 : ℝ), (21339100726257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136392919/625000000 : ℝ)|^8303 ≤ (331435938141/2500000000000 : ℝ)^6255
        have hw : |(-136392919/625000000 : ℝ)|=(136392919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168548973/312500000 : ℝ)|^8303 ≤ (22032180504527/50000000000000 : ℝ)^6255
        have hw : |(168548973/312500000 : ℝ)|=(168548973/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265246031/10000000000 : ℝ)|^8303 ≤ (21339100726257/50000000000000 : ℝ)^6255
        have hw : |(5265246031/10000000000 : ℝ)|=(5265246031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334053543/625000000 : ℝ)*x 0 + (-2247381553/10000000000 : ℝ)*x 1 + (1053049061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334053543/625000000 : ℝ)^8303 ≤ (43536891508383/100000000000000 : ℝ)^6255 := by
    have hnat : (334053543 : ℕ)^8303*100000000000000^6255 ≤ 43536891508383^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334053543 625000000 43536891508383 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247381553/10000000000 : ℝ)^8303 ≤ (13784914844281/100000000000000 : ℝ)^6255 := by
    have hnat : (2247381553 : ℕ)^8303*100000000000000^6255 ≤ 13784914844281^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247381553 10000000000 13784914844281 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053049061/2000000000 : ℝ)^8303 ≤ (42678193641061/100000000000000 : ℝ)^6255 := by
    have hnat : (1053049061 : ℕ)^8303*100000000000000^6255 ≤ 42678193641061^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053049061 2000000000 42678193641061 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334053543/625000000 : ℝ), (-2247381553/10000000000 : ℝ), (1053049061/2000000000 : ℝ)] ![(43536891508383/100000000000000 : ℝ), (13784914844281/100000000000000 : ℝ), (42678193641061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334053543/625000000 : ℝ)|^8303 ≤ (43536891508383/100000000000000 : ℝ)^6255
        have hw : |(334053543/625000000 : ℝ)|=(334053543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2247381553/10000000000 : ℝ)|^8303 ≤ (13784914844281/100000000000000 : ℝ)^6255
        have hw : |(-2247381553/10000000000 : ℝ)|=(2247381553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053049061/2000000000 : ℝ)|^8303 ≤ (42678193641061/100000000000000 : ℝ)^6255
        have hw : |(1053049061/2000000000 : ℝ)|=(1053049061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668107137/1250000000 : ℝ)*x 0 + (526524473/1000000000 : ℝ)*x 1 + (-224738177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668107137/1250000000 : ℝ)^8303 ≤ (43536895919913/100000000000000 : ℝ)^6255 := by
    have hnat : (668107137 : ℕ)^8303*100000000000000^6255 ≤ 43536895919913^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668107137 1250000000 43536895919913 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526524473/1000000000 : ℝ)^8303 ≤ (21339093727153/50000000000000 : ℝ)^6255 := by
    have hnat : (526524473 : ℕ)^8303*50000000000000^6255 ≤ 21339093727153^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526524473 1000000000 21339093727153 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224738177/1000000000 : ℝ)^8303 ≤ (13784916611111/100000000000000 : ℝ)^6255 := by
    have hnat : (224738177 : ℕ)^8303*100000000000000^6255 ≤ 13784916611111^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224738177 1000000000 13784916611111 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668107137/1250000000 : ℝ), (526524473/1000000000 : ℝ), (-224738177/1000000000 : ℝ)] ![(43536895919913/100000000000000 : ℝ), (21339093727153/50000000000000 : ℝ), (13784916611111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668107137/1250000000 : ℝ)|^8303 ≤ (43536895919913/100000000000000 : ℝ)^6255
        have hw : |(668107137/1250000000 : ℝ)|=(668107137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526524473/1000000000 : ℝ)|^8303 ≤ (21339093727153/50000000000000 : ℝ)^6255
        have hw : |(526524473/1000000000 : ℝ)|=(526524473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224738177/1000000000 : ℝ)|^8303 ≤ (13784916611111/100000000000000 : ℝ)^6255
        have hw : |(-224738177/1000000000 : ℝ)|=(224738177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436920303/1000000000 : ℝ)*x 0 + (4244202759/10000000000 : ℝ)*x 1 + (4497894627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436920303/1000000000 : ℝ)^8303 ≤ (33316810502029/100000000000000 : ℝ)^6255 := by
    have hnat : (436920303 : ℕ)^8303*100000000000000^6255 ≤ 33316810502029^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436920303 1000000000 33316810502029 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244202759/10000000000 : ℝ)^8303 ≤ (8014378674599/25000000000000 : ℝ)^6255 := by
    have hnat : (4244202759 : ℕ)^8303*25000000000000^6255 ≤ 8014378674599^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244202759 10000000000 8014378674599 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497894627/10000000000 : ℝ)^8303 ≤ (3462567477907/10000000000000 : ℝ)^6255 := by
    have hnat : (4497894627 : ℕ)^8303*10000000000000^6255 ≤ 3462567477907^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497894627 10000000000 3462567477907 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436920303/1000000000 : ℝ), (4244202759/10000000000 : ℝ), (4497894627/10000000000 : ℝ)] ![(33316810502029/100000000000000 : ℝ), (8014378674599/25000000000000 : ℝ), (3462567477907/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436920303/1000000000 : ℝ)|^8303 ≤ (33316810502029/100000000000000 : ℝ)^6255
        have hw : |(436920303/1000000000 : ℝ)|=(436920303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244202759/10000000000 : ℝ)|^8303 ≤ (8014378674599/25000000000000 : ℝ)^6255
        have hw : |(4244202759/10000000000 : ℝ)|=(4244202759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497894627/10000000000 : ℝ)|^8303 ≤ (3462567477907/10000000000000 : ℝ)^6255
        have hw : |(4497894627/10000000000 : ℝ)|=(4497894627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436458369/2000000000 : ℝ)*x 0 + (5265567337/10000000000 : ℝ)*x 1 + (1348311131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436458369/2000000000 : ℝ)^8303 ≤ (3314369745789/25000000000000 : ℝ)^6255 := by
    have hnat : (436458369 : ℕ)^8303*25000000000000^6255 ≤ 3314369745789^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436458369 2000000000 3314369745789 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265567337/10000000000 : ℝ)^8303 ≤ (1333801831357/3125000000000 : ℝ)^6255 := by
    have hnat : (5265567337 : ℕ)^8303*3125000000000^6255 ≤ 1333801831357^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265567337 10000000000 1333801831357 3125000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348311131/2500000000 : ℝ)^8303 ≤ (11015215600079/25000000000000 : ℝ)^6255 := by
    have hnat : (1348311131 : ℕ)^8303*25000000000000^6255 ≤ 11015215600079^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348311131 2500000000 11015215600079 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436458369/2000000000 : ℝ), (5265567337/10000000000 : ℝ), (1348311131/2500000000 : ℝ)] ![(3314369745789/25000000000000 : ℝ), (1333801831357/3125000000000 : ℝ), (11015215600079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436458369/2000000000 : ℝ)|^8303 ≤ (3314369745789/25000000000000 : ℝ)^6255
        have hw : |(-436458369/2000000000 : ℝ)|=(436458369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265567337/10000000000 : ℝ)|^8303 ≤ (1333801831357/3125000000000 : ℝ)^6255
        have hw : |(5265567337/10000000000 : ℝ)|=(5265567337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348311131/2500000000 : ℝ)|^8303 ≤ (11015215600079/25000000000000 : ℝ)^6255
        have hw : |(1348311131/2500000000 : ℝ)|=(1348311131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312423549/10000000000 : ℝ)*x 0 + (-1059691333/5000000000 : ℝ)*x 1 + (215729781/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312423549/10000000000 : ℝ)^8303 ≤ (21593277326701/50000000000000 : ℝ)^6255 := by
    have hnat : (5312423549 : ℕ)^8303*50000000000000^6255 ≤ 21593277326701^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312423549 10000000000 21593277326701 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059691333/5000000000 : ℝ)^8303 ≤ (6376291458291/50000000000000 : ℝ)^6255 := by
    have hnat : (1059691333 : ℕ)^8303*50000000000000^6255 ≤ 6376291458291^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059691333 5000000000 6376291458291 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215729781/400000000 : ℝ)^8303 ≤ (44060862411161/100000000000000 : ℝ)^6255 := by
    have hnat : (215729781 : ℕ)^8303*100000000000000^6255 ≤ 44060862411161^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215729781 400000000 44060862411161 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312423549/10000000000 : ℝ), (-1059691333/5000000000 : ℝ), (215729781/400000000 : ℝ)] ![(21593277326701/50000000000000 : ℝ), (6376291458291/50000000000000 : ℝ), (44060862411161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312423549/10000000000 : ℝ)|^8303 ≤ (21593277326701/50000000000000 : ℝ)^6255
        have hw : |(5312423549/10000000000 : ℝ)|=(5312423549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059691333/5000000000 : ℝ)|^8303 ≤ (6376291458291/50000000000000 : ℝ)^6255
        have hw : |(-1059691333/5000000000 : ℝ)|=(1059691333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215729781/400000000 : ℝ)|^8303 ≤ (44060862411161/100000000000000 : ℝ)^6255
        have hw : |(215729781/400000000 : ℝ)|=(215729781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106248471/200000000 : ℝ)*x 0 + (1348311131/2500000000 : ℝ)*x 1 + (-1059691333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106248471/200000000 : ℝ)^8303 ≤ (43186554664193/100000000000000 : ℝ)^6255 := by
    have hnat : (106248471 : ℕ)^8303*100000000000000^6255 ≤ 43186554664193^6255*200000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106248471 200000000 43186554664193 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348311131/2500000000 : ℝ)^8303 ≤ (11015215600079/25000000000000 : ℝ)^6255 := by
    have hnat : (1348311131 : ℕ)^8303*25000000000000^6255 ≤ 11015215600079^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348311131 2500000000 11015215600079 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059691333/5000000000 : ℝ)^8303 ≤ (6376291458291/50000000000000 : ℝ)^6255 := by
    have hnat : (1059691333 : ℕ)^8303*50000000000000^6255 ≤ 6376291458291^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059691333 5000000000 6376291458291 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106248471/200000000 : ℝ), (1348311131/2500000000 : ℝ), (-1059691333/5000000000 : ℝ)] ![(43186554664193/100000000000000 : ℝ), (11015215600079/25000000000000 : ℝ), (6376291458291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106248471/200000000 : ℝ)|^8303 ≤ (43186554664193/100000000000000 : ℝ)^6255
        have hw : |(106248471/200000000 : ℝ)|=(106248471/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348311131/2500000000 : ℝ)|^8303 ≤ (11015215600079/25000000000000 : ℝ)^6255
        have hw : |(1348311131/2500000000 : ℝ)|=(1348311131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059691333/5000000000 : ℝ)|^8303 ≤ (6376291458291/50000000000000 : ℝ)^6255
        have hw : |(-1059691333/5000000000 : ℝ)|=(1059691333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873842507/2000000000 : ℝ)*x 0 + (2248629271/5000000000 : ℝ)*x 1 + (265302589/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873842507/2000000000 : ℝ)^8303 ≤ (6663381342449/20000000000000 : ℝ)^6255 := by
    have hnat : (873842507 : ℕ)^8303*20000000000000^6255 ≤ 6663381342449^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873842507 2000000000 6663381342449 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248629271/5000000000 : ℝ)^8303 ≤ (6923834990431/20000000000000 : ℝ)^6255 := by
    have hnat : (2248629271 : ℕ)^8303*20000000000000^6255 ≤ 6923834990431^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248629271 5000000000 6923834990431 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265302589/625000000 : ℝ)^8303 ≤ (32063918314167/100000000000000 : ℝ)^6255 := by
    have hnat : (265302589 : ℕ)^8303*100000000000000^6255 ≤ 32063918314167^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265302589 625000000 32063918314167 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873842507/2000000000 : ℝ), (2248629271/5000000000 : ℝ), (265302589/625000000 : ℝ)] ![(6663381342449/20000000000000 : ℝ), (6923834990431/20000000000000 : ℝ), (32063918314167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873842507/2000000000 : ℝ)|^8303 ≤ (6663381342449/20000000000000 : ℝ)^6255
        have hw : |(873842507/2000000000 : ℝ)|=(873842507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248629271/5000000000 : ℝ)|^8303 ≤ (6923834990431/20000000000000 : ℝ)^6255
        have hw : |(2248629271/5000000000 : ℝ)|=(2248629271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265302589/625000000 : ℝ)|^8303 ≤ (32063918314167/100000000000000 : ℝ)^6255
        have hw : |(265302589/625000000 : ℝ)|=(265302589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s8_8 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-86417149/10000000000 : ℝ)*x 0 + (37994663/62500000 : ℝ)*x 1 + (230710469/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86417149/10000000000 : ℝ)^8303 ≤ (36478374031/20000000000000 : ℝ)^6255 := by
    have hnat : (86417149 : ℕ)^8303*20000000000000^6255 ≤ 36478374031^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86417149 10000000000 36478374031 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37994663/62500000 : ℝ)^8303 ≤ (51649810800913/100000000000000 : ℝ)^6255 := by
    have hnat : (37994663 : ℕ)^8303*100000000000000^6255 ≤ 51649810800913^6255*62500000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37994663 62500000 51649810800913 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230710469/400000000 : ℝ)^8303 ≤ (48167797312159/100000000000000 : ℝ)^6255 := by
    have hnat : (230710469 : ℕ)^8303*100000000000000^6255 ≤ 48167797312159^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230710469 400000000 48167797312159 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86417149/10000000000 : ℝ), (37994663/62500000 : ℝ), (230710469/400000000 : ℝ)] ![(36478374031/20000000000000 : ℝ), (51649810800913/100000000000000 : ℝ), (48167797312159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86417149/10000000000 : ℝ)|^8303 ≤ (36478374031/20000000000000 : ℝ)^6255
        have hw : |(-86417149/10000000000 : ℝ)|=(86417149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37994663/62500000 : ℝ)|^8303 ≤ (51649810800913/100000000000000 : ℝ)^6255
        have hw : |(37994663/62500000 : ℝ)|=(37994663/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230710469/400000000 : ℝ)|^8303 ≤ (48167797312159/100000000000000 : ℝ)^6255
        have hw : |(230710469/400000000 : ℝ)|=(230710469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (707/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1403/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1131/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1131/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1131/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1131/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1131/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1131/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1131/10000 : ℝ) ^ (4151/1024 : ℝ) ≤ (14554959751558571/100000000000000000000 : ℝ) := by
    have hpowers : (1131/10000 : ℝ)^4151 ≤ (14554959751558571/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1131 : ℕ)^4151*100000000000000000000^1024 ≤ 14554959751558571^1024*10000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1131 10000 14554959751558571 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1131/10000 : ℝ)) (X := (14554959751558571/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14031/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (1743868902796279/5000000000000000000 : ℝ) := by
    have hpowers : (14031/100000 : ℝ)^4151 ≤ (1743868902796279/5000000000000000000 : ℝ)^1024 := by
      have hnat : (14031 : ℕ)^4151*5000000000000000000^1024 ≤ 1743868902796279^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14031 100000 1743868902796279 5000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14031/100000 : ℝ)) (X := (1743868902796279/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014554959751558571/50000000000000000000 : ℝ) ≤ (10000718026735437/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50014554959751558571/50000000000000000000 : ℝ)^1024 ≤ (10000718026735437/10000000000000000 : ℝ)^4151 := by
      have hnat : (50014554959751558571 : ℕ)^1024*10000000000000000^4151 ≤ 10000718026735437^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014554959751558571 50000000000000000000 10000718026735437 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000718026735437/10000000000000000 : ℝ)) (X := (50014554959751558571/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049432337807484151/100000000000000000000 : ℝ) ≤ (10001219207225717/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (100049432337807484151/100000000000000000000 : ℝ)^1024 ≤ (10001219207225717/10000000000000000 : ℝ)^4151 := by
      have hnat : (100049432337807484151 : ℕ)^1024*10000000000000000^4151 ≤ 10001219207225717^4151*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049432337807484151 100000000000000000000 10001219207225717 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001219207225717/10000000000000000 : ℝ)) (X := (100049432337807484151/100000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501743868902796279/2500000000000000000 : ℝ) ≤ (10001720387715997/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (2501743868902796279/2500000000000000000 : ℝ)^1024 ≤ (10001720387715997/10000000000000000 : ℝ)^4151 := by
      have hnat : (2501743868902796279 : ℕ)^1024*10000000000000000^4151 ≤ 10001720387715997^4151*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501743868902796279 2500000000000000000 10001720387715997 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001720387715997/10000000000000000 : ℝ)) (X := (2501743868902796279/2500000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14554959751558571/100000000000000000000 : ℝ) ≤ ((9066872349352330159/9070000000000000000 : ℝ)+2*(12529512257/6802500000000 : ℝ)*(1131/10000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (9066872349352330159/9070000000000000000 : ℝ)+2*(12529512257/6802500000000 : ℝ)*(1131/10000 : ℝ)=(10000718026735437/10000000000000000 : ℝ) by norm_num, show 1+2*(14554959751558571/100000000000000000000 : ℝ)=(50014554959751558571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1743868902796279/5000000000000000000 : ℝ)+(14554959751558571/100000000000000000000 : ℝ) ≤ ((9066872349352330159/9070000000000000000 : ℝ)+(12529512257/6802500000000 : ℝ)*((14031/100000 : ℝ)+(1131/10000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (9066872349352330159/9070000000000000000 : ℝ)+(12529512257/6802500000000 : ℝ)*((14031/100000 : ℝ)+(1131/10000 : ℝ))=(10001219207225717/10000000000000000 : ℝ) by norm_num, show 1+(1743868902796279/5000000000000000000 : ℝ)+(14554959751558571/100000000000000000000 : ℝ)=(100049432337807484151/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1743868902796279/5000000000000000000 : ℝ) ≤ ((9066872349352330159/9070000000000000000 : ℝ)+2*(12529512257/6802500000000 : ℝ)*(14031/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (9066872349352330159/9070000000000000000 : ℝ)+2*(12529512257/6802500000000 : ℝ)*(14031/100000 : ℝ)=(10001720387715997/10000000000000000 : ℝ) by norm_num, show 1+2*(1743868902796279/5000000000000000000 : ℝ)=(2501743868902796279/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9066872349352330159/9070000000000000000 : ℝ)*(X 1 0+X 2 0)+(12529512257/6802500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (9066872349352330159/9070000000000000000 : ℝ)) (alpha := (12529512257/6802500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9066872349352330159/9070000000000000000 : ℝ)*(X 0 1+X 2 1)+(12529512257/6802500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (9066872349352330159/9070000000000000000 : ℝ)) (alpha := (12529512257/6802500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9066872349352330159/9070000000000000000 : ℝ)*(X 0 2+X 1 2)+(12529512257/6802500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (9066872349352330159/9070000000000000000 : ℝ)) (alpha := (12529512257/6802500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-136392919/625000000 : ℝ)*X 0 0+(168548973/312500000 : ℝ)*X 0 1+(5265246031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334053543/625000000 : ℝ)*X 1 0+(-2247381553/10000000000 : ℝ)*X 1 1+(1053049061/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668107137/1250000000 : ℝ)*X 2 0+(526524473/1000000000 : ℝ)*X 2 1+(-224738177/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436920303/1000000000 : ℝ)*X 0 0+(4244202759/10000000000 : ℝ)*X 0 1+(4497894627/10000000000 : ℝ)*X 0 2+(436920303/1000000000 : ℝ)*X 1 0+(4244202759/10000000000 : ℝ)*X 1 1+(4497894627/10000000000 : ℝ)*X 1 2+(436920303/1000000000 : ℝ)*X 2 0+(4244202759/10000000000 : ℝ)*X 2 1+(4497894627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436458369/2000000000 : ℝ)*X 0 0+(5265567337/10000000000 : ℝ)*X 0 1+(1348311131/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312423549/10000000000 : ℝ)*X 1 0+(-1059691333/5000000000 : ℝ)*X 1 1+(215729781/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106248471/200000000 : ℝ)*X 2 0+(1348311131/2500000000 : ℝ)*X 2 1+(-1059691333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873842507/2000000000 : ℝ)*X 0 0+(2248629271/5000000000 : ℝ)*X 0 1+(265302589/625000000 : ℝ)*X 0 2+(873842507/2000000000 : ℝ)*X 1 0+(2248629271/5000000000 : ℝ)*X 1 1+(265302589/625000000 : ℝ)*X 1 2+(873842507/2000000000 : ℝ)*X 2 0+(2248629271/5000000000 : ℝ)*X 2 1+(265302589/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-86417149/10000000000 : ℝ)*X 0 0+(37994663/62500000 : ℝ)*X 0 1+(230710469/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s8_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (226069485588332041492058583/113375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35196571/5000000000000 : ℝ)*(lower2) + (601242287/100000000000000 : ℝ)*(lower3) + (259970281/50000000000000 : ℝ)*(lower4) + (81503731/100000000000000 : ℝ)*(lower5) + (2933676443626779/50000000000000 : ℝ)*(major0) + (2933676443626779/50000000000000 : ℝ)*(major1) + (2933676443626779/50000000000000 : ℝ)*(major2) + (1558581026832991/20000000000000 : ℝ)*(sp0) + (1948223663108767/25000000000000 : ℝ)*(sp1) + (3896426674878311/50000000000000 : ℝ)*(sp2) + (3941796044238493/100000000000000 : ℝ)*(sp3) + (3002273389/20000000000000 : ℝ)*(sp5) + (56314045391/100000000000000 : ℝ)*(sp6) + (4529637059/100000000000000 : ℝ)*(sp8) + (3941796044238493/100000000000000 : ℝ)*(f.failure) + (7792909663802013/100000000000000 : ℝ)*(f.sum) + (5090859471437/907000000000000000000000000 : ℝ)*base66 + (3111187731218772139/453500000000000000000000000000000 : ℝ)*base68 + (8740931154982772139/453500000000000000000000000000000 : ℝ)*base70 + (45029262804309227861/453500000000000000000000000000000 : ℝ)*base71 + (17046864769/36280000000000000000000000 : ℝ)*base73 + (8122707023430272139/453500000000000000000000000000000 : ℝ)*base76 + (14788895161646272139/453500000000000000000000000000000 : ℝ)*base78 + (1720209512722772139/453500000000000000000000000000000 : ℝ)*base80 + (7044222820439/907000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (71372369/10000000000000000000000 : ℝ)*base89 + (71372369/10000000000000000000000 : ℝ)*base91 + (71372369/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1612045981734253880451/113375000000000000000000000 : ℝ) := by norm_num
    linear_combination (736506689/100000000000000 : ℝ)*(lower2) + (152301/62500000000 : ℝ)*(lower3) + (735352473/100000000000000 : ℝ)*(lower4) + (247719131/100000000000000 : ℝ)*(lower5) + (5896991763727939/100000000000000 : ℝ)*(major0) + (5896991763727939/100000000000000 : ℝ)*(major1) + (5896991763727939/100000000000000 : ℝ)*(major2) + (114383339/100000000000000 : ℝ)*(sp2) + (5704666881/100000000000000 : ℝ)*(sp3) + (3916134268562913/50000000000000 : ℝ)*(sp4) + (7832275064591809/100000000000000 : ℝ)*(sp5) + (783227495020847/10000000000000 : ℝ)*(sp6) + (990425571060063/25000000000000 : ℝ)*(sp7) + (12748957/195312500000 : ℝ)*(sp8) + (1980853994453567/50000000000000 : ℝ)*(f.failure) + (7832275064591809/100000000000000 : ℝ)*(f.sum) + (669427178521/68025000000000000000000000 : ℝ)*base65 + (53116362008088836903/2721000000000000000000000000000000 : ℝ)*base67 + (57657292463105163097/2721000000000000000000000000000000 : ℝ)*base70 + (55521938550077163097/2721000000000000000000000000000000 : ℝ)*base72 + (1438366611287/544200000000000000000000000 : ℝ)*base73 + (2478015102326163097/2721000000000000000000000000000000 : ℝ)*base76 + (19709134991859836903/2721000000000000000000000000000000 : ℝ)*base77 + (9189126647460836903/2721000000000000000000000000000000 : ℝ)*base79 + (3859528527199/2721000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (21152389/5000000000000000000000 : ℝ)*base90 + (21152389/5000000000000000000000 : ℝ)*base92 + (21152389/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1110_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1110_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1110_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1110_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1110_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
