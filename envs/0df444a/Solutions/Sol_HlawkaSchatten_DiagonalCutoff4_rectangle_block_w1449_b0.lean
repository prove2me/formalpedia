-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1449_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:55.769272+00:00
-- url     : https://prove2.me/submissions/e4f642b0-c490-4ad4-a3a3-6bcf9f717c0d

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
theorem support_rectangle_w1449_s0_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-873772719/5000000000 : ℝ)*x 0 + (5951971267/10000000000 : ℝ)*x 1 + (2417894907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873772719/5000000000 : ℝ)^4409 ≤ (10309905824961/100000000000000 : ℝ)^3385 := by
    have hnat : (873772719 : ℕ)^4409*100000000000000^3385 ≤ 10309905824961^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873772719 5000000000 10309905824961 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5951971267/10000000000 : ℝ)^4409 ≤ (12718422213457/25000000000000 : ℝ)^3385 := by
    have hnat : (5951971267 : ℕ)^4409*25000000000000^3385 ≤ 12718422213457^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5951971267 10000000000 12718422213457 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417894907/5000000000 : ℝ)^4409 ≤ (19408202653311/50000000000000 : ℝ)^3385 := by
    have hnat : (2417894907 : ℕ)^4409*50000000000000^3385 ≤ 19408202653311^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417894907 5000000000 19408202653311 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-873772719/5000000000 : ℝ), (5951971267/10000000000 : ℝ), (2417894907/5000000000 : ℝ)] ![(10309905824961/100000000000000 : ℝ), (12718422213457/25000000000000 : ℝ), (19408202653311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-873772719/5000000000 : ℝ)|^4409 ≤ (10309905824961/100000000000000 : ℝ)^3385
        have hw : |(-873772719/5000000000 : ℝ)|=(873772719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5951971267/10000000000 : ℝ)|^4409 ≤ (12718422213457/25000000000000 : ℝ)^3385
        have hw : |(5951971267/10000000000 : ℝ)|=(5951971267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2417894907/5000000000 : ℝ)|^4409 ≤ (19408202653311/50000000000000 : ℝ)^3385
        have hw : |(2417894907/5000000000 : ℝ)|=(2417894907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s0_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744938831/5000000000 : ℝ)*x 0 + (-297150543/1250000000 : ℝ)*x 1 + (604473711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744938831/5000000000 : ℝ)^4409 ≤ (457907216623/1000000000000 : ℝ)^3385 := by
    have hnat : (2744938831 : ℕ)^4409*1000000000000^3385 ≤ 457907216623^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744938831 5000000000 457907216623 1000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297150543/1250000000 : ℝ)^4409 ≤ (15392874336891/100000000000000 : ℝ)^3385 := by
    have hnat : (297150543 : ℕ)^4409*100000000000000^3385 ≤ 15392874336891^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297150543 1250000000 15392874336891 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604473711/1250000000 : ℝ)^4409 ≤ (9704100997319/25000000000000 : ℝ)^3385 := by
    have hnat : (604473711 : ℕ)^4409*25000000000000^3385 ≤ 9704100997319^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604473711 1250000000 9704100997319 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744938831/5000000000 : ℝ), (-297150543/1250000000 : ℝ), (604473711/1250000000 : ℝ)] ![(457907216623/1000000000000 : ℝ), (15392874336891/100000000000000 : ℝ), (9704100997319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744938831/5000000000 : ℝ)|^4409 ≤ (457907216623/1000000000000 : ℝ)^3385
        have hw : |(2744938831/5000000000 : ℝ)|=(2744938831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297150543/1250000000 : ℝ)|^4409 ≤ (15392874336891/100000000000000 : ℝ)^3385
        have hw : |(-297150543/1250000000 : ℝ)|=(297150543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604473711/1250000000 : ℝ)|^4409 ≤ (9704100997319/25000000000000 : ℝ)^3385
        have hw : |(604473711/1250000000 : ℝ)|=(604473711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s0_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (548987753/1000000000 : ℝ)*x 0 + (4835789647/10000000000 : ℝ)*x 1 + (-594301141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548987753/1000000000 : ℝ)^4409 ≤ (45790720228231/100000000000000 : ℝ)^3385 := by
    have hnat : (548987753 : ℕ)^4409*100000000000000^3385 ≤ 45790720228231^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548987753 1000000000 45790720228231 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4835789647/10000000000 : ℝ)^4409 ≤ (4852050445077/12500000000000 : ℝ)^3385 := by
    have hnat : (4835789647 : ℕ)^4409*12500000000000^3385 ≤ 4852050445077^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835789647 10000000000 4852050445077 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594301141/2500000000 : ℝ)^4409 ≤ (1924109524047/12500000000000 : ℝ)^3385 := by
    have hnat : (594301141 : ℕ)^4409*12500000000000^3385 ≤ 1924109524047^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594301141 2500000000 1924109524047 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(548987753/1000000000 : ℝ), (4835789647/10000000000 : ℝ), (-594301141/2500000000 : ℝ)] ![(45790720228231/100000000000000 : ℝ), (4852050445077/12500000000000 : ℝ), (1924109524047/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(548987753/1000000000 : ℝ)|^4409 ≤ (45790720228231/100000000000000 : ℝ)^3385
        have hw : |(548987753/1000000000 : ℝ)|=(548987753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4835789647/10000000000 : ℝ)|^4409 ≤ (4852050445077/12500000000000 : ℝ)^3385
        have hw : |(4835789647/10000000000 : ℝ)|=(4835789647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-594301141/2500000000 : ℝ)|^4409 ≤ (1924109524047/12500000000000 : ℝ)^3385
        have hw : |(-594301141/2500000000 : ℝ)|=(594301141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s0_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4163146063/10000000000 : ℝ)*x 0 + (155145831/500000000 : ℝ)*x 1 + (5535296213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163146063/10000000000 : ℝ)^4409 ≤ (6387375915371/20000000000000 : ℝ)^3385 := by
    have hnat : (4163146063 : ℕ)^4409*20000000000000^3385 ≤ 6387375915371^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163146063 10000000000 6387375915371 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155145831/500000000 : ℝ)^4409 ≤ (21778347951589/100000000000000 : ℝ)^3385 := by
    have hnat : (155145831 : ℕ)^4409*100000000000000^3385 ≤ 21778347951589^3385*500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155145831 500000000 21778347951589 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5535296213/10000000000 : ℝ)^4409 ≤ (9256954490921/20000000000000 : ℝ)^3385 := by
    have hnat : (5535296213 : ℕ)^4409*20000000000000^3385 ≤ 9256954490921^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535296213 10000000000 9256954490921 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163146063/10000000000 : ℝ), (155145831/500000000 : ℝ), (5535296213/10000000000 : ℝ)] ![(6387375915371/20000000000000 : ℝ), (21778347951589/100000000000000 : ℝ), (9256954490921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163146063/10000000000 : ℝ)|^4409 ≤ (6387375915371/20000000000000 : ℝ)^3385
        have hw : |(4163146063/10000000000 : ℝ)|=(4163146063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155145831/500000000 : ℝ)|^4409 ≤ (21778347951589/100000000000000 : ℝ)^3385
        have hw : |(155145831/500000000 : ℝ)|=(155145831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5535296213/10000000000 : ℝ)|^4409 ≤ (9256954490921/20000000000000 : ℝ)^3385
        have hw : |(5535296213/10000000000 : ℝ)|=(5535296213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s0_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-437867/2500000 : ℝ)*x 0 + (2432151643/5000000000 : ℝ)*x 1 + (2961219807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437867/2500000 : ℝ)^4409 ≤ (10340058427959/100000000000000 : ℝ)^3385 := by
    have hnat : (437867 : ℕ)^4409*100000000000000^3385 ≤ 10340058427959^3385*2500000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437867 2500000 10340058427959 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2432151643/5000000000 : ℝ)^4409 ≤ (39114782794063/100000000000000 : ℝ)^3385 := by
    have hnat : (2432151643 : ℕ)^4409*100000000000000^3385 ≤ 39114782794063^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432151643 5000000000 39114782794063 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2961219807/5000000000 : ℝ)^4409 ≤ (50545158759779/100000000000000 : ℝ)^3385 := by
    have hnat : (2961219807 : ℕ)^4409*100000000000000^3385 ≤ 50545158759779^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961219807 5000000000 50545158759779 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437867/2500000 : ℝ), (2432151643/5000000000 : ℝ), (2961219807/5000000000 : ℝ)] ![(10340058427959/100000000000000 : ℝ), (39114782794063/100000000000000 : ℝ), (50545158759779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437867/2500000 : ℝ)|^4409 ≤ (10340058427959/100000000000000 : ℝ)^3385
        have hw : |(-437867/2500000 : ℝ)|=(437867/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2432151643/5000000000 : ℝ)|^4409 ≤ (39114782794063/100000000000000 : ℝ)^3385
        have hw : |(2432151643/5000000000 : ℝ)|=(2432151643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2961219807/5000000000 : ℝ)|^4409 ≤ (50545158759779/100000000000000 : ℝ)^3385
        have hw : |(2961219807/5000000000 : ℝ)|=(2961219807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s0_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162035649/312500000 : ℝ)*x 0 + (-161319327/1250000000 : ℝ)*x 1 + (5922439683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162035649/312500000 : ℝ)^4409 ≤ (42508174825477/100000000000000 : ℝ)^3385 := by
    have hnat : (162035649 : ℕ)^4409*100000000000000^3385 ≤ 42508174825477^3385*312500000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162035649 312500000 42508174825477 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161319327/1250000000 : ℝ)^4409 ≤ (347333281401/5000000000000 : ℝ)^3385 := by
    have hnat : (161319327 : ℕ)^4409*5000000000000^3385 ≤ 347333281401^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161319327 1250000000 347333281401 5000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5922439683/10000000000 : ℝ)^4409 ≤ (12636289881701/25000000000000 : ℝ)^3385 := by
    have hnat : (5922439683 : ℕ)^4409*25000000000000^3385 ≤ 12636289881701^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5922439683 10000000000 12636289881701 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162035649/312500000 : ℝ), (-161319327/1250000000 : ℝ), (5922439683/10000000000 : ℝ)] ![(42508174825477/100000000000000 : ℝ), (347333281401/5000000000000 : ℝ), (12636289881701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162035649/312500000 : ℝ)|^4409 ≤ (42508174825477/100000000000000 : ℝ)^3385
        have hw : |(162035649/312500000 : ℝ)|=(162035649/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161319327/1250000000 : ℝ)|^4409 ≤ (347333281401/5000000000000 : ℝ)^3385
        have hw : |(-161319327/1250000000 : ℝ)|=(161319327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5922439683/10000000000 : ℝ)|^4409 ≤ (12636289881701/25000000000000 : ℝ)^3385
        have hw : |(5922439683/10000000000 : ℝ)|=(5922439683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s0_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185140799/10000000000 : ℝ)*x 0 + (740304941/1250000000 : ℝ)*x 1 + (-258110963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185140799/10000000000 : ℝ)^4409 ≤ (42508175156497/100000000000000 : ℝ)^3385 := by
    have hnat : (5185140799 : ℕ)^4409*100000000000000^3385 ≤ 42508175156497^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185140799 10000000000 42508175156497 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740304941/1250000000 : ℝ)^4409 ≤ (50545157803777/100000000000000 : ℝ)^3385 := by
    have hnat : (740304941 : ℕ)^4409*100000000000000^3385 ≤ 50545157803777^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740304941 1250000000 50545157803777 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258110963/2000000000 : ℝ)^4409 ≤ (3473333511607/50000000000000 : ℝ)^3385 := by
    have hnat : (258110963 : ℕ)^4409*50000000000000^3385 ≤ 3473333511607^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258110963 2000000000 3473333511607 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185140799/10000000000 : ℝ), (740304941/1250000000 : ℝ), (-258110963/2000000000 : ℝ)] ![(42508175156497/100000000000000 : ℝ), (50545157803777/100000000000000 : ℝ), (3473333511607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185140799/10000000000 : ℝ)|^4409 ≤ (42508175156497/100000000000000 : ℝ)^3385
        have hw : |(5185140799/10000000000 : ℝ)|=(5185140799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740304941/1250000000 : ℝ)|^4409 ≤ (50545157803777/100000000000000 : ℝ)^3385
        have hw : |(740304941/1250000000 : ℝ)|=(740304941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258110963/2000000000 : ℝ)|^4409 ≤ (3473333511607/50000000000000 : ℝ)^3385
        have hw : |(-258110963/2000000000 : ℝ)|=(258110963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s0_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4171693193/10000000000 : ℝ)*x 0 + (5473159323/10000000000 : ℝ)*x 1 + (3167272157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4171693193/10000000000 : ℝ)^4409 ≤ (16011154487427/50000000000000 : ℝ)^3385 := by
    have hnat : (4171693193 : ℕ)^4409*50000000000000^3385 ≤ 16011154487427^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171693193 10000000000 16011154487427 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473159323/10000000000 : ℝ)^4409 ≤ (45609174634907/100000000000000 : ℝ)^3385 := by
    have hnat : (5473159323 : ℕ)^4409*100000000000000^3385 ≤ 45609174634907^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473159323 10000000000 45609174634907 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167272157/10000000000 : ℝ)^4409 ≤ (22368516372779/100000000000000 : ℝ)^3385 := by
    have hnat : (3167272157 : ℕ)^4409*100000000000000^3385 ≤ 22368516372779^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167272157 10000000000 22368516372779 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4171693193/10000000000 : ℝ), (5473159323/10000000000 : ℝ), (3167272157/10000000000 : ℝ)] ![(16011154487427/50000000000000 : ℝ), (45609174634907/100000000000000 : ℝ), (22368516372779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4171693193/10000000000 : ℝ)|^4409 ≤ (16011154487427/50000000000000 : ℝ)^3385
        have hw : |(4171693193/10000000000 : ℝ)|=(4171693193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473159323/10000000000 : ℝ)|^4409 ≤ (45609174634907/100000000000000 : ℝ)^3385
        have hw : |(5473159323/10000000000 : ℝ)|=(5473159323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167272157/10000000000 : ℝ)|^4409 ≤ (22368516372779/100000000000000 : ℝ)^3385
        have hw : |(3167272157/10000000000 : ℝ)|=(3167272157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (547/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26121/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (551/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^551 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^551*1^128 ≤ 0^128*1^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (551/128 : ℝ) ≤ (193638905363950987/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^551 ≤ (193638905363950987/10000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^551*10000000000000000000^128 ≤ 193638905363950987^128*5^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 193638905363950987 10000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (193638905363950987/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^551 := by
      have hnat : (1 : ℕ)^128*1^551 ≤ 1^551*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10193638905363950987/10000000000000000000 : ℝ) ≤ (5022326340136907/5000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (10193638905363950987/10000000000000000000 : ℝ)^128 ≤ (5022326340136907/5000000000000000 : ℝ)^551 := by
      have hnat : (10193638905363950987 : ℕ)^128*5000000000000000^551 ≤ 5022326340136907^551*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10193638905363950987 10000000000000000000 5022326340136907 5000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5022326340136907/5000000000000000 : ℝ)) (X := (10193638905363950987/10000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (5193638905363950987/5000000000000000000 : ℝ) ≤ (2522326340136907/2500000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (5193638905363950987/5000000000000000000 : ℝ)^128 ≤ (2522326340136907/2500000000000000 : ℝ)^551 := by
      have hnat : (5193638905363950987 : ℕ)^128*2500000000000000^551 ≤ 2522326340136907^551*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5193638905363950987 5000000000000000000 2522326340136907 2500000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522326340136907/2500000000000000 : ℝ)) (X := (5193638905363950987/5000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(22326340136907/2000000000000000 : ℝ)*(0 : ℝ))^(551/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(22326340136907/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(193638905363950987/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(22326340136907/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(551/128 : ℝ) := by
    rw [show (1 : ℝ)+(22326340136907/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5022326340136907/5000000000000000 : ℝ) by norm_num, show 1+(193638905363950987/10000000000000000000 : ℝ)+(0 : ℝ)=(10193638905363950987/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(193638905363950987/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(22326340136907/2000000000000000 : ℝ)*(2/5 : ℝ))^(551/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(22326340136907/2000000000000000 : ℝ)*(2/5 : ℝ)=(2522326340136907/2500000000000000 : ℝ) by norm_num, show 1+2*(193638905363950987/10000000000000000000 : ℝ)=(5193638905363950987/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(22326340136907/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22326340136907/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(22326340136907/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22326340136907/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(22326340136907/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22326340136907/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-873772719/5000000000 : ℝ)*X 0 0+(5951971267/10000000000 : ℝ)*X 0 1+(2417894907/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2744938831/5000000000 : ℝ)*X 1 0+(-297150543/1250000000 : ℝ)*X 1 1+(604473711/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((548987753/1000000000 : ℝ)*X 2 0+(4835789647/10000000000 : ℝ)*X 2 1+(-594301141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4163146063/10000000000 : ℝ)*X 0 0+(155145831/500000000 : ℝ)*X 0 1+(5535296213/10000000000 : ℝ)*X 0 2+(4163146063/10000000000 : ℝ)*X 1 0+(155145831/500000000 : ℝ)*X 1 1+(5535296213/10000000000 : ℝ)*X 1 2+(4163146063/10000000000 : ℝ)*X 2 0+(155145831/500000000 : ℝ)*X 2 1+(5535296213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-437867/2500000 : ℝ)*X 0 0+(2432151643/5000000000 : ℝ)*X 0 1+(2961219807/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((162035649/312500000 : ℝ)*X 1 0+(-161319327/1250000000 : ℝ)*X 1 1+(5922439683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185140799/10000000000 : ℝ)*X 2 0+(740304941/1250000000 : ℝ)*X 2 1+(-258110963/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4171693193/10000000000 : ℝ)*X 0 0+(5473159323/10000000000 : ℝ)*X 0 1+(3167272157/10000000000 : ℝ)*X 0 2+(4171693193/10000000000 : ℝ)*X 1 0+(5473159323/10000000000 : ℝ)*X 1 1+(3167272157/10000000000 : ℝ)*X 1 2+(4171693193/10000000000 : ℝ)*X 2 0+(5473159323/10000000000 : ℝ)*X 2 1+(3167272157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53578890906383796159891/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70511221/50000000000000 : ℝ)*(base1) + (48354733/5000000000000 : ℝ)*(base19) + (37822121/4000000000000 : ℝ)*(base23) + (32833427/25000000000000 : ℝ)*(upper3) + (32642809/50000000000000 : ℝ)*(upper5) + (326760006460229/50000000000000 : ℝ)*(major0) + (326760006460229/50000000000000 : ℝ)*(major1) + (326760006460229/50000000000000 : ℝ)*(major2) + (17918293126749/2000000000000 : ℝ)*(sp0) + (895916204184293/100000000000000 : ℝ)*(sp1) + (111989528215741/12500000000000 : ℝ)*(sp2) + (102780296374881/25000000000000 : ℝ)*(sp3) + (331995493/12500000000000 : ℝ)*(sp4) + (27703259/2000000000000 : ℝ)*(sp7) + (102780677921229/25000000000000 : ℝ)*(f.failure) + (895917171278953/100000000000000 : ℝ)*(f.sum) + (5360102528297/50000000000000000000000000000 : ℝ)*base66 + (1017222224171703/100000000000000000000000000000 : ℝ)*base67 + (530186542771703/100000000000000000000000000000 : ℝ)*base69 + (320162677771703/100000000000000000000000000000 : ℝ)*base71 + (131726163671703/50000000000000000000000000000 : ℝ)*base73 + (531890675971703/100000000000000000000000000000 : ℝ)*base75 + (420799190371703/100000000000000000000000000000 : ℝ)*base77 + (464312395971703/100000000000000000000000000000 : ℝ)*base79 + (6398792071703/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (142909/1250000000000000000000 : ℝ)*base89 + (142909/1250000000000000000000 : ℝ)*base91 + (142909/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24324575387253696540549/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1778304443/100000000000000 : ℝ)*(base19) + (1793931773/100000000000000 : ℝ)*(base23) + (81078669/50000000000000 : ℝ)*(base32) + (267521137/100000000000000 : ℝ)*(upper3) + (164252483/100000000000000 : ℝ)*(upper5) + (43085301982369/6250000000000 : ℝ)*(major0) + (43085301982369/6250000000000 : ℝ)*(major1) + (43085301982369/6250000000000 : ℝ)*(major2) + (4271054361/100000000000000 : ℝ)*(sp1) + (2220410103/50000000000000 : ℝ)*(sp2) + (118132135728829/12500000000000 : ℝ)*(sp4) + (236262759117957/25000000000000 : ℝ)*(sp5) + (945050851078653/100000000000000 : ℝ)*(sp6) + (13552254874553/3125000000000 : ℝ)*(sp7) + (216836159071517/50000000000000 : ℝ)*(f.failure) + (118132135728829/12500000000000 : ℝ)*(f.sum) + (6516985607317/6250000000000000000000000000 : ℝ)*base66 + (78811703192683/12500000000000000000000000000 : ℝ)*base67 + (112293568807317/12500000000000000000000000000 : ℝ)*base70 + (52467479982317/12500000000000000000000000000 : ℝ)*base72 + (36810825342683/6250000000000000000000000000 : ℝ)*base73 + (77525116857317/12500000000000000000000000000 : ℝ)*base76 + (60339567994817/12500000000000000000000000000 : ℝ)*base78 + (15682374267683/12500000000000000000000000000 : ℝ)*base79 + (30334426638567/6250000000000000000000000000 : ℝ)*base82 + (4510157/2500000000000000000000 : ℝ)*base89 + (4510157/2500000000000000000000 : ℝ)*base91 + (4510157/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1449_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (547/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1449_s1_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917072693/10000000000 : ℝ)*x 0 + (5597320153/10000000000 : ℝ)*x 1 + (635215763/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917072693/10000000000 : ℝ)^4409 ≤ (2326262931777/20000000000000 : ℝ)^3385 := by
    have hnat : (1917072693 : ℕ)^4409*20000000000000^3385 ≤ 2326262931777^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917072693 10000000000 2326262931777 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5597320153/10000000000 : ℝ)^4409 ≤ (46961434124737/100000000000000 : ℝ)^3385 := by
    have hnat : (5597320153 : ℕ)^4409*100000000000000^3385 ≤ 46961434124737^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597320153 10000000000 46961434124737 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635215763/1250000000 : ℝ)^4409 ≤ (517590639937/1250000000000 : ℝ)^3385 := by
    have hnat : (635215763 : ℕ)^4409*1250000000000^3385 ≤ 517590639937^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635215763 1250000000 517590639937 1250000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917072693/10000000000 : ℝ), (5597320153/10000000000 : ℝ), (635215763/1250000000 : ℝ)] ![(2326262931777/20000000000000 : ℝ), (46961434124737/100000000000000 : ℝ), (517590639937/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917072693/10000000000 : ℝ)|^4409 ≤ (2326262931777/20000000000000 : ℝ)^3385
        have hw : |(-1917072693/10000000000 : ℝ)|=(1917072693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5597320153/10000000000 : ℝ)|^4409 ≤ (46961434124737/100000000000000 : ℝ)^3385
        have hw : |(5597320153/10000000000 : ℝ)|=(5597320153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635215763/1250000000 : ℝ)|^4409 ≤ (517590639937/1250000000000 : ℝ)^3385
        have hw : |(635215763/1250000000 : ℝ)|=(635215763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s1_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394815561/10000000000 : ℝ)*x 0 + (-54746771/250000000 : ℝ)*x 1 + (2540862667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394815561/10000000000 : ℝ)^4409 ≤ (44760667486261/100000000000000 : ℝ)^3385 := by
    have hnat : (5394815561 : ℕ)^4409*100000000000000^3385 ≤ 44760667486261^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394815561 10000000000 44760667486261 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54746771/250000000 : ℝ)^4409 ≤ (691604474477/5000000000000 : ℝ)^3385 := by
    have hnat : (54746771 : ℕ)^4409*5000000000000^3385 ≤ 691604474477^3385*250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54746771 250000000 691604474477 5000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540862667/5000000000 : ℝ)^4409 ≤ (5175905377849/12500000000000 : ℝ)^3385 := by
    have hnat : (2540862667 : ℕ)^4409*12500000000000^3385 ≤ 5175905377849^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540862667 5000000000 5175905377849 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394815561/10000000000 : ℝ), (-54746771/250000000 : ℝ), (2540862667/5000000000 : ℝ)] ![(44760667486261/100000000000000 : ℝ), (691604474477/5000000000000 : ℝ), (5175905377849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394815561/10000000000 : ℝ)|^4409 ≤ (44760667486261/100000000000000 : ℝ)^3385
        have hw : |(5394815561/10000000000 : ℝ)|=(5394815561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54746771/250000000 : ℝ)|^4409 ≤ (691604474477/5000000000000 : ℝ)^3385
        have hw : |(-54746771/250000000 : ℝ)|=(54746771/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540862667/5000000000 : ℝ)|^4409 ≤ (5175905377849/12500000000000 : ℝ)^3385
        have hw : |(2540862667/5000000000 : ℝ)|=(2540862667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s1_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674351867/1250000000 : ℝ)*x 0 + (5081725969/10000000000 : ℝ)*x 1 + (-54746771/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674351867/1250000000 : ℝ)^4409 ≤ (5595082591493/12500000000000 : ℝ)^3385 := by
    have hnat : (674351867 : ℕ)^4409*12500000000000^3385 ≤ 5595082591493^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674351867 1250000000 5595082591493 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081725969/10000000000 : ℝ)^4409 ≤ (41407249762177/100000000000000 : ℝ)^3385 := by
    have hnat : (5081725969 : ℕ)^4409*100000000000000^3385 ≤ 41407249762177^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081725969 10000000000 41407249762177 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54746771/250000000 : ℝ)^4409 ≤ (691604474477/5000000000000 : ℝ)^3385 := by
    have hnat : (54746771 : ℕ)^4409*5000000000000^3385 ≤ 691604474477^3385*250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54746771 250000000 691604474477 5000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674351867/1250000000 : ℝ), (5081725969/10000000000 : ℝ), (-54746771/250000000 : ℝ)] ![(5595082591493/12500000000000 : ℝ), (41407249762177/100000000000000 : ℝ), (691604474477/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674351867/1250000000 : ℝ)|^4409 ≤ (5595082591493/12500000000000 : ℝ)^3385
        have hw : |(674351867/1250000000 : ℝ)|=(674351867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081725969/10000000000 : ℝ)|^4409 ≤ (41407249762177/100000000000000 : ℝ)^3385
        have hw : |(5081725969/10000000000 : ℝ)|=(5081725969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54746771/250000000 : ℝ)|^4409 ≤ (691604474477/5000000000000 : ℝ)^3385
        have hw : |(-54746771/250000000 : ℝ)|=(54746771/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s1_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4272997623/10000000000 : ℝ)*x 0 + (3743895187/10000000000 : ℝ)*x 1 + (4867477469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272997623/10000000000 : ℝ)^4409 ≤ (16519435086353/50000000000000 : ℝ)^3385 := by
    have hnat : (4272997623 : ℕ)^4409*50000000000000^3385 ≤ 16519435086353^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272997623 10000000000 16519435086353 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3743895187/10000000000 : ℝ)^4409 ≤ (27813098174759/100000000000000 : ℝ)^3385 := by
    have hnat : (3743895187 : ℕ)^4409*100000000000000^3385 ≤ 27813098174759^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743895187 10000000000 27813098174759 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4867477469/10000000000 : ℝ)^4409 ≤ (19574015817941/50000000000000 : ℝ)^3385 := by
    have hnat : (4867477469 : ℕ)^4409*50000000000000^3385 ≤ 19574015817941^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867477469 10000000000 19574015817941 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272997623/10000000000 : ℝ), (3743895187/10000000000 : ℝ), (4867477469/10000000000 : ℝ)] ![(16519435086353/50000000000000 : ℝ), (27813098174759/100000000000000 : ℝ), (19574015817941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272997623/10000000000 : ℝ)|^4409 ≤ (16519435086353/50000000000000 : ℝ)^3385
        have hw : |(4272997623/10000000000 : ℝ)|=(4272997623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3743895187/10000000000 : ℝ)|^4409 ≤ (27813098174759/100000000000000 : ℝ)^3385
        have hw : |(3743895187/10000000000 : ℝ)|=(3743895187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4867477469/10000000000 : ℝ)|^4409 ≤ (19574015817941/50000000000000 : ℝ)^3385
        have hw : |(4867477469/10000000000 : ℝ)|=(4867477469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s1_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-47936107/250000000 : ℝ)*x 0 + (5087676859/10000000000 : ℝ)*x 1 + (5591270109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47936107/250000000 : ℝ)^4409 ≤ (363570351861/3125000000000 : ℝ)^3385 := by
    have hnat : (47936107 : ℕ)^4409*3125000000000^3385 ≤ 363570351861^3385*250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47936107 250000000 363570351861 3125000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5087676859/10000000000 : ℝ)^4409 ≤ (20735209481991/50000000000000 : ℝ)^3385 := by
    have hnat : (5087676859 : ℕ)^4409*50000000000000^3385 ≤ 20735209481991^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087676859 10000000000 20735209481991 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591270109/10000000000 : ℝ)^4409 ≤ (2344766488003/5000000000000 : ℝ)^3385 := by
    have hnat : (5591270109 : ℕ)^4409*5000000000000^3385 ≤ 2344766488003^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591270109 10000000000 2344766488003 5000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47936107/250000000 : ℝ), (5087676859/10000000000 : ℝ), (5591270109/10000000000 : ℝ)] ![(363570351861/3125000000000 : ℝ), (20735209481991/50000000000000 : ℝ), (2344766488003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47936107/250000000 : ℝ)|^4409 ≤ (363570351861/3125000000000 : ℝ)^3385
        have hw : |(-47936107/250000000 : ℝ)|=(47936107/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5087676859/10000000000 : ℝ)|^4409 ≤ (20735209481991/50000000000000 : ℝ)^3385
        have hw : |(5087676859/10000000000 : ℝ)|=(5087676859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5591270109/10000000000 : ℝ)|^4409 ≤ (2344766488003/5000000000000 : ℝ)^3385
        have hw : |(5591270109/10000000000 : ℝ)|=(5591270109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s1_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314976739/2500000000 : ℝ)*x 0 + (-1680325989/10000000000 : ℝ)*x 1 + (5591270139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314976739/2500000000 : ℝ)^4409 ≤ (43308269882363/100000000000000 : ℝ)^3385 := by
    have hnat : (1314976739 : ℕ)^4409*100000000000000^3385 ≤ 43308269882363^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314976739 2500000000 43308269882363 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1680325989/10000000000 : ℝ)^4409 ≤ (1959280003553/20000000000000 : ℝ)^3385 := by
    have hnat : (1680325989 : ℕ)^4409*20000000000000^3385 ≤ 1959280003553^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680325989 10000000000 1959280003553 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591270139/10000000000 : ℝ)^4409 ≤ (9379066017559/20000000000000 : ℝ)^3385 := by
    have hnat : (5591270139 : ℕ)^4409*20000000000000^3385 ≤ 9379066017559^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591270139 10000000000 9379066017559 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314976739/2500000000 : ℝ), (-1680325989/10000000000 : ℝ), (5591270139/10000000000 : ℝ)] ![(43308269882363/100000000000000 : ℝ), (1959280003553/20000000000000 : ℝ), (9379066017559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314976739/2500000000 : ℝ)|^4409 ≤ (43308269882363/100000000000000 : ℝ)^3385
        have hw : |(1314976739/2500000000 : ℝ)|=(1314976739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1680325989/10000000000 : ℝ)|^4409 ≤ (1959280003553/20000000000000 : ℝ)^3385
        have hw : |(-1680325989/10000000000 : ℝ)|=(1680325989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5591270139/10000000000 : ℝ)|^4409 ≤ (9379066017559/20000000000000 : ℝ)^3385
        have hw : |(5591270139/10000000000 : ℝ)|=(5591270139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s1_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259906861/10000000000 : ℝ)*x 0 + (5591270099/10000000000 : ℝ)*x 1 + (-84016309/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259906861/10000000000 : ℝ)^4409 ≤ (21654134431771/50000000000000 : ℝ)^3385 := by
    have hnat : (5259906861 : ℕ)^4409*50000000000000^3385 ≤ 21654134431771^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259906861 10000000000 21654134431771 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591270099/10000000000 : ℝ)^4409 ≤ (366369762897/781250000000 : ℝ)^3385 := by
    have hnat : (5591270099 : ℕ)^4409*781250000000^3385 ≤ 366369762897^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591270099 10000000000 366369762897 781250000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84016309/500000000 : ℝ)^4409 ≤ (1959280293633/20000000000000 : ℝ)^3385 := by
    have hnat : (84016309 : ℕ)^4409*20000000000000^3385 ≤ 1959280293633^3385*500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84016309 500000000 1959280293633 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259906861/10000000000 : ℝ), (5591270099/10000000000 : ℝ), (-84016309/500000000 : ℝ)] ![(21654134431771/50000000000000 : ℝ), (366369762897/781250000000 : ℝ), (1959280293633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259906861/10000000000 : ℝ)|^4409 ≤ (21654134431771/50000000000000 : ℝ)^3385
        have hw : |(5259906861/10000000000 : ℝ)|=(5259906861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591270099/10000000000 : ℝ)|^4409 ≤ (366369762897/781250000000 : ℝ)^3385
        have hw : |(5591270099/10000000000 : ℝ)|=(5591270099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84016309/500000000 : ℝ)|^4409 ≤ (1959280293633/20000000000000 : ℝ)^3385
        have hw : |(-84016309/500000000 : ℝ)|=(84016309/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s1_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10684517/25000000 : ℝ)*x 0 + (2427254653/5000000000 : ℝ)*x 1 + (3757080023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10684517/25000000 : ℝ)^4409 ≤ (6609403930663/20000000000000 : ℝ)^3385 := by
    have hnat : (10684517 : ℕ)^4409*20000000000000^3385 ≤ 6609403930663^3385*25000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10684517 25000000 6609403930663 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2427254653/5000000000 : ℝ)^4409 ≤ (390122344687/1000000000000 : ℝ)^3385 := by
    have hnat : (2427254653 : ℕ)^4409*1000000000000^3385 ≤ 390122344687^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427254653 5000000000 390122344687 1000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3757080023/10000000000 : ℝ)^4409 ≤ (13970372928291/50000000000000 : ℝ)^3385 := by
    have hnat : (3757080023 : ℕ)^4409*50000000000000^3385 ≤ 13970372928291^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3757080023 10000000000 13970372928291 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10684517/25000000 : ℝ), (2427254653/5000000000 : ℝ), (3757080023/10000000000 : ℝ)] ![(6609403930663/20000000000000 : ℝ), (390122344687/1000000000000 : ℝ), (13970372928291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10684517/25000000 : ℝ)|^4409 ≤ (6609403930663/20000000000000 : ℝ)^3385
        have hw : |(10684517/25000000 : ℝ)|=(10684517/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2427254653/5000000000 : ℝ)|^4409 ≤ (390122344687/1000000000000 : ℝ)^3385
        have hw : |(2427254653/5000000000 : ℝ)|=(2427254653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3757080023/10000000000 : ℝ)|^4409 ≤ (13970372928291/50000000000000 : ℝ)^3385
        have hw : |(3757080023/10000000000 : ℝ)|=(3757080023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (3907/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3743/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (547/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (547/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (547/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (547/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (547/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (547/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (547/25000 : ℝ) ^ (551/128 : ℝ) ≤ (7151916539517/100000000000000000000 : ℝ) := by
    have hpowers : (547/25000 : ℝ)^551 ≤ (7151916539517/100000000000000000000 : ℝ)^128 := by
      have hnat : (547 : ℕ)^551*100000000000000000000^128 ≤ 7151916539517^128*25000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        547 25000 7151916539517 100000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (547/25000 : ℝ)) (X := (7151916539517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (26121/100000 : ℝ) ^ (551/128 : ℝ) ≤ (154629830736098629/50000000000000000000 : ℝ) := by
    have hpowers : (26121/100000 : ℝ)^551 ≤ (154629830736098629/50000000000000000000 : ℝ)^128 := by
      have hnat : (26121 : ℕ)^551*50000000000000000000^128 ≤ 154629830736098629^128*100000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26121 100000 154629830736098629 50000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26121/100000 : ℝ)) (X := (154629830736098629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000007151916539517/50000000000000000000 : ℝ) ≤ (5000000166142517/5000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50000007151916539517/50000000000000000000 : ℝ)^128 ≤ (5000000166142517/5000000000000000 : ℝ)^551 := by
      have hnat : (50000007151916539517 : ℕ)^128*5000000000000000^551 ≤ 5000000166142517^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000007151916539517 50000000000000000000 5000000166142517 5000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000166142517/5000000000000000 : ℝ)) (X := (50000007151916539517/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (4012370672535549471/4000000000000000000 : ℝ) ≤ (1250896988301439/1250000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (4012370672535549471/4000000000000000000 : ℝ)^128 ≤ (1250896988301439/1250000000000000 : ℝ)^551 := by
      have hnat : (4012370672535549471 : ℕ)^128*1250000000000000^551 ≤ 1250896988301439^551*4000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4012370672535549471 4000000000000000000 1250896988301439 1250000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250896988301439/1250000000000000 : ℝ)) (X := (4012370672535549471/4000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25154629830736098629/25000000000000000000 : ℝ) ≤ (1001435148053799/1000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (25154629830736098629/25000000000000000000 : ℝ)^128 ≤ (1001435148053799/1000000000000000 : ℝ)^551 := by
      have hnat : (25154629830736098629 : ℕ)^128*1000000000000000^551 ≤ 1001435148053799^551*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25154629830736098629 25000000000000000000 1001435148053799 1000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001435148053799/1000000000000000 : ℝ)) (X := (25154629830736098629/25000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7151916539517/100000000000000000000 : ℝ) ≤ ((119649303820100125497/119665000000000000000 : ℝ)+2*(3587787063239/1196650000000000 : ℝ)*(547/25000 : ℝ))^(551/128 : ℝ) := by
    rw [show (119649303820100125497/119665000000000000000 : ℝ)+2*(3587787063239/1196650000000000 : ℝ)*(547/25000 : ℝ)=(5000000166142517/5000000000000000 : ℝ) by norm_num, show 1+2*(7151916539517/100000000000000000000 : ℝ)=(50000007151916539517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(154629830736098629/50000000000000000000 : ℝ)+(7151916539517/100000000000000000000 : ℝ) ≤ ((119649303820100125497/119665000000000000000 : ℝ)+(3587787063239/1196650000000000 : ℝ)*((26121/100000 : ℝ)+(547/25000 : ℝ)))^(551/128 : ℝ) := by
    rw [show (119649303820100125497/119665000000000000000 : ℝ)+(3587787063239/1196650000000000 : ℝ)*((26121/100000 : ℝ)+(547/25000 : ℝ))=(1250896988301439/1250000000000000 : ℝ) by norm_num, show 1+(154629830736098629/50000000000000000000 : ℝ)+(7151916539517/100000000000000000000 : ℝ)=(4012370672535549471/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(154629830736098629/50000000000000000000 : ℝ) ≤ ((119649303820100125497/119665000000000000000 : ℝ)+2*(3587787063239/1196650000000000 : ℝ)*(26121/100000 : ℝ))^(551/128 : ℝ) := by
    rw [show (119649303820100125497/119665000000000000000 : ℝ)+2*(3587787063239/1196650000000000 : ℝ)*(26121/100000 : ℝ)=(1001435148053799/1000000000000000 : ℝ) by norm_num, show 1+2*(154629830736098629/50000000000000000000 : ℝ)=(25154629830736098629/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (119649303820100125497/119665000000000000000 : ℝ)*(X 1 0+X 2 0)+(3587787063239/1196650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (547/25000 : ℝ)) (hi := (26121/100000 : ℝ)) (c := (119649303820100125497/119665000000000000000 : ℝ)) (alpha := (3587787063239/1196650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (119649303820100125497/119665000000000000000 : ℝ)*(X 0 1+X 2 1)+(3587787063239/1196650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (547/25000 : ℝ)) (hi := (26121/100000 : ℝ)) (c := (119649303820100125497/119665000000000000000 : ℝ)) (alpha := (3587787063239/1196650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (119649303820100125497/119665000000000000000 : ℝ)*(X 0 2+X 1 2)+(3587787063239/1196650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (547/25000 : ℝ)) (hi := (26121/100000 : ℝ)) (c := (119649303820100125497/119665000000000000000 : ℝ)) (alpha := (3587787063239/1196650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1917072693/10000000000 : ℝ)*X 0 0+(5597320153/10000000000 : ℝ)*X 0 1+(635215763/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5394815561/10000000000 : ℝ)*X 1 0+(-54746771/250000000 : ℝ)*X 1 1+(2540862667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((674351867/1250000000 : ℝ)*X 2 0+(5081725969/10000000000 : ℝ)*X 2 1+(-54746771/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4272997623/10000000000 : ℝ)*X 0 0+(3743895187/10000000000 : ℝ)*X 0 1+(4867477469/10000000000 : ℝ)*X 0 2+(4272997623/10000000000 : ℝ)*X 1 0+(3743895187/10000000000 : ℝ)*X 1 1+(4867477469/10000000000 : ℝ)*X 1 2+(4272997623/10000000000 : ℝ)*X 2 0+(3743895187/10000000000 : ℝ)*X 2 1+(4867477469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-47936107/250000000 : ℝ)*X 0 0+(5087676859/10000000000 : ℝ)*X 0 1+(5591270109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314976739/2500000000 : ℝ)*X 1 0+(-1680325989/10000000000 : ℝ)*X 1 1+(5591270139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259906861/10000000000 : ℝ)*X 2 0+(5591270099/10000000000 : ℝ)*X 2 1+(-84016309/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((10684517/25000000 : ℝ)*X 0 0+(2427254653/5000000000 : ℝ)*X 0 1+(3757080023/10000000000 : ℝ)*X 0 2+(10684517/25000000 : ℝ)*X 1 0+(2427254653/5000000000 : ℝ)*X 1 1+(3757080023/10000000000 : ℝ)*X 1 2+(10684517/25000000 : ℝ)*X 2 0+(2427254653/5000000000 : ℝ)*X 2 1+(3757080023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1157250565831638124624848717/230125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113400737/100000000000000 : ℝ)*(base1) + (133029799/12500000000000 : ℝ)*(base19) + (1679083/200000000000 : ℝ)*(base23) + (2266131/1562500000000 : ℝ)*(upper3) + (95548127/100000000000000 : ℝ)*(upper5) + (707383362789377/50000000000000 : ℝ)*(major0) + (707383362789377/50000000000000 : ℝ)*(major1) + (707383362789377/50000000000000 : ℝ)*(major2) + (48487871292717/2500000000000 : ℝ)*(sp0) + (1939517038239177/100000000000000 : ℝ)*(sp1) + (1939517262936069/100000000000000 : ℝ)*(sp2) + (890012742805343/100000000000000 : ℝ)*(sp3) + (1682084813/50000000000000 : ℝ)*(sp4) + (1162423741/50000000000000 : ℝ)*(sp7) + (890015181053561/100000000000000 : ℝ)*(f.failure) + (1939518102477569/100000000000000 : ℝ)*(f.sum) + (309623794603973/119665000000000000000000000000 : ℝ)*base66 + (45778197039294004631/5983250000000000000000000000000000 : ℝ)*base68 + (54410809197919004631/5983250000000000000000000000000000 : ℝ)*base70 + (27564263689795754631/5983250000000000000000000000000000 : ℝ)*base72 + (656016895472333/119665000000000000000000000000 : ℝ)*base74 + (11889755102672004631/5983250000000000000000000000000000 : ℝ)*base76 + (28371363949238504631/5983250000000000000000000000000000 : ℝ)*base78 + (21989770829586754631/5983250000000000000000000000000000 : ℝ)*base80 + (594352089778933/119665000000000000000000000000 : ℝ)*base82 + (25048681/5000000000000000000000 : ℝ)*base89 + (25048681/5000000000000000000000 : ℝ)*base91 + (25048681/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (750718727182722190428171939/213687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3279707/25000000000000 : ℝ)*(base1) + (215278013/25000000000000 : ℝ)*(base19) + (813143929/100000000000000 : ℝ)*(base23) + (48887667/50000000000000 : ℝ)*(upper3) + (61244147/100000000000000 : ℝ)*(upper5) + (362118703091701/25000000000000 : ℝ)*(major0) + (362118703091701/25000000000000 : ℝ)*(major1) + (362118703091701/25000000000000 : ℝ)*(major2) + (275233699/5000000000000 : ℝ)*(sp1) + (1006558281/20000000000000 : ℝ)*(sp2) + (496432232335833/25000000000000 : ℝ)*(sp4) + (248215318804809/12500000000000 : ℝ)*(sp5) + (198572307028917/10000000000000 : ℝ)*(sp6) + (911220578284883/100000000000000 : ℝ)*(sp7) + (911220591403711/100000000000000 : ℝ)*(f.failure) + (248216114528063/12500000000000 : ℝ)*(f.sum) + (36234929761089/14958125000000000000000000000 : ℝ)*base65 + (38276495534189149603/2991625000000000000000000000000000 : ℝ)*base68 + (2287187283759524603/2991625000000000000000000000000000 : ℝ)*base70 + (2908436851846399603/2991625000000000000000000000000000 : ℝ)*base72 + (243000195192519/59832500000000000000000000000 : ℝ)*base74 + (14902671683687024603/2991625000000000000000000000000000 : ℝ)*base76 + (23086368411928149603/2991625000000000000000000000000000 : ℝ)*base78 + (22033976433210524603/2991625000000000000000000000000000 : ℝ)*base80 + (507008221711827/119665000000000000000000000000 : ℝ)*base81 + (29386831/5000000000000000000000 : ℝ)*base89 + (29386831/5000000000000000000000 : ℝ)*base91 + (29386831/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1449_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3907/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3743/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1449_s2_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-121796473/625000000 : ℝ)*x 0 + (2726896611/5000000000 : ℝ)*x 1 + (650605569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121796473/625000000 : ℝ)^4409 ≤ (11882220890197/100000000000000 : ℝ)^3385 := by
    have hnat : (121796473 : ℕ)^4409*100000000000000^3385 ≤ 11882220890197^3385*625000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121796473 625000000 11882220890197 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726896611/5000000000 : ℝ)^4409 ≤ (22699542396809/50000000000000 : ℝ)^3385 := by
    have hnat : (2726896611 : ℕ)^4409*50000000000000^3385 ≤ 22699542396809^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726896611 5000000000 22699542396809 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650605569/1250000000 : ℝ)^4409 ≤ (42718694311893/100000000000000 : ℝ)^3385 := by
    have hnat : (650605569 : ℕ)^4409*100000000000000^3385 ≤ 42718694311893^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650605569 1250000000 42718694311893 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121796473/625000000 : ℝ), (2726896611/5000000000 : ℝ), (650605569/1250000000 : ℝ)] ![(11882220890197/100000000000000 : ℝ), (22699542396809/50000000000000 : ℝ), (42718694311893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121796473/625000000 : ℝ)|^4409 ≤ (11882220890197/100000000000000 : ℝ)^3385
        have hw : |(-121796473/625000000 : ℝ)|=(121796473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726896611/5000000000 : ℝ)|^4409 ≤ (22699542396809/50000000000000 : ℝ)^3385
        have hw : |(2726896611/5000000000 : ℝ)|=(2726896611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650605569/1250000000 : ℝ)|^4409 ≤ (42718694311893/100000000000000 : ℝ)^3385
        have hw : |(650605569/1250000000 : ℝ)|=(650605569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s2_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358888043/10000000000 : ℝ)*x 0 + (-2076716763/10000000000 : ℝ)*x 1 + (1301211031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358888043/10000000000 : ℝ)^4409 ≤ (22186396941001/50000000000000 : ℝ)^3385 := by
    have hnat : (5358888043 : ℕ)^4409*50000000000000^3385 ≤ 22186396941001^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358888043 10000000000 22186396941001 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076716763/10000000000 : ℝ)^4409 ≤ (12908516372059/100000000000000 : ℝ)^3385 := by
    have hnat : (2076716763 : ℕ)^4409*100000000000000^3385 ≤ 12908516372059^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076716763 10000000000 12908516372059 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301211031/2500000000 : ℝ)^4409 ≤ (21359344868213/50000000000000 : ℝ)^3385 := by
    have hnat : (1301211031 : ℕ)^4409*50000000000000^3385 ≤ 21359344868213^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301211031 2500000000 21359344868213 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358888043/10000000000 : ℝ), (-2076716763/10000000000 : ℝ), (1301211031/2500000000 : ℝ)] ![(22186396941001/50000000000000 : ℝ), (12908516372059/100000000000000 : ℝ), (21359344868213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358888043/10000000000 : ℝ)|^4409 ≤ (22186396941001/50000000000000 : ℝ)^3385
        have hw : |(5358888043/10000000000 : ℝ)|=(5358888043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076716763/10000000000 : ℝ)|^4409 ≤ (12908516372059/100000000000000 : ℝ)^3385
        have hw : |(-2076716763/10000000000 : ℝ)|=(2076716763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301211031/2500000000 : ℝ)|^4409 ≤ (21359344868213/50000000000000 : ℝ)^3385
        have hw : |(1301211031/2500000000 : ℝ)|=(1301211031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s2_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358887341/10000000000 : ℝ)*x 0 + (5204844763/10000000000 : ℝ)*x 1 + (-1038358427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358887341/10000000000 : ℝ)^4409 ≤ (44372786310873/100000000000000 : ℝ)^3385 := by
    have hnat : (5358887341 : ℕ)^4409*100000000000000^3385 ≤ 44372786310873^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358887341 10000000000 44372786310873 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204844763/10000000000 : ℝ)^4409 ≤ (8543739313511/20000000000000 : ℝ)^3385 := by
    have hnat : (5204844763 : ℕ)^4409*20000000000000^3385 ≤ 8543739313511^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204844763 10000000000 8543739313511 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038358427/5000000000 : ℝ)^4409 ≤ (3227129277203/25000000000000 : ℝ)^3385 := by
    have hnat : (1038358427 : ℕ)^4409*25000000000000^3385 ≤ 3227129277203^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038358427 5000000000 3227129277203 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358887341/10000000000 : ℝ), (5204844763/10000000000 : ℝ), (-1038358427/5000000000 : ℝ)] ![(44372786310873/100000000000000 : ℝ), (8543739313511/20000000000000 : ℝ), (3227129277203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358887341/10000000000 : ℝ)|^4409 ≤ (44372786310873/100000000000000 : ℝ)^3385
        have hw : |(5358887341/10000000000 : ℝ)|=(5358887341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204844763/10000000000 : ℝ)|^4409 ≤ (8543739313511/20000000000000 : ℝ)^3385
        have hw : |(5204844763/10000000000 : ℝ)|=(5204844763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038358427/5000000000 : ℝ)|^4409 ≤ (3227129277203/25000000000000 : ℝ)^3385
        have hw : |(-1038358427/5000000000 : ℝ)|=(1038358427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s2_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2147699211/5000000000 : ℝ)*x 0 + (4031766607/10000000000 : ℝ)*x 1 + (2287138249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147699211/5000000000 : ℝ)^4409 ≤ (16632323999401/50000000000000 : ℝ)^3385 := by
    have hnat : (2147699211 : ℕ)^4409*50000000000000^3385 ≤ 16632323999401^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147699211 5000000000 16632323999401 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031766607/10000000000 : ℝ)^4409 ≤ (957201539107/3125000000000 : ℝ)^3385 := by
    have hnat : (4031766607 : ℕ)^4409*3125000000000^3385 ≤ 957201539107^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031766607 10000000000 957201539107 3125000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287138249/5000000000 : ℝ)^4409 ≤ (7220980545981/20000000000000 : ℝ)^3385 := by
    have hnat : (2287138249 : ℕ)^4409*20000000000000^3385 ≤ 7220980545981^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287138249 5000000000 7220980545981 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147699211/5000000000 : ℝ), (4031766607/10000000000 : ℝ), (2287138249/5000000000 : ℝ)] ![(16632323999401/50000000000000 : ℝ), (957201539107/3125000000000 : ℝ), (7220980545981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147699211/5000000000 : ℝ)|^4409 ≤ (16632323999401/50000000000000 : ℝ)^3385
        have hw : |(2147699211/5000000000 : ℝ)|=(2147699211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031766607/10000000000 : ℝ)|^4409 ≤ (957201539107/3125000000000 : ℝ)^3385
        have hw : |(4031766607/10000000000 : ℝ)|=(4031766607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2287138249/5000000000 : ℝ)|^4409 ≤ (7220980545981/20000000000000 : ℝ)^3385
        have hw : |(2287138249/5000000000 : ℝ)|=(2287138249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s2_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1948785087/10000000000 : ℝ)*x 0 + (5206241513/10000000000 : ℝ)*x 1 + (5452385343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1948785087/10000000000 : ℝ)^4409 ≤ (11882550630959/100000000000000 : ℝ)^3385 := by
    have hnat : (1948785087 : ℕ)^4409*100000000000000^3385 ≤ 11882550630959^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948785087 10000000000 11882550630959 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206241513/10000000000 : ℝ)^4409 ≤ (1068340722753/2500000000000 : ℝ)^3385 := by
    have hnat : (5206241513 : ℕ)^4409*2500000000000^3385 ≤ 1068340722753^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206241513 10000000000 1068340722753 2500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452385343/10000000000 : ℝ)^4409 ≤ (45383820446693/100000000000000 : ℝ)^3385 := by
    have hnat : (5452385343 : ℕ)^4409*100000000000000^3385 ≤ 45383820446693^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452385343 10000000000 45383820446693 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1948785087/10000000000 : ℝ), (5206241513/10000000000 : ℝ), (5452385343/10000000000 : ℝ)] ![(11882550630959/100000000000000 : ℝ), (1068340722753/2500000000000 : ℝ), (45383820446693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1948785087/10000000000 : ℝ)|^4409 ≤ (11882550630959/100000000000000 : ℝ)^3385
        have hw : |(-1948785087/10000000000 : ℝ)|=(1948785087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206241513/10000000000 : ℝ)|^4409 ≤ (1068340722753/2500000000000 : ℝ)^3385
        have hw : |(5206241513/10000000000 : ℝ)|=(5206241513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452385343/10000000000 : ℝ)|^4409 ≤ (45383820446693/100000000000000 : ℝ)^3385
        have hw : |(5452385343/10000000000 : ℝ)|=(5452385343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s2_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294033093/10000000000 : ℝ)*x 0 + (-1829173929/10000000000 : ℝ)*x 1 + (5452386699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294033093/10000000000 : ℝ)^4409 ≤ (5459326480889/12500000000000 : ℝ)^3385 := by
    have hnat : (5294033093 : ℕ)^4409*12500000000000^3385 ≤ 5459326480889^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294033093 10000000000 5459326480889 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1829173929/10000000000 : ℝ)^4409 ≤ (1367694124431/12500000000000 : ℝ)^3385 := by
    have hnat : (1829173929 : ℕ)^4409*12500000000000^3385 ≤ 1367694124431^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829173929 10000000000 1367694124431 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452386699/10000000000 : ℝ)^4409 ≤ (45383835147989/100000000000000 : ℝ)^3385 := by
    have hnat : (5452386699 : ℕ)^4409*100000000000000^3385 ≤ 45383835147989^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452386699 10000000000 45383835147989 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294033093/10000000000 : ℝ), (-1829173929/10000000000 : ℝ), (5452386699/10000000000 : ℝ)] ![(5459326480889/12500000000000 : ℝ), (1367694124431/12500000000000 : ℝ), (45383835147989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294033093/10000000000 : ℝ)|^4409 ≤ (5459326480889/12500000000000 : ℝ)^3385
        have hw : |(5294033093/10000000000 : ℝ)|=(5294033093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1829173929/10000000000 : ℝ)|^4409 ≤ (1367694124431/12500000000000 : ℝ)^3385
        have hw : |(-1829173929/10000000000 : ℝ)|=(1829173929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452386699/10000000000 : ℝ)|^4409 ≤ (45383835147989/100000000000000 : ℝ)^3385
        have hw : |(5452386699/10000000000 : ℝ)|=(5452386699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s2_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647016049/5000000000 : ℝ)*x 0 + (5452386261/10000000000 : ℝ)*x 1 + (-1829175911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647016049/5000000000 : ℝ)^4409 ≤ (43674601155409/100000000000000 : ℝ)^3385 := by
    have hnat : (2647016049 : ℕ)^4409*100000000000000^3385 ≤ 43674601155409^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647016049 5000000000 43674601155409 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452386261/10000000000 : ℝ)^4409 ≤ (2269191519967/5000000000000 : ℝ)^3385 := by
    have hnat : (5452386261 : ℕ)^4409*5000000000000^3385 ≤ 2269191519967^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452386261 10000000000 2269191519967 5000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1829175911/10000000000 : ℝ)^4409 ≤ (5470784218823/50000000000000 : ℝ)^3385 := by
    have hnat : (1829175911 : ℕ)^4409*50000000000000^3385 ≤ 5470784218823^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829175911 10000000000 5470784218823 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647016049/5000000000 : ℝ), (5452386261/10000000000 : ℝ), (-1829175911/10000000000 : ℝ)] ![(43674601155409/100000000000000 : ℝ), (2269191519967/5000000000000 : ℝ), (5470784218823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647016049/5000000000 : ℝ)|^4409 ≤ (43674601155409/100000000000000 : ℝ)^3385
        have hw : |(2647016049/5000000000 : ℝ)|=(2647016049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452386261/10000000000 : ℝ)|^4409 ≤ (2269191519967/5000000000000 : ℝ)^3385
        have hw : |(5452386261/10000000000 : ℝ)|=(5452386261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1829175911/10000000000 : ℝ)|^4409 ≤ (5470784218823/50000000000000 : ℝ)^3385
        have hw : |(-1829175911/10000000000 : ℝ)|=(1829175911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s2_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859097961/2000000000 : ℝ)*x 0 + (4571234343/10000000000 : ℝ)*x 1 + (504354171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859097961/2000000000 : ℝ)^4409 ≤ (33265569779721/100000000000000 : ℝ)^3385 := by
    have hnat : (859097961 : ℕ)^4409*100000000000000^3385 ≤ 33265569779721^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859097961 2000000000 33265569779721 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4571234343/10000000000 : ℝ)^4409 ≤ (36073630213121/100000000000000 : ℝ)^3385 := by
    have hnat : (4571234343 : ℕ)^4409*100000000000000^3385 ≤ 36073630213121^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571234343 10000000000 36073630213121 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504354171/1250000000 : ℝ)^4409 ≤ (6132159998441/20000000000000 : ℝ)^3385 := by
    have hnat : (504354171 : ℕ)^4409*20000000000000^3385 ≤ 6132159998441^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504354171 1250000000 6132159998441 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859097961/2000000000 : ℝ), (4571234343/10000000000 : ℝ), (504354171/1250000000 : ℝ)] ![(33265569779721/100000000000000 : ℝ), (36073630213121/100000000000000 : ℝ), (6132159998441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859097961/2000000000 : ℝ)|^4409 ≤ (33265569779721/100000000000000 : ℝ)^3385
        have hw : |(859097961/2000000000 : ℝ)|=(859097961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4571234343/10000000000 : ℝ)|^4409 ≤ (36073630213121/100000000000000 : ℝ)^3385
        have hw : |(4571234343/10000000000 : ℝ)|=(4571234343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504354171/1250000000 : ℝ)|^4409 ≤ (6132159998441/20000000000000 : ℝ)^3385
        have hw : |(504354171/1250000000 : ℝ)|=(504354171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3743/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3907/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1309/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (787/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3743/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3907/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3743/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3907/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3743/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3907/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3743/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3907/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3743/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3907/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3743/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3907/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3907/50000 : ℝ) ^ (551/128 : ℝ) ≤ (53581641635103/3125000000000000000 : ℝ) := by
    have hpowers : (3907/50000 : ℝ)^551 ≤ (53581641635103/3125000000000000000 : ℝ)^128 := by
      have hnat : (3907 : ℕ)^551*3125000000000000000^128 ≤ 53581641635103^128*50000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3907 50000 53581641635103 3125000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3907/50000 : ℝ)) (X := (53581641635103/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3743/20000 : ℝ) ^ (551/128 : ℝ) ≤ (36810750283563373/50000000000000000000 : ℝ) := by
    have hpowers : (3743/20000 : ℝ)^551 ≤ (36810750283563373/50000000000000000000 : ℝ)^128 := by
      have hnat : (3743 : ℕ)^551*50000000000000000000^128 ≤ 36810750283563373^128*20000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3743 20000 36810750283563373 50000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3743/20000 : ℝ)) (X := (36810750283563373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562553581641635103/1562500000000000000 : ℝ) ≤ (5000039830765029/5000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (1562553581641635103/1562500000000000000 : ℝ)^128 ≤ (5000039830765029/5000000000000000 : ℝ)^551 := by
      have hnat : (1562553581641635103 : ℕ)^128*5000000000000000^551 ≤ 5000039830765029^551*1562500000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562553581641635103 1562500000000000000 5000039830765029 5000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000039830765029/5000000000000000 : ℝ)) (X := (1562553581641635103/1562500000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50037668056549725021/50000000000000000000 : ℝ) ≤ (10001749588962787/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50037668056549725021/50000000000000000000 : ℝ)^128 ≤ (10001749588962787/10000000000000000 : ℝ)^551 := by
      have hnat : (50037668056549725021 : ℕ)^128*10000000000000000^551 ≤ 10001749588962787^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037668056549725021 50000000000000000000 10001749588962787 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001749588962787/10000000000000000 : ℝ)) (X := (50037668056549725021/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25036810750283563373/25000000000000000000 : ℝ) ≤ (2500854879098879/2500000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (25036810750283563373/25000000000000000000 : ℝ)^128 ≤ (2500854879098879/2500000000000000 : ℝ)^551 := by
      have hnat : (25036810750283563373 : ℕ)^128*2500000000000000^551 ≤ 2500854879098879^551*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036810750283563373 25000000000000000000 2500854879098879 2500000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500854879098879/2500000000000000 : ℝ)) (X := (25036810750283563373/25000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53581641635103/3125000000000000000 : ℝ) ≤ ((54492385382210236723/54505000000000000000 : ℝ)+2*(1669927432729/1090100000000000 : ℝ)*(3907/50000 : ℝ))^(551/128 : ℝ) := by
    rw [show (54492385382210236723/54505000000000000000 : ℝ)+2*(1669927432729/1090100000000000 : ℝ)*(3907/50000 : ℝ)=(5000039830765029/5000000000000000 : ℝ) by norm_num, show 1+2*(53581641635103/3125000000000000000 : ℝ)=(1562553581641635103/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36810750283563373/50000000000000000000 : ℝ)+(53581641635103/3125000000000000000 : ℝ) ≤ ((54492385382210236723/54505000000000000000 : ℝ)+(1669927432729/1090100000000000 : ℝ)*((3743/20000 : ℝ)+(3907/50000 : ℝ)))^(551/128 : ℝ) := by
    rw [show (54492385382210236723/54505000000000000000 : ℝ)+(1669927432729/1090100000000000 : ℝ)*((3743/20000 : ℝ)+(3907/50000 : ℝ))=(10001749588962787/10000000000000000 : ℝ) by norm_num, show 1+(36810750283563373/50000000000000000000 : ℝ)+(53581641635103/3125000000000000000 : ℝ)=(50037668056549725021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36810750283563373/50000000000000000000 : ℝ) ≤ ((54492385382210236723/54505000000000000000 : ℝ)+2*(1669927432729/1090100000000000 : ℝ)*(3743/20000 : ℝ))^(551/128 : ℝ) := by
    rw [show (54492385382210236723/54505000000000000000 : ℝ)+2*(1669927432729/1090100000000000 : ℝ)*(3743/20000 : ℝ)=(2500854879098879/2500000000000000 : ℝ) by norm_num, show 1+2*(36810750283563373/50000000000000000000 : ℝ)=(25036810750283563373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54492385382210236723/54505000000000000000 : ℝ)*(X 1 0+X 2 0)+(1669927432729/1090100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (3907/50000 : ℝ)) (hi := (3743/20000 : ℝ)) (c := (54492385382210236723/54505000000000000000 : ℝ)) (alpha := (1669927432729/1090100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54492385382210236723/54505000000000000000 : ℝ)*(X 0 1+X 2 1)+(1669927432729/1090100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (3907/50000 : ℝ)) (hi := (3743/20000 : ℝ)) (c := (54492385382210236723/54505000000000000000 : ℝ)) (alpha := (1669927432729/1090100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54492385382210236723/54505000000000000000 : ℝ)*(X 0 2+X 1 2)+(1669927432729/1090100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (3907/50000 : ℝ)) (hi := (3743/20000 : ℝ)) (c := (54492385382210236723/54505000000000000000 : ℝ)) (alpha := (1669927432729/1090100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-121796473/625000000 : ℝ)*X 0 0+(2726896611/5000000000 : ℝ)*X 0 1+(650605569/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358888043/10000000000 : ℝ)*X 1 0+(-2076716763/10000000000 : ℝ)*X 1 1+(1301211031/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358887341/10000000000 : ℝ)*X 2 0+(5204844763/10000000000 : ℝ)*X 2 1+(-1038358427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2147699211/5000000000 : ℝ)*X 0 0+(4031766607/10000000000 : ℝ)*X 0 1+(2287138249/5000000000 : ℝ)*X 0 2+(2147699211/5000000000 : ℝ)*X 1 0+(4031766607/10000000000 : ℝ)*X 1 1+(2287138249/5000000000 : ℝ)*X 1 2+(2147699211/5000000000 : ℝ)*X 2 0+(4031766607/10000000000 : ℝ)*X 2 1+(2287138249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1948785087/10000000000 : ℝ)*X 0 0+(5206241513/10000000000 : ℝ)*X 0 1+(5452385343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294033093/10000000000 : ℝ)*X 1 0+(-1829173929/10000000000 : ℝ)*X 1 1+(5452386699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647016049/5000000000 : ℝ)*X 2 0+(5452386261/10000000000 : ℝ)*X 2 1+(-1829175911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859097961/2000000000 : ℝ)*X 0 0+(4571234343/10000000000 : ℝ)*X 0 1+(504354171/1250000000 : ℝ)*X 0 2+(859097961/2000000000 : ℝ)*X 1 0+(4571234343/10000000000 : ℝ)*X 1 1+(504354171/1250000000 : ℝ)*X 1 2+(859097961/2000000000 : ℝ)*X 2 0+(4571234343/10000000000 : ℝ)*X 2 1+(504354171/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (344810334739354188569241/54505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112249573/25000000000000 : ℝ)*(base19) + (24214107/25000000000000 : ℝ)*(base23) + (8675731/20000000000000 : ℝ)*(upper3) + (22440041/20000000000000 : ℝ)*(lower4) + (183409591/100000000000000 : ℝ)*(upper5) + (732523007736943/25000000000000 : ℝ)*(major0) + (732523007736943/25000000000000 : ℝ)*(major1) + (732523007736943/25000000000000 : ℝ)*(major2) + (4016893121689097/100000000000000 : ℝ)*(sp0) + (1004223168172701/25000000000000 : ℝ)*(sp1) + (1004222526768351/25000000000000 : ℝ)*(sp2) + (1843289174272847/100000000000000 : ℝ)*(sp3) + (91179977/3125000000000 : ℝ)*(sp6) + (194382471/12500000000000 : ℝ)*(sp7) + (368658145866523/20000000000000 : ℝ)*(f.failure) + (4016893121689097/100000000000000 : ℝ)*(f.sum) + (31312137877949/27252500000000000000000000000 : ℝ)*base65 + (2110740860258667211/1362625000000000000000000000000000 : ℝ)*base68 + (3613859156907042211/1362625000000000000000000000000000 : ℝ)*base70 + (3861081943916042211/1362625000000000000000000000000000 : ℝ)*base72 + (94158114999783/54505000000000000000000000000 : ℝ)*base73 + (14222920962723957789/1362625000000000000000000000000000 : ℝ)*base75 + (16694691121625957789/1362625000000000000000000000000000 : ℝ)*base77 + (9341911572938582789/1362625000000000000000000000000000 : ℝ)*base79 + (197284920702381/27252500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4584683/1000000000000000000000 : ℝ)*base89 + (4584683/1000000000000000000000 : ℝ)*base91 + (4584683/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4347841146248268372228777/483886718750000000000000000000 : ℝ) := by norm_num
    linear_combination (188582021/100000000000000 : ℝ)*(base19) + (34955453/50000000000000 : ℝ)*(upper2) + (5897431/4000000000000 : ℝ)*(upper3) + (368821817/100000000000000 : ℝ)*(lower4) + (46304217401321/1562500000000 : ℝ)*(major0) + (46304217401321/1562500000000 : ℝ)*(major1) + (46304217401321/1562500000000 : ℝ)*(major2) + (118761021/12500000000000 : ℝ)*(sp0) + (20713127217/100000000000000 : ℝ)*(sp1) + (7338052281/100000000000000 : ℝ)*(sp3) + (4062650166058931/100000000000000 : ℝ)*(sp4) + (2031315107218931/50000000000000 : ℝ)*(sp5) + (40626511161471/1000000000000 : ℝ)*(sp6) + (372856214732301/20000000000000 : ℝ)*(sp7) + (932144205856893/50000000000000 : ℝ)*(f.failure) + (40626511161471/1000000000000 : ℝ)*(f.sum) + (18567878986143/2477500000000000000000000000 : ℝ)*base65 + (32654274412998269/15484375000000000000000000000000 : ℝ)*base68 + (94524267969720481/15484375000000000000000000000000 : ℝ)*base69 + (43645829764649303/7742187500000000000000000000000 : ℝ)*base71 + (3827174090001/4955000000000000000000000000 : ℝ)*base73 + (8515494339493053/7742187500000000000000000000000 : ℝ)*base75 + (97352131993782981/15484375000000000000000000000000 : ℝ)*base77 + (16593236033683161/3871093750000000000000000000000 : ℝ)*base80 + (4838339553463/2477500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7054547/2500000000000000000000 : ℝ)*base90 + (7054547/2500000000000000000000 : ℝ)*base92 + (7054547/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1449_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3743/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3907/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (787/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1449_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (787/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1449_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1449_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1449_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (787/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1449_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
