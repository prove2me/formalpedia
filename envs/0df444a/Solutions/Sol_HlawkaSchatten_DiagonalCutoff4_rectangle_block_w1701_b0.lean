-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1701_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:24.437304+00:00
-- url     : https://prove2.me/submissions/80fc1d6b-29b5-47ff-bb01-a3259068c4f2

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
theorem support_rectangle_w1701_s0_0 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1363513171/10000000000 : ℝ)*x 0 + (5716221497/10000000000 : ℝ)*x 1 + (198017961/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363513171/10000000000 : ℝ)^5231 ≤ (8395220125067/100000000000000 : ℝ)^4207 := by
    have hnat : (1363513171 : ℕ)^5231*100000000000000^4207 ≤ 8395220125067^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363513171 10000000000 8395220125067 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5716221497/10000000000 : ℝ)^5231 ≤ (12471780670351/25000000000000 : ℝ)^4207 := by
    have hnat : (5716221497 : ℕ)^5231*25000000000000^4207 ≤ 12471780670351^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5716221497 10000000000 12471780670351 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198017961/400000000 : ℝ)^5231 ≤ (20858828593953/50000000000000 : ℝ)^4207 := by
    have hnat : (198017961 : ℕ)^5231*50000000000000^4207 ≤ 20858828593953^4207*400000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198017961 400000000 20858828593953 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1363513171/10000000000 : ℝ), (5716221497/10000000000 : ℝ), (198017961/400000000 : ℝ)] ![(8395220125067/100000000000000 : ℝ), (12471780670351/25000000000000 : ℝ), (20858828593953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1363513171/10000000000 : ℝ)|^5231 ≤ (8395220125067/100000000000000 : ℝ)^4207
        have hw : |(-1363513171/10000000000 : ℝ)|=(1363513171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5716221497/10000000000 : ℝ)|^5231 ≤ (12471780670351/25000000000000 : ℝ)^4207
        have hw : |(5716221497/10000000000 : ℝ)|=(5716221497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198017961/400000000 : ℝ)|^5231 ≤ (20858828593953/50000000000000 : ℝ)^4207
        have hw : |(198017961/400000000 : ℝ)|=(198017961/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s0_1 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21135293/39062500 : ℝ)*x 0 + (-1779421133/10000000000 : ℝ)*x 1 + (247522419/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21135293/39062500 : ℝ)^5231 ≤ (5824113704777/12500000000000 : ℝ)^4207 := by
    have hnat : (21135293 : ℕ)^5231*12500000000000^4207 ≤ 5824113704777^4207*39062500^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21135293 39062500 5824113704777 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1779421133/10000000000 : ℝ)^5231 ≤ (5844719963567/50000000000000 : ℝ)^4207 := by
    have hnat : (1779421133 : ℕ)^5231*50000000000000^4207 ≤ 5844719963567^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779421133 10000000000 5844719963567 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247522419/500000000 : ℝ)^5231 ≤ (20858825214727/50000000000000 : ℝ)^4207 := by
    have hnat : (247522419 : ℕ)^5231*50000000000000^4207 ≤ 20858825214727^4207*500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247522419 500000000 20858825214727 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21135293/39062500 : ℝ), (-1779421133/10000000000 : ℝ), (247522419/500000000 : ℝ)] ![(5824113704777/12500000000000 : ℝ), (5844719963567/50000000000000 : ℝ), (20858825214727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21135293/39062500 : ℝ)|^5231 ≤ (5824113704777/12500000000000 : ℝ)^4207
        have hw : |(21135293/39062500 : ℝ)|=(21135293/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1779421133/10000000000 : ℝ)|^5231 ≤ (5844719963567/50000000000000 : ℝ)^4207
        have hw : |(-1779421133/10000000000 : ℝ)|=(1779421133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(247522419/500000000 : ℝ)|^5231 ≤ (20858825214727/50000000000000 : ℝ)^4207
        have hw : |(247522419/500000000 : ℝ)|=(247522419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s0_2 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5410634247/10000000000 : ℝ)*x 0 + (990089811/2000000000 : ℝ)*x 1 + (-111213829/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410634247/10000000000 : ℝ)^5231 ≤ (46592901489889/100000000000000 : ℝ)^4207 := by
    have hnat : (5410634247 : ℕ)^5231*100000000000000^4207 ≤ 46592901489889^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410634247 10000000000 46592901489889 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990089811/2000000000 : ℝ)^5231 ≤ (41717657502253/100000000000000 : ℝ)^4207 := by
    have hnat : (990089811 : ℕ)^5231*100000000000000^4207 ≤ 41717657502253^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990089811 2000000000 41717657502253 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111213829/625000000 : ℝ)^5231 ≤ (1168944099717/10000000000000 : ℝ)^4207 := by
    have hnat : (111213829 : ℕ)^5231*10000000000000^4207 ≤ 1168944099717^4207*625000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111213829 625000000 1168944099717 10000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410634247/10000000000 : ℝ), (990089811/2000000000 : ℝ), (-111213829/625000000 : ℝ)] ![(46592901489889/100000000000000 : ℝ), (41717657502253/100000000000000 : ℝ), (1168944099717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410634247/10000000000 : ℝ)|^5231 ≤ (46592901489889/100000000000000 : ℝ)^4207
        have hw : |(5410634247/10000000000 : ℝ)|=(5410634247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(990089811/2000000000 : ℝ)|^5231 ≤ (41717657502253/100000000000000 : ℝ)^4207
        have hw : |(990089811/2000000000 : ℝ)|=(990089811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111213829/625000000 : ℝ)|^5231 ≤ (1168944099717/10000000000000 : ℝ)^4207
        have hw : |(-111213829/625000000 : ℝ)|=(111213829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s0_3 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1011793917/2500000000 : ℝ)*x 0 + (3053635829/10000000000 : ℝ)*x 1 + (1045652239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011793917/2500000000 : ℝ)^5231 ≤ (3247366849623/10000000000000 : ℝ)^4207 := by
    have hnat : (1011793917 : ℕ)^5231*10000000000000^4207 ≤ 3247366849623^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011793917 2500000000 3247366849623 10000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3053635829/10000000000 : ℝ)^5231 ≤ (1429880663027/6250000000000 : ℝ)^4207 := by
    have hnat : (3053635829 : ℕ)^5231*6250000000000^4207 ≤ 1429880663027^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3053635829 10000000000 1429880663027 6250000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045652239/2000000000 : ℝ)^5231 ≤ (44648240876439/100000000000000 : ℝ)^4207 := by
    have hnat : (1045652239 : ℕ)^5231*100000000000000^4207 ≤ 44648240876439^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045652239 2000000000 44648240876439 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1011793917/2500000000 : ℝ), (3053635829/10000000000 : ℝ), (1045652239/2000000000 : ℝ)] ![(3247366849623/10000000000000 : ℝ), (1429880663027/6250000000000 : ℝ), (44648240876439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1011793917/2500000000 : ℝ)|^5231 ≤ (3247366849623/10000000000000 : ℝ)^4207
        have hw : |(1011793917/2500000000 : ℝ)|=(1011793917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3053635829/10000000000 : ℝ)|^5231 ≤ (1429880663027/6250000000000 : ℝ)^4207
        have hw : |(3053635829/10000000000 : ℝ)|=(3053635829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045652239/2000000000 : ℝ)|^5231 ≤ (44648240876439/100000000000000 : ℝ)^4207
        have hw : |(1045652239/2000000000 : ℝ)|=(1045652239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s0_4 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1365328221/10000000000 : ℝ)*x 0 + (4969450759/10000000000 : ℝ)*x 1 + (5696575977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1365328221/10000000000 : ℝ)^5231 ≤ (4204558927693/50000000000000 : ℝ)^4207 := by
    have hnat : (1365328221 : ℕ)^5231*50000000000000^4207 ≤ 4204558927693^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365328221 10000000000 4204558927693 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4969450759/10000000000 : ℝ)^5231 ≤ (10479213615707/25000000000000 : ℝ)^4207 := by
    have hnat : (4969450759 : ℕ)^5231*25000000000000^4207 ≤ 10479213615707^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4969450759 10000000000 10479213615707 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5696575977/10000000000 : ℝ)^5231 ≤ (24837013831349/50000000000000 : ℝ)^4207 := by
    have hnat : (5696575977 : ℕ)^5231*50000000000000^4207 ≤ 24837013831349^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696575977 10000000000 24837013831349 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1365328221/10000000000 : ℝ), (4969450759/10000000000 : ℝ), (5696575977/10000000000 : ℝ)] ![(4204558927693/50000000000000 : ℝ), (10479213615707/25000000000000 : ℝ), (24837013831349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1365328221/10000000000 : ℝ)|^5231 ≤ (4204558927693/50000000000000 : ℝ)^4207
        have hw : |(-1365328221/10000000000 : ℝ)|=(1365328221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4969450759/10000000000 : ℝ)|^5231 ≤ (10479213615707/25000000000000 : ℝ)^4207
        have hw : |(4969450759/10000000000 : ℝ)|=(4969450759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5696575977/10000000000 : ℝ)|^5231 ≤ (24837013831349/50000000000000 : ℝ)^4207
        have hw : |(5696575977/10000000000 : ℝ)|=(5696575977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s0_5 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202907941/10000000000 : ℝ)*x 0 + (-1033293977/10000000000 : ℝ)*x 1 + (2848287943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202907941/10000000000 : ℝ)^5231 ≤ (11094797208033/25000000000000 : ℝ)^4207 := by
    have hnat : (5202907941 : ℕ)^5231*25000000000000^4207 ≤ 11094797208033^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202907941 10000000000 11094797208033 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033293977/10000000000 : ℝ)^5231 ≤ (5946784471733/100000000000000 : ℝ)^4207 := by
    have hnat : (1033293977 : ℕ)^5231*100000000000000^4207 ≤ 5946784471733^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033293977 10000000000 5946784471733 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2848287943/5000000000 : ℝ)^5231 ≤ (24837013338017/50000000000000 : ℝ)^4207 := by
    have hnat : (2848287943 : ℕ)^5231*50000000000000^4207 ≤ 24837013338017^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848287943 5000000000 24837013338017 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202907941/10000000000 : ℝ), (-1033293977/10000000000 : ℝ), (2848287943/5000000000 : ℝ)] ![(11094797208033/25000000000000 : ℝ), (5946784471733/100000000000000 : ℝ), (24837013338017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202907941/10000000000 : ℝ)|^5231 ≤ (11094797208033/25000000000000 : ℝ)^4207
        have hw : |(5202907941/10000000000 : ℝ)|=(5202907941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033293977/10000000000 : ℝ)|^5231 ≤ (5946784471733/100000000000000 : ℝ)^4207
        have hw : |(-1033293977/10000000000 : ℝ)|=(1033293977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2848287943/5000000000 : ℝ)|^5231 ≤ (24837013338017/50000000000000 : ℝ)^4207
        have hw : |(2848287943/5000000000 : ℝ)|=(2848287943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s0_6 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202907989/10000000000 : ℝ)*x 0 + (2848288071/5000000000 : ℝ)*x 1 + (-516646759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202907989/10000000000 : ℝ)^5231 ≤ (44379189341213/100000000000000 : ℝ)^4207 := by
    have hnat : (5202907989 : ℕ)^5231*100000000000000^4207 ≤ 44379189341213^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202907989 10000000000 44379189341213 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848288071/5000000000 : ℝ)^5231 ≤ (49674029451703/100000000000000 : ℝ)^4207 := by
    have hnat : (2848288071 : ℕ)^5231*100000000000000^4207 ≤ 49674029451703^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848288071 5000000000 49674029451703 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516646759/5000000000 : ℝ)^5231 ≤ (743347648391/12500000000000 : ℝ)^4207 := by
    have hnat : (516646759 : ℕ)^5231*12500000000000^4207 ≤ 743347648391^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516646759 5000000000 743347648391 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202907989/10000000000 : ℝ), (2848288071/5000000000 : ℝ), (-516646759/5000000000 : ℝ)] ![(44379189341213/100000000000000 : ℝ), (49674029451703/100000000000000 : ℝ), (743347648391/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202907989/10000000000 : ℝ)|^5231 ≤ (44379189341213/100000000000000 : ℝ)^4207
        have hw : |(5202907989/10000000000 : ℝ)|=(5202907989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848288071/5000000000 : ℝ)|^5231 ≤ (49674029451703/100000000000000 : ℝ)^4207
        have hw : |(2848288071/5000000000 : ℝ)|=(2848288071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516646759/5000000000 : ℝ)|^5231 ≤ (743347648391/12500000000000 : ℝ)^4207
        have hw : |(-516646759/5000000000 : ℝ)|=(516646759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s0_7 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2026163761/5000000000 : ℝ)*x 0 + (5174300277/10000000000 : ℝ)*x 1 + (1554711737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026163761/5000000000 : ℝ)^5231 ≤ (32525075501753/100000000000000 : ℝ)^4207 := by
    have hnat : (2026163761 : ℕ)^5231*100000000000000^4207 ≤ 32525075501753^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026163761 5000000000 32525075501753 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174300277/10000000000 : ℝ)^5231 ≤ (44075983589673/100000000000000 : ℝ)^4207 := by
    have hnat : (5174300277 : ℕ)^5231*100000000000000^4207 ≤ 44075983589673^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174300277 10000000000 44075983589673 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1554711737/5000000000 : ℝ)^5231 ≤ (5849735223207/25000000000000 : ℝ)^4207 := by
    have hnat : (1554711737 : ℕ)^5231*25000000000000^4207 ≤ 5849735223207^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554711737 5000000000 5849735223207 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2026163761/5000000000 : ℝ), (5174300277/10000000000 : ℝ), (1554711737/5000000000 : ℝ)] ![(32525075501753/100000000000000 : ℝ), (44075983589673/100000000000000 : ℝ), (5849735223207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2026163761/5000000000 : ℝ)|^5231 ≤ (32525075501753/100000000000000 : ℝ)^4207
        have hw : |(2026163761/5000000000 : ℝ)|=(2026163761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174300277/10000000000 : ℝ)|^5231 ≤ (44075983589673/100000000000000 : ℝ)^4207
        have hw : |(5174300277/10000000000 : ℝ)|=(5174300277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1554711737/5000000000 : ℝ)|^5231 ≤ (5849735223207/25000000000000 : ℝ)^4207
        have hw : |(1554711737/5000000000 : ℝ)|=(1554711737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1701_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5781/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2223/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5223/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5223 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5223*1^1024 ≤ 0^1024*1^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5223/1024 : ℝ) ≤ (466920338968598377/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5223 ≤ (466920338968598377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5223*50000000000000000000^1024 ≤ 466920338968598377^1024*5^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 466920338968598377 50000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (466920338968598377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5223 := by
      have hnat : (1 : ℕ)^1024*1^5223 ≤ 1^5223*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50466920338968598377/50000000000000000000 : ℝ) ≤ (5009120077717217/5000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (50466920338968598377/50000000000000000000 : ℝ)^1024 ≤ (5009120077717217/5000000000000000 : ℝ)^5223 := by
      have hnat : (50466920338968598377 : ℕ)^1024*5000000000000000^5223 ≤ 5009120077717217^5223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50466920338968598377 50000000000000000000 5009120077717217 5000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009120077717217/5000000000000000 : ℝ)) (X := (50466920338968598377/50000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25466920338968598377/25000000000000000000 : ℝ) ≤ (2509120077717217/2500000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (25466920338968598377/25000000000000000000 : ℝ)^1024 ≤ (2509120077717217/2500000000000000 : ℝ)^5223 := by
      have hnat : (25466920338968598377 : ℕ)^1024*2500000000000000^5223 ≤ 2509120077717217^5223*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25466920338968598377 25000000000000000000 2509120077717217 2500000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509120077717217/2500000000000000 : ℝ)) (X := (25466920338968598377/25000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9120077717217/2000000000000000 : ℝ)*(0 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9120077717217/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(466920338968598377/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9120077717217/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5223/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9120077717217/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5009120077717217/5000000000000000 : ℝ) by norm_num, show 1+(466920338968598377/50000000000000000000 : ℝ)+(0 : ℝ)=(50466920338968598377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(466920338968598377/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9120077717217/2000000000000000 : ℝ)*(2/5 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9120077717217/2000000000000000 : ℝ)*(2/5 : ℝ)=(2509120077717217/2500000000000000 : ℝ) by norm_num, show 1+2*(466920338968598377/50000000000000000000 : ℝ)=(25466920338968598377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9120077717217/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9120077717217/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9120077717217/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9120077717217/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9120077717217/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9120077717217/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1363513171/10000000000 : ℝ)*X 0 0+(5716221497/10000000000 : ℝ)*X 0 1+(198017961/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((21135293/39062500 : ℝ)*X 1 0+(-1779421133/10000000000 : ℝ)*X 1 1+(247522419/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5410634247/10000000000 : ℝ)*X 2 0+(990089811/2000000000 : ℝ)*X 2 1+(-111213829/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1011793917/2500000000 : ℝ)*X 0 0+(3053635829/10000000000 : ℝ)*X 0 1+(1045652239/2000000000 : ℝ)*X 0 2+(1011793917/2500000000 : ℝ)*X 1 0+(3053635829/10000000000 : ℝ)*X 1 1+(1045652239/2000000000 : ℝ)*X 1 2+(1011793917/2500000000 : ℝ)*X 2 0+(3053635829/10000000000 : ℝ)*X 2 1+(1045652239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1365328221/10000000000 : ℝ)*X 0 0+(4969450759/10000000000 : ℝ)*X 0 1+(5696575977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5202907941/10000000000 : ℝ)*X 1 0+(-1033293977/10000000000 : ℝ)*X 1 1+(2848287943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5202907989/10000000000 : ℝ)*X 2 0+(2848288071/5000000000 : ℝ)*X 2 1+(-516646759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2026163761/5000000000 : ℝ)*X 0 0+(5174300277/10000000000 : ℝ)*X 0 1+(1554711737/5000000000 : ℝ)*X 0 2+(2026163761/5000000000 : ℝ)*X 1 0+(5174300277/10000000000 : ℝ)*X 1 1+(1554711737/5000000000 : ℝ)*X 1 2+(2026163761/5000000000 : ℝ)*X 2 0+(5174300277/10000000000 : ℝ)*X 2 1+(1554711737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (954427793026598040315873/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191615413/100000000000000 : ℝ)*(base1) + (1887165597/100000000000000 : ℝ)*(base19) + (1703494611/100000000000000 : ℝ)*(base23) + (296730473/100000000000000 : ℝ)*(upper3) + (206083137/100000000000000 : ℝ)*(upper5) + (882869310142923/100000000000000 : ℝ)*(major0) + (882869310142923/100000000000000 : ℝ)*(major1) + (882869310142923/100000000000000 : ℝ)*(major2) + (652939056118101/50000000000000 : ℝ)*(sp0) + (1305882428020659/100000000000000 : ℝ)*(sp1) + (261176522338329/20000000000000 : ℝ)*(sp2) + (229925702179493/50000000000000 : ℝ)*(sp3) + (3197282733/50000000000000 : ℝ)*(sp4) + (597745647/25000000000000 : ℝ)*(sp7) + (459853986956987/100000000000000 : ℝ)*(f.failure) + (81617769699141/6250000000000 : ℝ)*(f.sum) + (163192857794709/100000000000000000000000000000 : ℝ)*base66 + (167464023794709/200000000000000000000000000000 : ℝ)*base68 + (989611385005291/200000000000000000000000000000 : ℝ)*base69 + (980056123394709/200000000000000000000000000000 : ℝ)*base72 + (33467885505291/100000000000000000000000000000 : ℝ)*base73 + (1855002432594709/200000000000000000000000000000 : ℝ)*base76 + (841683331994709/200000000000000000000000000000 : ℝ)*base78 + (2335208501194709/200000000000000000000000000000 : ℝ)*base80 + (488609877605291/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (273419/2500000000000000000000 : ℝ)*base90 + (273419/2500000000000000000000 : ℝ)*base92 + (273419/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1383237893001819507/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (94254061/6250000000000 : ℝ)*(base19) + (405991951/25000000000000 : ℝ)*(base23) + (16004007/50000000000000 : ℝ)*(upper2) + (248624093/100000000000000 : ℝ)*(upper3) + (117259437/50000000000000 : ℝ)*(upper5) + (929784640824513/100000000000000 : ℝ)*(major0) + (929784640824513/100000000000000 : ℝ)*(major1) + (929784640824513/100000000000000 : ℝ)*(major2) + (5198108719/100000000000000 : ℝ)*(sp1) + (6242476027/100000000000000 : ℝ)*(sp2) + (171909831101199/12500000000000 : ℝ)*(sp4) + (1375271942635897/100000000000000 : ℝ)*(sp5) + (4297721194893/312500000000 : ℝ)*(sp6) + (484290448407711/100000000000000 : ℝ)*(sp7) + (484290448407711/100000000000000 : ℝ)*(f.failure) + (171909831101199/12500000000000 : ℝ)*(f.sum) + (182136895259679/100000000000000000000000000000 : ℝ)*base66 + (1076637519259679/200000000000000000000000000000 : ℝ)*base68 + (664709856140321/200000000000000000000000000000 : ℝ)*base69 + (496557258459679/200000000000000000000000000000 : ℝ)*base72 + (261412759359679/100000000000000000000000000000 : ℝ)*base74 + (318463140540321/200000000000000000000000000000 : ℝ)*base75 + (422970645540321/200000000000000000000000000000 : ℝ)*base77 + (914338065340321/200000000000000000000000000000 : ℝ)*base79 + (98903115140321/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11094993/2500000000000000000000 : ℝ)*base89 + (11094993/2500000000000000000000 : ℝ)*base91 + (11094993/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1701_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5781/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2223/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1701_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1701_s1_0 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-720425959/5000000000 : ℝ)*x 0 + (5493757211/10000000000 : ℝ)*x 1 + (1024425671/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (720425959/5000000000 : ℝ)^5231 ≤ (8991332507767/100000000000000 : ℝ)^4207 := by
    have hnat : (720425959 : ℕ)^5231*100000000000000^4207 ≤ 8991332507767^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720425959 5000000000 8991332507767 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493757211/10000000000 : ℝ)^5231 ≤ (23742294750993/50000000000000 : ℝ)^4207 := by
    have hnat : (5493757211 : ℕ)^5231*50000000000000^4207 ≤ 23742294750993^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493757211 10000000000 23742294750993 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024425671/2000000000 : ℝ)^5231 ≤ (10881019493659/25000000000000 : ℝ)^4207 := by
    have hnat : (1024425671 : ℕ)^5231*25000000000000^4207 ≤ 10881019493659^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024425671 2000000000 10881019493659 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-720425959/5000000000 : ℝ), (5493757211/10000000000 : ℝ), (1024425671/2000000000 : ℝ)] ![(8991332507767/100000000000000 : ℝ), (23742294750993/50000000000000 : ℝ), (10881019493659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-720425959/5000000000 : ℝ)|^5231 ≤ (8991332507767/100000000000000 : ℝ)^4207
        have hw : |(-720425959/5000000000 : ℝ)|=(720425959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493757211/10000000000 : ℝ)|^5231 ≤ (23742294750993/50000000000000 : ℝ)^4207
        have hw : |(5493757211/10000000000 : ℝ)|=(5493757211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024425671/2000000000 : ℝ)|^5231 ≤ (10881019493659/25000000000000 : ℝ)^4207
        have hw : |(1024425671/2000000000 : ℝ)|=(1024425671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s1_1 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351371081/10000000000 : ℝ)*x 0 + (-817191127/5000000000 : ℝ)*x 1 + (1024425529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351371081/10000000000 : ℝ)^5231 ≤ (919183912661/2000000000000 : ℝ)^4207 := by
    have hnat : (5351371081 : ℕ)^5231*2000000000000^4207 ≤ 919183912661^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351371081 10000000000 919183912661 2000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (817191127/5000000000 : ℝ)^5231 ≤ (10516733879733/100000000000000 : ℝ)^4207 := by
    have hnat : (817191127 : ℕ)^5231*100000000000000^4207 ≤ 10516733879733^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817191127 5000000000 10516733879733 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024425529/2000000000 : ℝ)^5231 ≤ (43524070473109/100000000000000 : ℝ)^4207 := by
    have hnat : (1024425529 : ℕ)^5231*100000000000000^4207 ≤ 43524070473109^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024425529 2000000000 43524070473109 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351371081/10000000000 : ℝ), (-817191127/5000000000 : ℝ), (1024425529/2000000000 : ℝ)] ![(919183912661/2000000000000 : ℝ), (10516733879733/100000000000000 : ℝ), (43524070473109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351371081/10000000000 : ℝ)|^5231 ≤ (919183912661/2000000000000 : ℝ)^4207
        have hw : |(5351371081/10000000000 : ℝ)|=(5351371081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-817191127/5000000000 : ℝ)|^5231 ≤ (10516733879733/100000000000000 : ℝ)^4207
        have hw : |(-817191127/5000000000 : ℝ)|=(817191127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024425529/2000000000 : ℝ)|^5231 ≤ (43524070473109/100000000000000 : ℝ)^4207
        have hw : |(1024425529/2000000000 : ℝ)|=(1024425529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s1_2 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668921229/1250000000 : ℝ)*x 0 + (1024425747/2000000000 : ℝ)*x 1 + (-1634382481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668921229/1250000000 : ℝ)^5231 ≤ (22979591147659/50000000000000 : ℝ)^4207 := by
    have hnat : (668921229 : ℕ)^5231*50000000000000^4207 ≤ 22979591147659^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668921229 1250000000 22979591147659 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024425747/2000000000 : ℝ)^5231 ≤ (43524081989537/100000000000000 : ℝ)^4207 := by
    have hnat : (1024425747 : ℕ)^5231*100000000000000^4207 ≤ 43524081989537^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024425747 2000000000 43524081989537 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1634382481/10000000000 : ℝ)^5231 ≤ (525836784797/5000000000000 : ℝ)^4207 := by
    have hnat : (1634382481 : ℕ)^5231*5000000000000^4207 ≤ 525836784797^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634382481 10000000000 525836784797 5000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668921229/1250000000 : ℝ), (1024425747/2000000000 : ℝ), (-1634382481/10000000000 : ℝ)] ![(22979591147659/50000000000000 : ℝ), (43524081989537/100000000000000 : ℝ), (525836784797/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668921229/1250000000 : ℝ)|^5231 ≤ (22979591147659/50000000000000 : ℝ)^4207
        have hw : |(668921229/1250000000 : ℝ)|=(668921229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024425747/2000000000 : ℝ)|^5231 ≤ (43524081989537/100000000000000 : ℝ)^4207
        have hw : |(1024425747/2000000000 : ℝ)|=(1024425747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1634382481/10000000000 : ℝ)|^5231 ≤ (525836784797/5000000000000 : ℝ)^4207
        have hw : |(-1634382481/10000000000 : ℝ)|=(1634382481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s1_3 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4113035497/10000000000 : ℝ)*x 0 + (721454959/2000000000 : ℝ)*x 1 + (932523813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4113035497/10000000000 : ℝ)^5231 ≤ (33132035199517/100000000000000 : ℝ)^4207 := by
    have hnat : (4113035497 : ℕ)^5231*100000000000000^4207 ≤ 33132035199517^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113035497 10000000000 33132035199517 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721454959/2000000000 : ℝ)^5231 ≤ (14072295635127/50000000000000 : ℝ)^4207 := by
    have hnat : (721454959 : ℕ)^5231*50000000000000^4207 ≤ 14072295635127^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721454959 2000000000 14072295635127 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932523813/2000000000 : ℝ)^5231 ≤ (7744674703809/20000000000000 : ℝ)^4207 := by
    have hnat : (932523813 : ℕ)^5231*20000000000000^4207 ≤ 7744674703809^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932523813 2000000000 7744674703809 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4113035497/10000000000 : ℝ), (721454959/2000000000 : ℝ), (932523813/2000000000 : ℝ)] ![(33132035199517/100000000000000 : ℝ), (14072295635127/50000000000000 : ℝ), (7744674703809/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4113035497/10000000000 : ℝ)|^5231 ≤ (33132035199517/100000000000000 : ℝ)^4207
        have hw : |(4113035497/10000000000 : ℝ)|=(4113035497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(721454959/2000000000 : ℝ)|^5231 ≤ (14072295635127/50000000000000 : ℝ)^4207
        have hw : |(721454959/2000000000 : ℝ)|=(721454959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(932523813/2000000000 : ℝ)|^5231 ≤ (7744674703809/20000000000000 : ℝ)^4207
        have hw : |(932523813/2000000000 : ℝ)|=(932523813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s1_4 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360264293/2500000000 : ℝ)*x 0 + (1281651039/2500000000 : ℝ)*x 1 + (343075497/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360264293/2500000000 : ℝ)^5231 ≤ (2248231285527/25000000000000 : ℝ)^4207 := by
    have hnat : (360264293 : ℕ)^5231*25000000000000^4207 ≤ 2248231285527^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360264293 2500000000 2248231285527 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281651039/2500000000 : ℝ)^5231 ≤ (1742854888677/4000000000000 : ℝ)^4207 := by
    have hnat : (1281651039 : ℕ)^5231*4000000000000^4207 ≤ 1742854888677^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281651039 2500000000 1742854888677 4000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343075497/625000000 : ℝ)^5231 ≤ (29647314139/62500000000 : ℝ)^4207 := by
    have hnat : (343075497 : ℕ)^5231*62500000000^4207 ≤ 29647314139^4207*625000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343075497 625000000 29647314139 62500000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360264293/2500000000 : ℝ), (1281651039/2500000000 : ℝ), (343075497/625000000 : ℝ)] ![(2248231285527/25000000000000 : ℝ), (1742854888677/4000000000000 : ℝ), (29647314139/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360264293/2500000000 : ℝ)|^5231 ≤ (2248231285527/25000000000000 : ℝ)^4207
        have hw : |(-360264293/2500000000 : ℝ)|=(360264293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281651039/2500000000 : ℝ)|^5231 ≤ (1742854888677/4000000000000 : ℝ)^4207
        have hw : |(1281651039/2500000000 : ℝ)|=(1281651039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(343075497/625000000 : ℝ)|^5231 ≤ (29647314139/62500000000 : ℝ)^4207
        have hw : |(343075497/625000000 : ℝ)|=(343075497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s1_5 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251882311/10000000000 : ℝ)*x 0 + (-126730231/1000000000 : ℝ)*x 1 + (686150997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251882311/10000000000 : ℝ)^5231 ≤ (44899197206471/100000000000000 : ℝ)^4207 := by
    have hnat : (5251882311 : ℕ)^5231*100000000000000^4207 ≤ 44899197206471^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251882311 10000000000 44899197206471 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126730231/1000000000 : ℝ)^5231 ≤ (3832549946689/50000000000000 : ℝ)^4207 := by
    have hnat : (126730231 : ℕ)^5231*50000000000000^4207 ≤ 3832549946689^4207*1000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126730231 1000000000 3832549946689 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686150997/1250000000 : ℝ)^5231 ≤ (47435702880281/100000000000000 : ℝ)^4207 := by
    have hnat : (686150997 : ℕ)^5231*100000000000000^4207 ≤ 47435702880281^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686150997 1250000000 47435702880281 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251882311/10000000000 : ℝ), (-126730231/1000000000 : ℝ), (686150997/1250000000 : ℝ)] ![(44899197206471/100000000000000 : ℝ), (3832549946689/50000000000000 : ℝ), (47435702880281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251882311/10000000000 : ℝ)|^5231 ≤ (44899197206471/100000000000000 : ℝ)^4207
        have hw : |(5251882311/10000000000 : ℝ)|=(5251882311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126730231/1000000000 : ℝ)|^5231 ≤ (3832549946689/50000000000000 : ℝ)^4207
        have hw : |(-126730231/1000000000 : ℝ)|=(126730231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686150997/1250000000 : ℝ)|^5231 ≤ (47435702880281/100000000000000 : ℝ)^4207
        have hw : |(686150997/1250000000 : ℝ)|=(686150997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s1_6 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52518823/100000000 : ℝ)*x 0 + (2744604191/5000000000 : ℝ)*x 1 + (-1267301747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52518823/100000000 : ℝ)^5231 ≤ (44899197089541/100000000000000 : ℝ)^4207 := by
    have hnat : (52518823 : ℕ)^5231*100000000000000^4207 ≤ 44899197089541^4207*100000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52518823 100000000 44899197089541 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744604191/5000000000 : ℝ)^5231 ≤ (9487141448553/20000000000000 : ℝ)^4207 := by
    have hnat : (2744604191 : ℕ)^5231*20000000000000^4207 ≤ 9487141448553^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744604191 5000000000 9487141448553 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267301747/10000000000 : ℝ)^5231 ≤ (3832547829653/50000000000000 : ℝ)^4207 := by
    have hnat : (1267301747 : ℕ)^5231*50000000000000^4207 ≤ 3832547829653^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267301747 10000000000 3832547829653 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52518823/100000000 : ℝ), (2744604191/5000000000 : ℝ), (-1267301747/10000000000 : ℝ)] ![(44899197089541/100000000000000 : ℝ), (9487141448553/20000000000000 : ℝ), (3832547829653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52518823/100000000 : ℝ)|^5231 ≤ (44899197089541/100000000000000 : ℝ)^4207
        have hw : |(52518823/100000000 : ℝ)|=(52518823/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744604191/5000000000 : ℝ)|^5231 ≤ (9487141448553/20000000000000 : ℝ)^4207
        have hw : |(2744604191/5000000000 : ℝ)|=(2744604191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1267301747/10000000000 : ℝ)|^5231 ≤ (3832547829653/50000000000000 : ℝ)^4207
        have hw : |(-1267301747/10000000000 : ℝ)|=(1267301747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s1_7 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32908949/80000000 : ℝ)*x 0 + (145309651/312500000 : ℝ)*x 1 + (1810096047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32908949/80000000 : ℝ)^5231 ≤ (16568937979031/50000000000000 : ℝ)^4207 := by
    have hnat : (32908949 : ℕ)^5231*50000000000000^4207 ≤ 16568937979031^4207*80000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32908949 80000000 16568937979031 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145309651/312500000 : ℝ)^5231 ≤ (7718432834867/20000000000000 : ℝ)^4207 := by
    have hnat : (145309651 : ℕ)^5231*20000000000000^4207 ≤ 7718432834867^4207*312500000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145309651 312500000 7718432834867 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1810096047/5000000000 : ℝ)^5231 ≤ (1130798393863/4000000000000 : ℝ)^4207 := by
    have hnat : (1810096047 : ℕ)^5231*4000000000000^4207 ≤ 1130798393863^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810096047 5000000000 1130798393863 4000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32908949/80000000 : ℝ), (145309651/312500000 : ℝ), (1810096047/5000000000 : ℝ)] ![(16568937979031/50000000000000 : ℝ), (7718432834867/20000000000000 : ℝ), (1130798393863/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32908949/80000000 : ℝ)|^5231 ≤ (16568937979031/50000000000000 : ℝ)^4207
        have hw : |(32908949/80000000 : ℝ)|=(32908949/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(145309651/312500000 : ℝ)|^5231 ≤ (7718432834867/20000000000000 : ℝ)^4207
        have hw : |(145309651/312500000 : ℝ)|=(145309651/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1810096047/5000000000 : ℝ)|^5231 ≤ (1130798393863/4000000000000 : ℝ)^4207
        have hw : |(1810096047/5000000000 : ℝ)|=(1810096047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1701_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2223/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5781/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9609/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4383/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2223/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5781/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2223/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5781/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2223/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5781/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2223/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5781/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2223/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5781/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2223/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5781/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5781/100000 : ℝ) ^ (5223/1024 : ℝ) ≤ (4847186779031/10000000000000000000 : ℝ) := by
    have hpowers : (5781/100000 : ℝ)^5223 ≤ (4847186779031/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5781 : ℕ)^5223*10000000000000000000^1024 ≤ 4847186779031^1024*100000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5781 100000 4847186779031 10000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5781/100000 : ℝ)) (X := (4847186779031/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2223/10000 : ℝ) ^ (5223/1024 : ℝ) ≤ (11666715723475353/25000000000000000000 : ℝ) := by
    have hpowers : (2223/10000 : ℝ)^5223 ≤ (11666715723475353/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2223 : ℕ)^5223*25000000000000000000^1024 ≤ 11666715723475353^1024*10000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2223 10000 11666715723475353 25000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2223/10000 : ℝ)) (X := (11666715723475353/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000004847186779031/5000000000000000000 : ℝ) ≤ (1250000237579807/1250000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (5000004847186779031/5000000000000000000 : ℝ)^1024 ≤ (1250000237579807/1250000000000000 : ℝ)^5223 := by
      have hnat : (5000004847186779031 : ℕ)^1024*1250000000000000^5223 ≤ 1250000237579807^5223*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000004847186779031 5000000000000000000 1250000237579807 1250000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000237579807/1250000000000000 : ℝ)) (X := (5000004847186779031/5000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023357667380845861/50000000000000000000 : ℝ) ≤ (2000183141958477/2000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (50023357667380845861/50000000000000000000 : ℝ)^1024 ≤ (2000183141958477/2000000000000000 : ℝ)^5223 := by
      have hnat : (50023357667380845861 : ℕ)^1024*2000000000000000^5223 ≤ 2000183141958477^5223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023357667380845861 50000000000000000000 2000183141958477 2000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000183141958477/2000000000000000 : ℝ)) (X := (50023357667380845861/50000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511666715723475353/12500000000000000000 : ℝ) ≤ (5000914759473157/5000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (12511666715723475353/12500000000000000000 : ℝ)^1024 ≤ (5000914759473157/5000000000000000 : ℝ)^5223 := by
      have hnat : (12511666715723475353 : ℕ)^1024*5000000000000000^5223 ≤ 5000914759473157^5223*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511666715723475353 12500000000000000000 5000914759473157 5000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000914759473157/5000000000000000 : ℝ)) (X := (12511666715723475353/12500000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4847186779031/10000000000000000000 : ℝ) ≤ ((27413244300360705941/27415000000000000000 : ℝ)+2*(913809153929/1644900000000000 : ℝ)*(5781/100000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (27413244300360705941/27415000000000000000 : ℝ)+2*(913809153929/1644900000000000 : ℝ)*(5781/100000 : ℝ)=(1250000237579807/1250000000000000 : ℝ) by norm_num, show 1+2*(4847186779031/10000000000000000000 : ℝ)=(5000004847186779031/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11666715723475353/25000000000000000000 : ℝ)+(4847186779031/10000000000000000000 : ℝ) ≤ ((27413244300360705941/27415000000000000000 : ℝ)+(913809153929/1644900000000000 : ℝ)*((2223/10000 : ℝ)+(5781/100000 : ℝ)))^(5223/1024 : ℝ) := by
    rw [show (27413244300360705941/27415000000000000000 : ℝ)+(913809153929/1644900000000000 : ℝ)*((2223/10000 : ℝ)+(5781/100000 : ℝ))=(2000183141958477/2000000000000000 : ℝ) by norm_num, show 1+(11666715723475353/25000000000000000000 : ℝ)+(4847186779031/10000000000000000000 : ℝ)=(50023357667380845861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11666715723475353/25000000000000000000 : ℝ) ≤ ((27413244300360705941/27415000000000000000 : ℝ)+2*(913809153929/1644900000000000 : ℝ)*(2223/10000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (27413244300360705941/27415000000000000000 : ℝ)+2*(913809153929/1644900000000000 : ℝ)*(2223/10000 : ℝ)=(5000914759473157/5000000000000000 : ℝ) by norm_num, show 1+2*(11666715723475353/25000000000000000000 : ℝ)=(12511666715723475353/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27413244300360705941/27415000000000000000 : ℝ)*(X 1 0+X 2 0)+(913809153929/1644900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (5781/100000 : ℝ)) (hi := (2223/10000 : ℝ)) (c := (27413244300360705941/27415000000000000000 : ℝ)) (alpha := (913809153929/1644900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27413244300360705941/27415000000000000000 : ℝ)*(X 0 1+X 2 1)+(913809153929/1644900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (5781/100000 : ℝ)) (hi := (2223/10000 : ℝ)) (c := (27413244300360705941/27415000000000000000 : ℝ)) (alpha := (913809153929/1644900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27413244300360705941/27415000000000000000 : ℝ)*(X 0 2+X 1 2)+(913809153929/1644900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (5781/100000 : ℝ)) (hi := (2223/10000 : ℝ)) (c := (27413244300360705941/27415000000000000000 : ℝ)) (alpha := (913809153929/1644900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-720425959/5000000000 : ℝ)*X 0 0+(5493757211/10000000000 : ℝ)*X 0 1+(1024425671/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351371081/10000000000 : ℝ)*X 1 0+(-817191127/5000000000 : ℝ)*X 1 1+(1024425529/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668921229/1250000000 : ℝ)*X 2 0+(1024425747/2000000000 : ℝ)*X 2 1+(-1634382481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4113035497/10000000000 : ℝ)*X 0 0+(721454959/2000000000 : ℝ)*X 0 1+(932523813/2000000000 : ℝ)*X 0 2+(4113035497/10000000000 : ℝ)*X 1 0+(721454959/2000000000 : ℝ)*X 1 1+(932523813/2000000000 : ℝ)*X 1 2+(4113035497/10000000000 : ℝ)*X 2 0+(721454959/2000000000 : ℝ)*X 2 1+(932523813/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-360264293/2500000000 : ℝ)*X 0 0+(1281651039/2500000000 : ℝ)*X 0 1+(343075497/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251882311/10000000000 : ℝ)*X 1 0+(-126730231/1000000000 : ℝ)*X 1 1+(686150997/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((52518823/100000000 : ℝ)*X 2 0+(2744604191/5000000000 : ℝ)*X 2 1+(-1267301747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((32908949/80000000 : ℝ)*X 0 0+(145309651/312500000 : ℝ)*X 0 1+(1810096047/5000000000 : ℝ)*X 0 2+(32908949/80000000 : ℝ)*X 1 0+(145309651/312500000 : ℝ)*X 1 1+(1810096047/5000000000 : ℝ)*X 1 2+(32908949/80000000 : ℝ)*X 2 0+(145309651/312500000 : ℝ)*X 2 1+(1810096047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1264705351963932027580662111/137075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1191099267/100000000000000 : ℝ)*(base19) + (69682047/12500000000000 : ℝ)*(base23) + (11522669/50000000000000 : ℝ)*(lower2) + (57942991/25000000000000 : ℝ)*(upper3) + (5012309/25000000000000 : ℝ)*(lower4) + (181921715284819/10000000000000 : ℝ)*(major0) + (181921715284819/10000000000000 : ℝ)*(major1) + (181921715284819/10000000000000 : ℝ)*(major2) + (2690866724419909/100000000000000 : ℝ)*(sp0) + (336358730305787/12500000000000 : ℝ)*(sp1) + (1345435238044593/50000000000000 : ℝ)*(sp2) + (473780087514183/50000000000000 : ℝ)*(sp3) + (4309125653/100000000000000 : ℝ)*(sp4) + (2789576611/100000000000000 : ℝ)*(sp7) + (947562964604977/100000000000000 : ℝ)*(f.failure) + (1345435516772781/50000000000000 : ℝ)*(f.sum) + (43699477706849/16449000000000000000000000000 : ℝ)*base66 + (3783782714549270963/822450000000000000000000000000000 : ℝ)*base68 + (8261885274904970963/822450000000000000000000000000000 : ℝ)*base70 + (8414145589801070963/822450000000000000000000000000000 : ℝ)*base72 + (39952846513/822450000000000000000000000 : ℝ)*base74 + (16271923680879020963/822450000000000000000000000000000 : ℝ)*base76 + (2321329709522270963/822450000000000000000000000000000 : ℝ)*base78 + (6889873738314620963/822450000000000000000000000000000 : ℝ)*base80 + (211020773129/102806250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (22177951/2500000000000000000000 : ℝ)*base89 + (22177951/2500000000000000000000 : ℝ)*base91 + (22177951/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357463674666144183329398587/137075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40556899/10000000000000 : ℝ)*(base19) + (584491709/100000000000000 : ℝ)*(base23) + (11357059/10000000000000 : ℝ)*(upper3) + (17817107/50000000000000 : ℝ)*(lower4) + (5171769/100000000000000 : ℝ)*(upper5) + (186448525050669/10000000000000 : ℝ)*(major0) + (186448525050669/10000000000000 : ℝ)*(major1) + (186448525050669/10000000000000 : ℝ)*(major2) + (82806873/4000000000000 : ℝ)*(sp1) + (8238558801/100000000000000 : ℝ)*(sp2) + (1378914485410109/50000000000000 : ℝ)*(sp4) + (1378913247539701/50000000000000 : ℝ)*(sp5) + (2757820147769707/100000000000000 : ℝ)*(sp6) + (485570721633307/50000000000000 : ℝ)*(sp7) + (485570721633307/50000000000000 : ℝ)*(f.failure) + (1378914485410109/50000000000000 : ℝ)*(f.sum) + (3435443136587/1370750000000000000000000000 : ℝ)*base66 + (241080731229725471/274150000000000000000000000000000 : ℝ)*base68 + (966032682093125471/274150000000000000000000000000000 : ℝ)*base70 + (1604805840624875471/274150000000000000000000000000000 : ℝ)*base72 + (1574391055443/274150000000000000000000000 : ℝ)*base73 + (38359997231724529/274150000000000000000000000000000 : ℝ)*base75 + (1217905261317625471/274150000000000000000000000000000 : ℝ)*base78 + (2080502397576124529/274150000000000000000000000000000 : ℝ)*base79 + (2161621522067/685375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (638741/1250000000000000000000 : ℝ)*base89 + (638741/1250000000000000000000 : ℝ)*base91 + (638741/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1701_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2223/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5781/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9609/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4383/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1701_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1701_s2_0 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1445078593/10000000000 : ℝ)*x 0 + (684573893/1250000000 : ℝ)*x 1 + (5136472931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445078593/10000000000 : ℝ)^5231 ≤ (9024139821879/100000000000000 : ℝ)^4207 := by
    have hnat : (1445078593 : ℕ)^5231*100000000000000^4207 ≤ 9024139821879^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445078593 10000000000 9024139821879 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684573893/1250000000 : ℝ)^5231 ≤ (9460034502913/20000000000000 : ℝ)^4207 := by
    have hnat : (684573893 : ℕ)^5231*20000000000000^4207 ≤ 9460034502913^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684573893 1250000000 9460034502913 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136472931/10000000000 : ℝ)^5231 ≤ (21837843828211/50000000000000 : ℝ)^4207 := by
    have hnat : (5136472931 : ℕ)^5231*50000000000000^4207 ≤ 21837843828211^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136472931 10000000000 21837843828211 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1445078593/10000000000 : ℝ), (684573893/1250000000 : ℝ), (5136472931/10000000000 : ℝ)] ![(9024139821879/100000000000000 : ℝ), (9460034502913/20000000000000 : ℝ), (21837843828211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1445078593/10000000000 : ℝ)|^5231 ≤ (9024139821879/100000000000000 : ℝ)^4207
        have hw : |(-1445078593/10000000000 : ℝ)|=(1445078593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684573893/1250000000 : ℝ)|^5231 ≤ (9460034502913/20000000000000 : ℝ)^4207
        have hw : |(684573893/1250000000 : ℝ)|=(684573893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136472931/10000000000 : ℝ)|^5231 ≤ (21837843828211/50000000000000 : ℝ)^4207
        have hw : |(5136472931/10000000000 : ℝ)|=(5136472931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s2_1 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346740583/10000000000 : ℝ)*x 0 + (-1621599421/10000000000 : ℝ)*x 1 + (256823657/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346740583/10000000000 : ℝ)^5231 ≤ (1836390120351/4000000000000 : ℝ)^4207 := by
    have hnat : (5346740583 : ℕ)^5231*4000000000000^4207 ≤ 1836390120351^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346740583 10000000000 1836390120351 4000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1621599421/10000000000 : ℝ)^5231 ≤ (2603639277523/25000000000000 : ℝ)^4207 := by
    have hnat : (1621599421 : ℕ)^5231*25000000000000^4207 ≤ 2603639277523^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621599421 10000000000 2603639277523 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256823657/500000000 : ℝ)^5231 ≤ (21837844933061/50000000000000 : ℝ)^4207 := by
    have hnat : (256823657 : ℕ)^5231*50000000000000^4207 ≤ 21837844933061^4207*500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256823657 500000000 21837844933061 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346740583/10000000000 : ℝ), (-1621599421/10000000000 : ℝ), (256823657/500000000 : ℝ)] ![(1836390120351/4000000000000 : ℝ), (2603639277523/25000000000000 : ℝ), (21837844933061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346740583/10000000000 : ℝ)|^5231 ≤ (1836390120351/4000000000000 : ℝ)^4207
        have hw : |(5346740583/10000000000 : ℝ)|=(5346740583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1621599421/10000000000 : ℝ)|^5231 ≤ (2603639277523/25000000000000 : ℝ)^4207
        have hw : |(-1621599421/10000000000 : ℝ)|=(1621599421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256823657/500000000 : ℝ)|^5231 ≤ (21837844933061/50000000000000 : ℝ)^4207
        have hw : |(256823657/500000000 : ℝ)|=(256823657/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s2_2 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346740347/10000000000 : ℝ)*x 0 + (1284118271/2500000000 : ℝ)*x 1 + (-162159981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346740347/10000000000 : ℝ)^5231 ≤ (22954875244563/50000000000000 : ℝ)^4207 := by
    have hnat : (5346740347 : ℕ)^5231*50000000000000^4207 ≤ 22954875244563^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346740347 10000000000 22954875244563 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284118271/2500000000 : ℝ)^5231 ≤ (43675689274049/100000000000000 : ℝ)^4207 := by
    have hnat : (1284118271 : ℕ)^5231*100000000000000^4207 ≤ 43675689274049^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284118271 2500000000 43675689274049 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162159981/1000000000 : ℝ)^5231 ≤ (1301820027063/12500000000000 : ℝ)^4207 := by
    have hnat : (162159981 : ℕ)^5231*12500000000000^4207 ≤ 1301820027063^4207*1000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162159981 1000000000 1301820027063 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346740347/10000000000 : ℝ), (1284118271/2500000000 : ℝ), (-162159981/1000000000 : ℝ)] ![(22954875244563/50000000000000 : ℝ), (43675689274049/100000000000000 : ℝ), (1301820027063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346740347/10000000000 : ℝ)|^5231 ≤ (22954875244563/50000000000000 : ℝ)^4207
        have hw : |(5346740347/10000000000 : ℝ)|=(5346740347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284118271/2500000000 : ℝ)|^5231 ≤ (43675689274049/100000000000000 : ℝ)^4207
        have hw : |(1284118271/2500000000 : ℝ)|=(1284118271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-162159981/1000000000 : ℝ)|^5231 ≤ (1301820027063/12500000000000 : ℝ)^4207
        have hw : |(-162159981/1000000000 : ℝ)|=(162159981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s2_3 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823260059/2000000000 : ℝ)*x 0 + (73034411/200000000 : ℝ)*x 1 + (230879109/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823260059/2000000000 : ℝ)^5231 ≤ (6632947768363/20000000000000 : ℝ)^4207 := by
    have hnat : (823260059 : ℕ)^5231*20000000000000^4207 ≤ 6632947768363^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823260059 2000000000 6632947768363 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73034411/200000000 : ℝ)^5231 ≤ (28576415438159/100000000000000 : ℝ)^4207 := by
    have hnat : (73034411 : ℕ)^5231*100000000000000^4207 ≤ 28576415438159^4207*200000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73034411 200000000 28576415438159 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230879109/500000000 : ℝ)^5231 ≤ (19129422852219/50000000000000 : ℝ)^4207 := by
    have hnat : (230879109 : ℕ)^5231*50000000000000^4207 ≤ 19129422852219^4207*500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230879109 500000000 19129422852219 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823260059/2000000000 : ℝ), (73034411/200000000 : ℝ), (230879109/500000000 : ℝ)] ![(6632947768363/20000000000000 : ℝ), (28576415438159/100000000000000 : ℝ), (19129422852219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823260059/2000000000 : ℝ)|^5231 ≤ (6632947768363/20000000000000 : ℝ)^4207
        have hw : |(823260059/2000000000 : ℝ)|=(823260059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73034411/200000000 : ℝ)|^5231 ≤ (28576415438159/100000000000000 : ℝ)^4207
        have hw : |(73034411/200000000 : ℝ)|=(73034411/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230879109/500000000 : ℝ)|^5231 ≤ (19129422852219/50000000000000 : ℝ)^4207
        have hw : |(230879109/500000000 : ℝ)|=(230879109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s2_4 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-361308889/2500000000 : ℝ)*x 0 + (1285056197/2500000000 : ℝ)*x 1 + (2736391621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361308889/2500000000 : ℝ)^5231 ≤ (4512679306929/50000000000000 : ℝ)^4207 := by
    have hnat : (361308889 : ℕ)^5231*50000000000000^4207 ≤ 4512679306929^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361308889 2500000000 4512679306929 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285056197/2500000000 : ℝ)^5231 ≤ (437153585361/1000000000000 : ℝ)^4207 := by
    have hnat : (1285056197 : ℕ)^5231*1000000000000^4207 ≤ 437153585361^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285056197 2500000000 437153585361 1000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736391621/5000000000 : ℝ)^5231 ≤ (9451856568683/20000000000000 : ℝ)^4207 := by
    have hnat : (2736391621 : ℕ)^5231*20000000000000^4207 ≤ 9451856568683^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736391621 5000000000 9451856568683 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361308889/2500000000 : ℝ), (1285056197/2500000000 : ℝ), (2736391621/5000000000 : ℝ)] ![(4512679306929/50000000000000 : ℝ), (437153585361/1000000000000 : ℝ), (9451856568683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361308889/2500000000 : ℝ)|^5231 ≤ (4512679306929/50000000000000 : ℝ)^4207
        have hw : |(-361308889/2500000000 : ℝ)|=(361308889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285056197/2500000000 : ℝ)|^5231 ≤ (437153585361/1000000000000 : ℝ)^4207
        have hw : |(1285056197/2500000000 : ℝ)|=(1285056197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736391621/5000000000 : ℝ)|^5231 ≤ (9451856568683/20000000000000 : ℝ)^4207
        have hw : |(2736391621/5000000000 : ℝ)|=(2736391621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s2_5 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525573083/1000000000 : ℝ)*x 0 + (-642644747/5000000000 : ℝ)*x 1 + (5472783241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525573083/1000000000 : ℝ)^5231 ≤ (1404378464059/3125000000000 : ℝ)^4207 := by
    have hnat : (525573083 : ℕ)^5231*3125000000000^4207 ≤ 1404378464059^4207*1000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525573083 1000000000 1404378464059 3125000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642644747/5000000000 : ℝ)^5231 ≤ (7800606305161/100000000000000 : ℝ)^4207 := by
    have hnat : (642644747 : ℕ)^5231*100000000000000^4207 ≤ 7800606305161^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642644747 5000000000 7800606305161 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472783241/10000000000 : ℝ)^5231 ≤ (23629641416339/50000000000000 : ℝ)^4207 := by
    have hnat : (5472783241 : ℕ)^5231*50000000000000^4207 ≤ 23629641416339^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472783241 10000000000 23629641416339 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525573083/1000000000 : ℝ), (-642644747/5000000000 : ℝ), (5472783241/10000000000 : ℝ)] ![(1404378464059/3125000000000 : ℝ), (7800606305161/100000000000000 : ℝ), (23629641416339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525573083/1000000000 : ℝ)|^5231 ≤ (1404378464059/3125000000000 : ℝ)^4207
        have hw : |(525573083/1000000000 : ℝ)|=(525573083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-642644747/5000000000 : ℝ)|^5231 ≤ (7800606305161/100000000000000 : ℝ)^4207
        have hw : |(-642644747/5000000000 : ℝ)|=(642644747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472783241/10000000000 : ℝ)|^5231 ≤ (23629641416339/50000000000000 : ℝ)^4207
        have hw : |(5472783241/10000000000 : ℝ)|=(5472783241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s2_6 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627865411/5000000000 : ℝ)*x 0 + (1368195811/2500000000 : ℝ)*x 1 + (-1285289501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627865411/5000000000 : ℝ)^5231 ≤ (44940110764833/100000000000000 : ℝ)^4207 := by
    have hnat : (2627865411 : ℕ)^5231*100000000000000^4207 ≤ 44940110764833^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627865411 5000000000 44940110764833 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368195811/2500000000 : ℝ)^5231 ≤ (47259282864889/100000000000000 : ℝ)^4207 := by
    have hnat : (1368195811 : ℕ)^5231*100000000000000^4207 ≤ 47259282864889^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368195811 2500000000 47259282864889 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285289501/10000000000 : ℝ)^5231 ≤ (3900303178993/50000000000000 : ℝ)^4207 := by
    have hnat : (1285289501 : ℕ)^5231*50000000000000^4207 ≤ 3900303178993^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285289501 10000000000 3900303178993 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627865411/5000000000 : ℝ), (1368195811/2500000000 : ℝ), (-1285289501/10000000000 : ℝ)] ![(44940110764833/100000000000000 : ℝ), (47259282864889/100000000000000 : ℝ), (3900303178993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627865411/5000000000 : ℝ)|^5231 ≤ (44940110764833/100000000000000 : ℝ)^4207
        have hw : |(2627865411/5000000000 : ℝ)|=(2627865411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368195811/2500000000 : ℝ)|^5231 ≤ (47259282864889/100000000000000 : ℝ)^4207
        have hw : |(1368195811/2500000000 : ℝ)|=(1368195811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1285289501/10000000000 : ℝ)|^5231 ≤ (3900303178993/50000000000000 : ℝ)^4207
        have hw : |(-1285289501/10000000000 : ℝ)|=(1285289501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s2_7 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4116746531/10000000000 : ℝ)*x 0 + (287932989/625000000 : ℝ)*x 1 + (1831267349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116746531/10000000000 : ℝ)^5231 ≤ (8292302325093/25000000000000 : ℝ)^4207 := by
    have hnat : (4116746531 : ℕ)^5231*25000000000000^4207 ≤ 8292302325093^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116746531 10000000000 8292302325093 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287932989/625000000 : ℝ)^5231 ≤ (38149113374699/100000000000000 : ℝ)^4207 := by
    have hnat : (287932989 : ℕ)^5231*100000000000000^4207 ≤ 38149113374699^4207*625000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287932989 625000000 38149113374699 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1831267349/5000000000 : ℝ)^5231 ≤ (14340838657571/50000000000000 : ℝ)^4207 := by
    have hnat : (1831267349 : ℕ)^5231*50000000000000^4207 ≤ 14340838657571^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831267349 5000000000 14340838657571 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116746531/10000000000 : ℝ), (287932989/625000000 : ℝ), (1831267349/5000000000 : ℝ)] ![(8292302325093/25000000000000 : ℝ), (38149113374699/100000000000000 : ℝ), (14340838657571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116746531/10000000000 : ℝ)|^5231 ≤ (8292302325093/25000000000000 : ℝ)^4207
        have hw : |(4116746531/10000000000 : ℝ)|=(4116746531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287932989/625000000 : ℝ)|^5231 ≤ (38149113374699/100000000000000 : ℝ)^4207
        have hw : |(287932989/625000000 : ℝ)|=(287932989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1831267349/5000000000 : ℝ)|^5231 ≤ (14340838657571/50000000000000 : ℝ)^4207
        have hw : |(1831267349/5000000000 : ℝ)|=(1831267349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1701_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4383/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9609/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9921/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17173/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4383/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9609/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4383/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9609/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4383/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9609/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4383/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9609/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4383/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9609/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4383/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9609/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9609/100000 : ℝ) ^ (5223/1024 : ℝ) ≤ (64723605071887/10000000000000000000 : ℝ) := by
    have hpowers : (9609/100000 : ℝ)^5223 ≤ (64723605071887/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9609 : ℕ)^5223*10000000000000000000^1024 ≤ 64723605071887^1024*100000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9609 100000 64723605071887 10000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9609/100000 : ℝ)) (X := (64723605071887/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4383/25000 : ℝ) ^ (5223/1024 : ℝ) ≤ (6951321784280839/50000000000000000000 : ℝ) := by
    have hpowers : (4383/25000 : ℝ)^5223 ≤ (6951321784280839/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4383 : ℕ)^5223*50000000000000000000^1024 ≤ 6951321784280839^1024*25000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4383 25000 6951321784280839 50000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4383/25000 : ℝ)) (X := (6951321784280839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000064723605071887/5000000000000000000 : ℝ) ≤ (5000012689379041/5000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (5000064723605071887/5000000000000000000 : ℝ)^1024 ≤ (5000012689379041/5000000000000000 : ℝ)^5223 := by
      have hnat : (5000064723605071887 : ℕ)^1024*5000000000000000^5223 ≤ 5000012689379041^5223*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000064723605071887 5000000000000000000 5000012689379041 5000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000012689379041/5000000000000000 : ℝ)) (X := (5000064723605071887/5000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003637469904820137/25000000000000000000 : ℝ) ≤ (2000057048460319/2000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (25003637469904820137/25000000000000000000 : ℝ)^1024 ≤ (2000057048460319/2000000000000000 : ℝ)^5223 := by
      have hnat : (25003637469904820137 : ℕ)^1024*2000000000000000^5223 ≤ 2000057048460319^5223*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003637469904820137 25000000000000000000 2000057048460319 2000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000057048460319/2000000000000000 : ℝ)) (X := (25003637469904820137/25000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006951321784280839/25000000000000000000 : ℝ) ≤ (2500136276461277/2500000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (25006951321784280839/25000000000000000000 : ℝ)^1024 ≤ (2500136276461277/2500000000000000 : ℝ)^5223 := by
      have hnat : (25006951321784280839 : ℕ)^1024*2500000000000000^5223 ≤ 2500136276461277^5223*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006951321784280839 25000000000000000000 2500136276461277 2500000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500136276461277/2500000000000000 : ℝ)) (X := (25006951321784280839/25000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(64723605071887/10000000000000000000 : ℝ) ≤ ((6602100584860087571/6602500000000000000 : ℝ)+2*(86621181171/264100000000000 : ℝ)*(9609/100000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (6602100584860087571/6602500000000000000 : ℝ)+2*(86621181171/264100000000000 : ℝ)*(9609/100000 : ℝ)=(5000012689379041/5000000000000000 : ℝ) by norm_num, show 1+2*(64723605071887/10000000000000000000 : ℝ)=(5000064723605071887/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6951321784280839/50000000000000000000 : ℝ)+(64723605071887/10000000000000000000 : ℝ) ≤ ((6602100584860087571/6602500000000000000 : ℝ)+(86621181171/264100000000000 : ℝ)*((4383/25000 : ℝ)+(9609/100000 : ℝ)))^(5223/1024 : ℝ) := by
    rw [show (6602100584860087571/6602500000000000000 : ℝ)+(86621181171/264100000000000 : ℝ)*((4383/25000 : ℝ)+(9609/100000 : ℝ))=(2000057048460319/2000000000000000 : ℝ) by norm_num, show 1+(6951321784280839/50000000000000000000 : ℝ)+(64723605071887/10000000000000000000 : ℝ)=(25003637469904820137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6951321784280839/50000000000000000000 : ℝ) ≤ ((6602100584860087571/6602500000000000000 : ℝ)+2*(86621181171/264100000000000 : ℝ)*(4383/25000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (6602100584860087571/6602500000000000000 : ℝ)+2*(86621181171/264100000000000 : ℝ)*(4383/25000 : ℝ)=(2500136276461277/2500000000000000 : ℝ) by norm_num, show 1+2*(6951321784280839/50000000000000000000 : ℝ)=(25006951321784280839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6602100584860087571/6602500000000000000 : ℝ)*(X 1 0+X 2 0)+(86621181171/264100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (9609/100000 : ℝ)) (hi := (4383/25000 : ℝ)) (c := (6602100584860087571/6602500000000000000 : ℝ)) (alpha := (86621181171/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6602100584860087571/6602500000000000000 : ℝ)*(X 0 1+X 2 1)+(86621181171/264100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (9609/100000 : ℝ)) (hi := (4383/25000 : ℝ)) (c := (6602100584860087571/6602500000000000000 : ℝ)) (alpha := (86621181171/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6602100584860087571/6602500000000000000 : ℝ)*(X 0 2+X 1 2)+(86621181171/264100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (9609/100000 : ℝ)) (hi := (4383/25000 : ℝ)) (c := (6602100584860087571/6602500000000000000 : ℝ)) (alpha := (86621181171/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1445078593/10000000000 : ℝ)*X 0 0+(684573893/1250000000 : ℝ)*X 0 1+(5136472931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346740583/10000000000 : ℝ)*X 1 0+(-1621599421/10000000000 : ℝ)*X 1 1+(256823657/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346740347/10000000000 : ℝ)*X 2 0+(1284118271/2500000000 : ℝ)*X 2 1+(-162159981/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((823260059/2000000000 : ℝ)*X 0 0+(73034411/200000000 : ℝ)*X 0 1+(230879109/500000000 : ℝ)*X 0 2+(823260059/2000000000 : ℝ)*X 1 0+(73034411/200000000 : ℝ)*X 1 1+(230879109/500000000 : ℝ)*X 1 2+(823260059/2000000000 : ℝ)*X 2 0+(73034411/200000000 : ℝ)*X 2 1+(230879109/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-361308889/2500000000 : ℝ)*X 0 0+(1285056197/2500000000 : ℝ)*X 0 1+(2736391621/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525573083/1000000000 : ℝ)*X 1 0+(-642644747/5000000000 : ℝ)*X 1 1+(5472783241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627865411/5000000000 : ℝ)*X 2 0+(1368195811/2500000000 : ℝ)*X 2 1+(-1285289501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4116746531/10000000000 : ℝ)*X 0 0+(287932989/625000000 : ℝ)*X 0 1+(1831267349/5000000000 : ℝ)*X 0 2+(4116746531/10000000000 : ℝ)*X 1 0+(287932989/625000000 : ℝ)*X 1 1+(1831267349/5000000000 : ℝ)*X 1 2+(4116746531/10000000000 : ℝ)*X 2 0+(287932989/625000000 : ℝ)*X 2 1+(1831267349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3192162930195612869952754899/330125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101923089/6250000000000 : ℝ)*(base19) + (1500934409/100000000000000 : ℝ)*(base23) + (31023/100000000000000 : ℝ)*(lower2) + (7548127/2000000000000 : ℝ)*(upper3) + (29164197/25000000000000 : ℝ)*(upper5) + (1987772598612523/100000000000000 : ℝ)*(major0) + (1987772598612523/100000000000000 : ℝ)*(major1) + (1987772598612523/100000000000000 : ℝ)*(major2) + (735043355266181/25000000000000 : ℝ)*(sp0) + (735046494689729/25000000000000 : ℝ)*(sp1) + (735046527148483/25000000000000 : ℝ)*(sp2) + (517675201420723/50000000000000 : ℝ)*(sp3) + (27711843/195312500000 : ℝ)*(sp4) + (3431268323/50000000000000 : ℝ)*(sp7) + (258839316344523/25000000000000 : ℝ)*(f.failure) + (147009380476417/5000000000000 : ℝ)*(f.sum) + (28422010277993/13205000000000000000000000000 : ℝ)*base65 + (2001847334708923367/660250000000000000000000000000000 : ℝ)*base68 + (213084733272076633/660250000000000000000000000000000 : ℝ)*base69 + (3139470204257923367/660250000000000000000000000000000 : ℝ)*base72 + (30066212203007/13205000000000000000000000000 : ℝ)*base74 + (3400106779651076633/660250000000000000000000000000000 : ℝ)*base75 + (1497749584011923367/660250000000000000000000000000000 : ℝ)*base78 + (8403108828704923367/660250000000000000000000000000000 : ℝ)*base80 + (6307537355493/13205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (290549/625000000000000000000 : ℝ)*base89 + (290549/625000000000000000000 : ℝ)*base91 + (290549/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (580575053111255555646137709/41265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195377329/10000000000000 : ℝ)*(base19) + (2108586163/100000000000000 : ℝ)*(base23) + (59582099/20000000000000 : ℝ)*(upper3) + (36275181/50000000000000 : ℝ)*(lower4) + (74137731/25000000000000 : ℝ)*(upper5) + (508233816708393/25000000000000 : ℝ)*(major0) + (508233816708393/25000000000000 : ℝ)*(major1) + (508233816708393/25000000000000 : ℝ)*(major2) + (8716721899/50000000000000 : ℝ)*(sp1) + (9333201521/50000000000000 : ℝ)*(sp2) + (375873654368761/12500000000000 : ℝ)*(sp4) + (3006969847733/100000000000 : ℝ)*(sp5) + (1503484229980441/50000000000000 : ℝ)*(sp6) + (264720207435783/25000000000000 : ℝ)*(sp7) + (264720207435783/25000000000000 : ℝ)*(f.failure) + (375873654368761/12500000000000 : ℝ)*(f.sum) + (7300138502851/1650625000000000000000000000 : ℝ)*base66 + (620128564206241597/165062500000000000000000000000000 : ℝ)*base68 + (1701111870338741597/165062500000000000000000000000000 : ℝ)*base70 + (2299909084092116597/165062500000000000000000000000000 : ℝ)*base72 + (17844796185881/6602500000000000000000000000 : ℝ)*base73 + (1380298611137741597/165062500000000000000000000000000 : ℝ)*base76 + (408622355623616597/165062500000000000000000000000000 : ℝ)*base78 + (708063118526758403/165062500000000000000000000000000 : ℝ)*base79 + (24988991388579/6602500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7261929/625000000000000000000 : ℝ)*base89 + (7261929/625000000000000000000 : ℝ)*base91 + (7261929/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1701_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4383/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9609/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9921/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17173/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1701_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1701_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9921/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17173/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1701_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1701_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1701_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9921/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17173/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1701_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
