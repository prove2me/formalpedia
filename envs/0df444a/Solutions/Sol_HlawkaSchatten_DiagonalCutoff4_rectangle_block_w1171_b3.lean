-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:45:23.744186+00:00
-- url     : https://prove2.me/submissions/80d854b9-c015-455b-a180-f6a1e48c6cd9

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
theorem support_rectangle_w1171_box_0 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013575441/5000000000 : ℝ)*x 0 + (5375893307/10000000000 : ℝ)*x 1 + (67198663/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013575441/5000000000 : ℝ)^2091 ≤ (604101380767/5000000000000 : ℝ)^1579 := by
    have hnat : (1013575441 : ℕ)^2091*5000000000000^1579 ≤ 604101380767^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013575441 5000000000 604101380767 5000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375893307/10000000000 : ℝ)^2091 ≤ (5494873453847/12500000000000 : ℝ)^1579 := by
    have hnat : (5375893307 : ℕ)^2091*12500000000000^1579 ≤ 5494873453847^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375893307 10000000000 5494873453847 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67198663/125000000 : ℝ)^2091 ≤ (21979492369781/50000000000000 : ℝ)^1579 := by
    have hnat : (67198663 : ℕ)^2091*50000000000000^1579 ≤ 21979492369781^1579*125000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67198663 125000000 21979492369781 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013575441/5000000000 : ℝ), (5375893307/10000000000 : ℝ), (67198663/125000000 : ℝ)] ![(604101380767/5000000000000 : ℝ), (5494873453847/12500000000000 : ℝ), (21979492369781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013575441/5000000000 : ℝ)|^2091 ≤ (604101380767/5000000000000 : ℝ)^1579
        have hw : |(-1013575441/5000000000 : ℝ)|=(1013575441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375893307/10000000000 : ℝ)|^2091 ≤ (5494873453847/12500000000000 : ℝ)^1579
        have hw : |(5375893307/10000000000 : ℝ)|=(5375893307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67198663/125000000 : ℝ)|^2091 ≤ (21979492369781/50000000000000 : ℝ)^1579
        have hw : |(67198663/125000000 : ℝ)|=(67198663/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_1 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20688451/39062500 : ℝ)*x 0 + (-2135240877/10000000000 : ℝ)*x 1 + (5375893083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20688451/39062500 : ℝ)^2091 ≤ (43098576690961/100000000000000 : ℝ)^1579 := by
    have hnat : (20688451 : ℕ)^2091*100000000000000^1579 ≤ 43098576690961^1579*39062500^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20688451 39062500 43098576690961 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135240877/10000000000 : ℝ)^2091 ≤ (12942438083623/100000000000000 : ℝ)^1579 := by
    have hnat : (2135240877 : ℕ)^2091*100000000000000^1579 ≤ 12942438083623^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135240877 10000000000 12942438083623 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375893083/10000000000 : ℝ)^2091 ≤ (10989746301297/25000000000000 : ℝ)^1579 := by
    have hnat : (5375893083 : ℕ)^2091*25000000000000^1579 ≤ 10989746301297^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375893083 10000000000 10989746301297 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20688451/39062500 : ℝ), (-2135240877/10000000000 : ℝ), (5375893083/10000000000 : ℝ)] ![(43098576690961/100000000000000 : ℝ), (12942438083623/100000000000000 : ℝ), (10989746301297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20688451/39062500 : ℝ)|^2091 ≤ (43098576690961/100000000000000 : ℝ)^1579
        have hw : |(20688451/39062500 : ℝ)|=(20688451/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135240877/10000000000 : ℝ)|^2091 ≤ (12942438083623/100000000000000 : ℝ)^1579
        have hw : |(-2135240877/10000000000 : ℝ)|=(2135240877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375893083/10000000000 : ℝ)|^2091 ≤ (10989746301297/25000000000000 : ℝ)^1579
        have hw : |(5375893083/10000000000 : ℝ)|=(5375893083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_2 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (52962439/100000000 : ℝ)*x 0 + (5375892859/10000000000 : ℝ)*x 1 + (-266905073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52962439/100000000 : ℝ)^2091 ≤ (43098581475607/100000000000000 : ℝ)^1579 := by
    have hnat : (52962439 : ℕ)^2091*100000000000000^1579 ≤ 43098581475607^1579*100000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52962439 100000000 43098581475607 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375892859/10000000000 : ℝ)^2091 ≤ (43958982779601/100000000000000 : ℝ)^1579 := by
    have hnat : (5375892859 : ℕ)^2091*100000000000000^1579 ≤ 43958982779601^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375892859 10000000000 43958982779601 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266905073/1250000000 : ℝ)^2091 ≤ (6471217865889/50000000000000 : ℝ)^1579 := by
    have hnat : (266905073 : ℕ)^2091*50000000000000^1579 ≤ 6471217865889^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266905073 1250000000 6471217865889 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52962439/100000000 : ℝ), (5375892859/10000000000 : ℝ), (-266905073/1250000000 : ℝ)] ![(43098581475607/100000000000000 : ℝ), (43958982779601/100000000000000 : ℝ), (6471217865889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52962439/100000000 : ℝ)|^2091 ≤ (43098581475607/100000000000000 : ℝ)^1579
        have hw : |(52962439/100000000 : ℝ)|=(52962439/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375892859/10000000000 : ℝ)|^2091 ≤ (43958982779601/100000000000000 : ℝ)^1579
        have hw : |(5375892859/10000000000 : ℝ)|=(5375892859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266905073/1250000000 : ℝ)|^2091 ≤ (6471217865889/50000000000000 : ℝ)^1579
        have hw : |(-266905073/1250000000 : ℝ)|=(266905073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_3 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2233923367/5000000000 : ℝ)*x 0 + (4309073349/10000000000 : ℝ)*x 1 + (4309074029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2233923367/5000000000 : ℝ)^2091 ≤ (8601626652801/25000000000000 : ℝ)^1579 := by
    have hnat : (2233923367 : ℕ)^2091*25000000000000^1579 ≤ 8601626652801^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233923367 5000000000 8601626652801 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4309073349/10000000000 : ℝ)^2091 ≤ (1024898226973/3125000000000 : ℝ)^1579 := by
    have hnat : (4309073349 : ℕ)^2091*3125000000000^1579 ≤ 1024898226973^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309073349 10000000000 1024898226973 3125000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4309074029/10000000000 : ℝ)^2091 ≤ (32796750116877/100000000000000 : ℝ)^1579 := by
    have hnat : (4309074029 : ℕ)^2091*100000000000000^1579 ≤ 32796750116877^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309074029 10000000000 32796750116877 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2233923367/5000000000 : ℝ), (4309073349/10000000000 : ℝ), (4309074029/10000000000 : ℝ)] ![(8601626652801/25000000000000 : ℝ), (1024898226973/3125000000000 : ℝ), (32796750116877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2233923367/5000000000 : ℝ)|^2091 ≤ (8601626652801/25000000000000 : ℝ)^1579
        have hw : |(2233923367/5000000000 : ℝ)|=(2233923367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4309073349/10000000000 : ℝ)|^2091 ≤ (1024898226973/3125000000000 : ℝ)^1579
        have hw : |(4309073349/10000000000 : ℝ)|=(4309073349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4309074029/10000000000 : ℝ)|^2091 ≤ (32796750116877/100000000000000 : ℝ)^1579
        have hw : |(4309074029/10000000000 : ℝ)|=(4309074029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_4 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-570107327/2500000000 : ℝ)*x 0 + (5281498313/10000000000 : ℝ)*x 1 + (1056299813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (570107327/2500000000 : ℝ)^2091 ≤ (2824097821549/20000000000000 : ℝ)^1579 := by
    have hnat : (570107327 : ℕ)^2091*20000000000000^1579 ≤ 2824097821549^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570107327 2500000000 2824097821549 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281498313/10000000000 : ℝ)^2091 ≤ (42939751391993/100000000000000 : ℝ)^1579 := by
    have hnat : (5281498313 : ℕ)^2091*100000000000000^1579 ≤ 42939751391993^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281498313 10000000000 42939751391993 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056299813/2000000000 : ℝ)^2091 ≤ (10734939872099/25000000000000 : ℝ)^1579 := by
    have hnat : (1056299813 : ℕ)^2091*25000000000000^1579 ≤ 10734939872099^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056299813 2000000000 10734939872099 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-570107327/2500000000 : ℝ), (5281498313/10000000000 : ℝ), (1056299813/2000000000 : ℝ)] ![(2824097821549/20000000000000 : ℝ), (42939751391993/100000000000000 : ℝ), (10734939872099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-570107327/2500000000 : ℝ)|^2091 ≤ (2824097821549/20000000000000 : ℝ)^1579
        have hw : |(-570107327/2500000000 : ℝ)|=(570107327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281498313/10000000000 : ℝ)|^2091 ≤ (42939751391993/100000000000000 : ℝ)^1579
        have hw : |(5281498313/10000000000 : ℝ)|=(5281498313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056299813/2000000000 : ℝ)|^2091 ≤ (10734939872099/25000000000000 : ℝ)^1579
        have hw : |(1056299813/2000000000 : ℝ)|=(1056299813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_5 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362889213/10000000000 : ℝ)*x 0 + (-2172457773/10000000000 : ℝ)*x 1 + (5281499251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362889213/10000000000 : ℝ)^2091 ≤ (876364556911/2000000000000 : ℝ)^1579 := by
    have hnat : (5362889213 : ℕ)^2091*2000000000000^1579 ≤ 876364556911^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362889213 10000000000 876364556911 2000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172457773/10000000000 : ℝ)^2091 ≤ (13242010642237/100000000000000 : ℝ)^1579 := by
    have hnat : (2172457773 : ℕ)^2091*100000000000000^1579 ≤ 13242010642237^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172457773 10000000000 13242010642237 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281499251/10000000000 : ℝ)^2091 ≤ (10734940372741/25000000000000 : ℝ)^1579 := by
    have hnat : (5281499251 : ℕ)^2091*25000000000000^1579 ≤ 10734940372741^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281499251 10000000000 10734940372741 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362889213/10000000000 : ℝ), (-2172457773/10000000000 : ℝ), (5281499251/10000000000 : ℝ)] ![(876364556911/2000000000000 : ℝ), (13242010642237/100000000000000 : ℝ), (10734940372741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362889213/10000000000 : ℝ)|^2091 ≤ (876364556911/2000000000000 : ℝ)^1579
        have hw : |(5362889213/10000000000 : ℝ)|=(5362889213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2172457773/10000000000 : ℝ)|^2091 ≤ (13242010642237/100000000000000 : ℝ)^1579
        have hw : |(-2172457773/10000000000 : ℝ)|=(2172457773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281499251/10000000000 : ℝ)|^2091 ≤ (10734940372741/25000000000000 : ℝ)^1579
        have hw : |(5281499251/10000000000 : ℝ)|=(5281499251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_6 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362890667/10000000000 : ℝ)*x 0 + (5281497761/10000000000 : ℝ)*x 1 + (-543114453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362890667/10000000000 : ℝ)^2091 ≤ (43818243577853/100000000000000 : ℝ)^1579 := by
    have hnat : (5362890667 : ℕ)^2091*100000000000000^1579 ≤ 43818243577853^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362890667 10000000000 43818243577853 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281497761/10000000000 : ℝ)^2091 ≤ (42939745448889/100000000000000 : ℝ)^1579 := by
    have hnat : (5281497761 : ℕ)^2091*100000000000000^1579 ≤ 42939745448889^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281497761 10000000000 42939745448889 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543114453/2500000000 : ℝ)^2091 ≤ (165525136963/1250000000000 : ℝ)^1579 := by
    have hnat : (543114453 : ℕ)^2091*1250000000000^1579 ≤ 165525136963^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543114453 2500000000 165525136963 1250000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362890667/10000000000 : ℝ), (5281497761/10000000000 : ℝ), (-543114453/2500000000 : ℝ)] ![(43818243577853/100000000000000 : ℝ), (42939745448889/100000000000000 : ℝ), (165525136963/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362890667/10000000000 : ℝ)|^2091 ≤ (43818243577853/100000000000000 : ℝ)^1579
        have hw : |(5362890667/10000000000 : ℝ)|=(5362890667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281497761/10000000000 : ℝ)|^2091 ≤ (42939745448889/100000000000000 : ℝ)^1579
        have hw : |(5281497761/10000000000 : ℝ)|=(5281497761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-543114453/2500000000 : ℝ)|^2091 ≤ (165525136963/1250000000000 : ℝ)^1579
        have hw : |(-543114453/2500000000 : ℝ)|=(543114453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_7 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4252991277/10000000000 : ℝ)*x 0 + (4416480469/10000000000 : ℝ)*x 1 + (2208240563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252991277/10000000000 : ℝ)^2091 ≤ (4029085827643/12500000000000 : ℝ)^1579 := by
    have hnat : (4252991277 : ℕ)^2091*12500000000000^1579 ≤ 4029085827643^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252991277 10000000000 4029085827643 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416480469/10000000000 : ℝ)^2091 ≤ (33883653340883/100000000000000 : ℝ)^1579 := by
    have hnat : (4416480469 : ℕ)^2091*100000000000000^1579 ≤ 33883653340883^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416480469 10000000000 33883653340883 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208240563/5000000000 : ℝ)^2091 ≤ (16941830007941/50000000000000 : ℝ)^1579 := by
    have hnat : (2208240563 : ℕ)^2091*50000000000000^1579 ≤ 16941830007941^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208240563 5000000000 16941830007941 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252991277/10000000000 : ℝ), (4416480469/10000000000 : ℝ), (2208240563/5000000000 : ℝ)] ![(4029085827643/12500000000000 : ℝ), (33883653340883/100000000000000 : ℝ), (16941830007941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252991277/10000000000 : ℝ)|^2091 ≤ (4029085827643/12500000000000 : ℝ)^1579
        have hw : |(4252991277/10000000000 : ℝ)|=(4252991277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416480469/10000000000 : ℝ)|^2091 ≤ (33883653340883/100000000000000 : ℝ)^1579
        have hw : |(4416480469/10000000000 : ℝ)|=(4416480469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208240563/5000000000 : ℝ)|^2091 ≤ (16941830007941/50000000000000 : ℝ)^1579
        have hw : |(2208240563/5000000000 : ℝ)|=(2208240563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_8 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1113716001/5000000000 : ℝ)*x 0 + (81519469/156250000 : ℝ)*x 1 + (2692751951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113716001/5000000000 : ℝ)^2091 ≤ (3421891519973/25000000000000 : ℝ)^1579 := by
    have hnat : (1113716001 : ℕ)^2091*25000000000000^1579 ≤ 3421891519973^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113716001 5000000000 3421891519973 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81519469/156250000 : ℝ)^2091 ≤ (21124673822223/50000000000000 : ℝ)^1579 := by
    have hnat : (81519469 : ℕ)^2091*50000000000000^1579 ≤ 21124673822223^1579*156250000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81519469 156250000 21124673822223 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692751951/5000000000 : ℝ)^2091 ≤ (44063086263871/100000000000000 : ℝ)^1579 := by
    have hnat : (2692751951 : ℕ)^2091*100000000000000^1579 ≤ 44063086263871^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692751951 5000000000 44063086263871 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1113716001/5000000000 : ℝ), (81519469/156250000 : ℝ), (2692751951/5000000000 : ℝ)] ![(3421891519973/25000000000000 : ℝ), (21124673822223/50000000000000 : ℝ), (44063086263871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1113716001/5000000000 : ℝ)|^2091 ≤ (3421891519973/25000000000000 : ℝ)^1579
        have hw : |(-1113716001/5000000000 : ℝ)|=(1113716001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81519469/156250000 : ℝ)|^2091 ≤ (21124673822223/50000000000000 : ℝ)^1579
        have hw : |(81519469/156250000 : ℝ)|=(81519469/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692751951/5000000000 : ℝ)|^2091 ≤ (44063086263871/100000000000000 : ℝ)^1579
        have hw : |(2692751951/5000000000 : ℝ)|=(2692751951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_9 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289454523/10000000000 : ℝ)*x 0 + (-426276597/2000000000 : ℝ)*x 1 + (5385503921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289454523/10000000000 : ℝ)^2091 ≤ (5378179098687/12500000000000 : ℝ)^1579 := by
    have hnat : (5289454523 : ℕ)^2091*12500000000000^1579 ≤ 5378179098687^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289454523 10000000000 5378179098687 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426276597/2000000000 : ℝ)^2091 ≤ (645574036237/5000000000000 : ℝ)^1579 := by
    have hnat : (426276597 : ℕ)^2091*5000000000000^1579 ≤ 645574036237^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426276597 2000000000 645574036237 5000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385503921/10000000000 : ℝ)^2091 ≤ (11015771617433/25000000000000 : ℝ)^1579 := by
    have hnat : (5385503921 : ℕ)^2091*25000000000000^1579 ≤ 11015771617433^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385503921 10000000000 11015771617433 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289454523/10000000000 : ℝ), (-426276597/2000000000 : ℝ), (5385503921/10000000000 : ℝ)] ![(5378179098687/12500000000000 : ℝ), (645574036237/5000000000000 : ℝ), (11015771617433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289454523/10000000000 : ℝ)|^2091 ≤ (5378179098687/12500000000000 : ℝ)^1579
        have hw : |(5289454523/10000000000 : ℝ)|=(5289454523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426276597/2000000000 : ℝ)|^2091 ≤ (645574036237/5000000000000 : ℝ)^1579
        have hw : |(-426276597/2000000000 : ℝ)|=(426276597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385503921/10000000000 : ℝ)|^2091 ≤ (11015771617433/25000000000000 : ℝ)^1579
        have hw : |(5385503921/10000000000 : ℝ)|=(5385503921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_10 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1322363639/2500000000 : ℝ)*x 0 + (5385504223/10000000000 : ℝ)*x 1 + (-1065691267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322363639/2500000000 : ℝ)^2091 ≤ (43025433144963/100000000000000 : ℝ)^1579 := by
    have hnat : (1322363639 : ℕ)^2091*100000000000000^1579 ≤ 43025433144963^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322363639 2500000000 43025433144963 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385504223/10000000000 : ℝ)^2091 ≤ (22031544870919/50000000000000 : ℝ)^1579 := by
    have hnat : (5385504223 : ℕ)^2091*50000000000000^1579 ≤ 22031544870919^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385504223 10000000000 22031544870919 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065691267/5000000000 : ℝ)^2091 ≤ (6455738553393/50000000000000 : ℝ)^1579 := by
    have hnat : (1065691267 : ℕ)^2091*50000000000000^1579 ≤ 6455738553393^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065691267 5000000000 6455738553393 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322363639/2500000000 : ℝ), (5385504223/10000000000 : ℝ), (-1065691267/5000000000 : ℝ)] ![(43025433144963/100000000000000 : ℝ), (22031544870919/50000000000000 : ℝ), (6455738553393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322363639/2500000000 : ℝ)|^2091 ≤ (43025433144963/100000000000000 : ℝ)^1579
        have hw : |(1322363639/2500000000 : ℝ)|=(1322363639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385504223/10000000000 : ℝ)|^2091 ≤ (22031544870919/50000000000000 : ℝ)^1579
        have hw : |(5385504223/10000000000 : ℝ)|=(5385504223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065691267/5000000000 : ℝ)|^2091 ≤ (6455738553393/50000000000000 : ℝ)^1579
        have hw : |(-1065691267/5000000000 : ℝ)|=(1065691267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_11 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4489449649/10000000000 : ℝ)*x 0 + (537266451/1250000000 : ℝ)*x 1 + (429813177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489449649/10000000000 : ℝ)^2091 ≤ (34626985251521/100000000000000 : ℝ)^1579 := by
    have hnat : (4489449649 : ℕ)^2091*100000000000000^1579 ≤ 34626985251521^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489449649 10000000000 34626985251521 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537266451/1250000000 : ℝ)^2091 ≤ (16343253277383/50000000000000 : ℝ)^1579 := by
    have hnat : (537266451 : ℕ)^2091*50000000000000^1579 ≤ 16343253277383^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537266451 1250000000 16343253277383 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429813177/1000000000 : ℝ)^2091 ≤ (2042906761639/6250000000000 : ℝ)^1579 := by
    have hnat : (429813177 : ℕ)^2091*6250000000000^1579 ≤ 2042906761639^1579*1000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429813177 1000000000 2042906761639 6250000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489449649/10000000000 : ℝ), (537266451/1250000000 : ℝ), (429813177/1000000000 : ℝ)] ![(34626985251521/100000000000000 : ℝ), (16343253277383/50000000000000 : ℝ), (2042906761639/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489449649/10000000000 : ℝ)|^2091 ≤ (34626985251521/100000000000000 : ℝ)^1579
        have hw : |(4489449649/10000000000 : ℝ)|=(4489449649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537266451/1250000000 : ℝ)|^2091 ≤ (16343253277383/50000000000000 : ℝ)^1579
        have hw : |(537266451/1250000000 : ℝ)|=(537266451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(429813177/1000000000 : ℝ)|^2091 ≤ (2042906761639/6250000000000 : ℝ)^1579
        have hw : |(429813177/1000000000 : ℝ)|=(429813177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_12 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080449897/10000000000 : ℝ)*x 0 + (679861149/1250000000 : ℝ)*x 1 + (5273446617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080449897/10000000000 : ℝ)^2091 ≤ (1563060441261/12500000000000 : ℝ)^1579 := by
    have hnat : (2080449897 : ℕ)^2091*12500000000000^1579 ≤ 1563060441261^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080449897 10000000000 1563060441261 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679861149/1250000000 : ℝ)^2091 ≤ (22321216082129/50000000000000 : ℝ)^1579 := by
    have hnat : (679861149 : ℕ)^2091*50000000000000^1579 ≤ 22321216082129^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679861149 1250000000 22321216082129 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273446617/10000000000 : ℝ)^2091 ≤ (1339158884157/3125000000000 : ℝ)^1579 := by
    have hnat : (5273446617 : ℕ)^2091*3125000000000^1579 ≤ 1339158884157^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273446617 10000000000 1339158884157 3125000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080449897/10000000000 : ℝ), (679861149/1250000000 : ℝ), (5273446617/10000000000 : ℝ)] ![(1563060441261/12500000000000 : ℝ), (22321216082129/50000000000000 : ℝ), (1339158884157/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080449897/10000000000 : ℝ)|^2091 ≤ (1563060441261/12500000000000 : ℝ)^1579
        have hw : |(-2080449897/10000000000 : ℝ)|=(2080449897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679861149/1250000000 : ℝ)|^2091 ≤ (22321216082129/50000000000000 : ℝ)^1579
        have hw : |(679861149/1250000000 : ℝ)|=(679861149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273446617/10000000000 : ℝ)|^2091 ≤ (1339158884157/3125000000000 : ℝ)^1579
        have hw : |(5273446617/10000000000 : ℝ)|=(5273446617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_13 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684286101/5000000000 : ℝ)*x 0 + (-543893811/2500000000 : ℝ)*x 1 + (5273447261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684286101/5000000000 : ℝ)^2091 ≤ (43879728436929/100000000000000 : ℝ)^1579 := by
    have hnat : (2684286101 : ℕ)^2091*100000000000000^1579 ≤ 43879728436929^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684286101 5000000000 43879728436929 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543893811/2500000000 : ℝ)^2091 ≤ (13267180334723/100000000000000 : ℝ)^1579 := by
    have hnat : (543893811 : ℕ)^2091*100000000000000^1579 ≤ 13267180334723^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543893811 2500000000 13267180334723 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273447261/10000000000 : ℝ)^2091 ≤ (42853091223217/100000000000000 : ℝ)^1579 := by
    have hnat : (5273447261 : ℕ)^2091*100000000000000^1579 ≤ 42853091223217^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273447261 10000000000 42853091223217 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684286101/5000000000 : ℝ), (-543893811/2500000000 : ℝ), (5273447261/10000000000 : ℝ)] ![(43879728436929/100000000000000 : ℝ), (13267180334723/100000000000000 : ℝ), (42853091223217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684286101/5000000000 : ℝ)|^2091 ≤ (43879728436929/100000000000000 : ℝ)^1579
        have hw : |(2684286101/5000000000 : ℝ)|=(2684286101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543893811/2500000000 : ℝ)|^2091 ≤ (13267180334723/100000000000000 : ℝ)^1579
        have hw : |(-543893811/2500000000 : ℝ)|=(543893811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273447261/10000000000 : ℝ)|^2091 ≤ (42853091223217/100000000000000 : ℝ)^1579
        have hw : |(5273447261/10000000000 : ℝ)|=(5273447261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_14 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368572571/10000000000 : ℝ)*x 0 + (1054689423/2000000000 : ℝ)*x 1 + (-2175574943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368572571/10000000000 : ℝ)^2091 ≤ (21939866215443/50000000000000 : ℝ)^1579 := by
    have hnat : (5368572571 : ℕ)^2091*50000000000000^1579 ≤ 21939866215443^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368572571 10000000000 21939866215443 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054689423/2000000000 : ℝ)^2091 ≤ (21426544826043/50000000000000 : ℝ)^1579 := by
    have hnat : (1054689423 : ℕ)^2091*50000000000000^1579 ≤ 21426544826043^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054689423 2000000000 21426544826043 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175574943/10000000000 : ℝ)^2091 ≤ (6633588951979/50000000000000 : ℝ)^1579 := by
    have hnat : (2175574943 : ℕ)^2091*50000000000000^1579 ≤ 6633588951979^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175574943 10000000000 6633588951979 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368572571/10000000000 : ℝ), (1054689423/2000000000 : ℝ), (-2175574943/10000000000 : ℝ)] ![(21939866215443/50000000000000 : ℝ), (21426544826043/50000000000000 : ℝ), (6633588951979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368572571/10000000000 : ℝ)|^2091 ≤ (21939866215443/50000000000000 : ℝ)^1579
        have hw : |(5368572571/10000000000 : ℝ)|=(5368572571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054689423/2000000000 : ℝ)|^2091 ≤ (21426544826043/50000000000000 : ℝ)^1579
        have hw : |(1054689423/2000000000 : ℝ)|=(1054689423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175574943/10000000000 : ℝ)|^2091 ≤ (6633588951979/50000000000000 : ℝ)^1579
        have hw : |(-2175574943/10000000000 : ℝ)|=(2175574943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_box_15 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2117216911/5000000000 : ℝ)*x 0 + (2212818509/5000000000 : ℝ)*x 1 + (2212818651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117216911/5000000000 : ℝ)^2091 ≤ (2002910637587/6250000000000 : ℝ)^1579 := by
    have hnat : (2117216911 : ℕ)^2091*6250000000000^1579 ≤ 2002910637587^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117216911 5000000000 2002910637587 6250000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212818509/5000000000 : ℝ)^2091 ≤ (16988356722183/50000000000000 : ℝ)^1579 := by
    have hnat : (2212818509 : ℕ)^2091*50000000000000^1579 ≤ 16988356722183^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212818509 5000000000 16988356722183 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212818651/5000000000 : ℝ)^2091 ≤ (8494179082923/25000000000000 : ℝ)^1579 := by
    have hnat : (2212818651 : ℕ)^2091*25000000000000^1579 ≤ 8494179082923^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212818651 5000000000 8494179082923 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117216911/5000000000 : ℝ), (2212818509/5000000000 : ℝ), (2212818651/5000000000 : ℝ)] ![(2002910637587/6250000000000 : ℝ), (16988356722183/50000000000000 : ℝ), (8494179082923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117216911/5000000000 : ℝ)|^2091 ≤ (2002910637587/6250000000000 : ℝ)^1579
        have hw : |(2117216911/5000000000 : ℝ)|=(2117216911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2212818509/5000000000 : ℝ)|^2091 ≤ (16988356722183/50000000000000 : ℝ)^1579
        have hw : |(2212818509/5000000000 : ℝ)|=(2212818509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212818651/5000000000 : ℝ)|^2091 ≤ (8494179082923/25000000000000 : ℝ)^1579
        have hw : |(2212818651/5000000000 : ℝ)|=(2212818651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1171_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12447/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59321/100000 : ℝ) ∧ (9987/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83189/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11391/100000 : ℝ) ^ (8363/2048 : ℝ) ≤ (14043456306472153/100000000000000000000 : ℝ) := by
    have hpowers : (11391/100000 : ℝ)^8363 ≤ (14043456306472153/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11391 : ℕ)^8363*100000000000000000000^2048 ≤ 14043456306472153^2048*100000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11391 100000 14043456306472153 100000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11391/100000 : ℝ)) (X := (14043456306472153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (8363/2048 : ℝ) ≤ (33222471809654623/100000000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^8363 ≤ (33222471809654623/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2813 : ℕ)^8363*100000000000000000000^2048 ≤ 33222471809654623^2048*20000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 33222471809654623 100000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (33222471809654623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014043456306472153/50000000000000000000 : ℝ) ≤ (10000687742415193/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (50014043456306472153/50000000000000000000 : ℝ)^2048 ≤ (10000687742415193/10000000000000000 : ℝ)^8363 := by
      have hnat : (50014043456306472153 : ℕ)^2048*10000000000000000^8363 ≤ 10000687742415193^8363*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014043456306472153 50000000000000000000 10000687742415193 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000687742415193/10000000000000000 : ℝ)) (X := (50014043456306472153/50000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505908241014515847/12500000000000000000 : ℝ) ≤ (10001157280293833/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (12505908241014515847/12500000000000000000 : ℝ)^2048 ≤ (10001157280293833/10000000000000000 : ℝ)^8363 := by
      have hnat : (12505908241014515847 : ℕ)^2048*10000000000000000^8363 ≤ 10001157280293833^8363*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505908241014515847 12500000000000000000 10001157280293833 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001157280293833/10000000000000000 : ℝ)) (X := (12505908241014515847/12500000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033222471809654623/50000000000000000000 : ℝ) ≤ (10001626818172473/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (50033222471809654623/50000000000000000000 : ℝ)^2048 ≤ (10001626818172473/10000000000000000 : ℝ)^8363 := by
      have hnat : (50033222471809654623 : ℕ)^2048*10000000000000000^8363 ≤ 10001626818172473^8363*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033222471809654623 50000000000000000000 10001626818172473 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001626818172473/10000000000000000 : ℝ)) (X := (50033222471809654623/50000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14043456306472153/100000000000000000000 : ℝ) ≤ ((13365571005633524801/13370000000000000000 : ℝ)+2*(5869223483/3342500000000 : ℝ)*(11391/100000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (13365571005633524801/13370000000000000000 : ℝ)+2*(5869223483/3342500000000 : ℝ)*(11391/100000 : ℝ)=(10000687742415193/10000000000000000 : ℝ) by norm_num, show 1+2*(14043456306472153/100000000000000000000 : ℝ)=(50014043456306472153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33222471809654623/100000000000000000000 : ℝ)+(14043456306472153/100000000000000000000 : ℝ) ≤ ((13365571005633524801/13370000000000000000 : ℝ)+(5869223483/3342500000000 : ℝ)*((2813/20000 : ℝ)+(11391/100000 : ℝ)))^(8363/2048 : ℝ) := by
    rw [show (13365571005633524801/13370000000000000000 : ℝ)+(5869223483/3342500000000 : ℝ)*((2813/20000 : ℝ)+(11391/100000 : ℝ))=(10001157280293833/10000000000000000 : ℝ) by norm_num, show 1+(33222471809654623/100000000000000000000 : ℝ)+(14043456306472153/100000000000000000000 : ℝ)=(12505908241014515847/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33222471809654623/100000000000000000000 : ℝ) ≤ ((13365571005633524801/13370000000000000000 : ℝ)+2*(5869223483/3342500000000 : ℝ)*(2813/20000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (13365571005633524801/13370000000000000000 : ℝ)+2*(5869223483/3342500000000 : ℝ)*(2813/20000 : ℝ)=(10001626818172473/10000000000000000 : ℝ) by norm_num, show 1+2*(33222471809654623/100000000000000000000 : ℝ)=(50033222471809654623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13365571005633524801/13370000000000000000 : ℝ)*(X 1 0+X 2 0)+(5869223483/3342500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (13365571005633524801/13370000000000000000 : ℝ)) (alpha := (5869223483/3342500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13365571005633524801/13370000000000000000 : ℝ)*(X 0 1+X 2 1)+(5869223483/3342500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (13365571005633524801/13370000000000000000 : ℝ)) (alpha := (5869223483/3342500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13365571005633524801/13370000000000000000 : ℝ)*(X 0 2+X 1 2)+(5869223483/3342500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (13365571005633524801/13370000000000000000 : ℝ)) (alpha := (5869223483/3342500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1013575441/5000000000 : ℝ)*X 0 0+(5375893307/10000000000 : ℝ)*X 0 1+(67198663/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20688451/39062500 : ℝ)*X 1 0+(-2135240877/10000000000 : ℝ)*X 1 1+(5375893083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((52962439/100000000 : ℝ)*X 2 0+(5375892859/10000000000 : ℝ)*X 2 1+(-266905073/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2233923367/5000000000 : ℝ)*X 0 0+(4309073349/10000000000 : ℝ)*X 0 1+(4309074029/10000000000 : ℝ)*X 0 2+(2233923367/5000000000 : ℝ)*X 1 0+(4309073349/10000000000 : ℝ)*X 1 1+(4309074029/10000000000 : ℝ)*X 1 2+(2233923367/5000000000 : ℝ)*X 2 0+(4309073349/10000000000 : ℝ)*X 2 1+(4309074029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-570107327/2500000000 : ℝ)*X 0 0+(5281498313/10000000000 : ℝ)*X 0 1+(1056299813/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362889213/10000000000 : ℝ)*X 1 0+(-2172457773/10000000000 : ℝ)*X 1 1+(5281499251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362890667/10000000000 : ℝ)*X 2 0+(5281497761/10000000000 : ℝ)*X 2 1+(-543114453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4252991277/10000000000 : ℝ)*X 0 0+(4416480469/10000000000 : ℝ)*X 0 1+(2208240563/5000000000 : ℝ)*X 0 2+(4252991277/10000000000 : ℝ)*X 1 0+(4416480469/10000000000 : ℝ)*X 1 1+(2208240563/5000000000 : ℝ)*X 1 2+(4252991277/10000000000 : ℝ)*X 2 0+(4416480469/10000000000 : ℝ)*X 2 1+(2208240563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1113716001/5000000000 : ℝ)*X 0 0+(81519469/156250000 : ℝ)*X 0 1+(2692751951/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289454523/10000000000 : ℝ)*X 1 0+(-426276597/2000000000 : ℝ)*X 1 1+(5385503921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322363639/2500000000 : ℝ)*X 2 0+(5385504223/10000000000 : ℝ)*X 2 1+(-1065691267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4489449649/10000000000 : ℝ)*X 0 0+(537266451/1250000000 : ℝ)*X 0 1+(429813177/1000000000 : ℝ)*X 0 2+(4489449649/10000000000 : ℝ)*X 1 0+(537266451/1250000000 : ℝ)*X 1 1+(429813177/1000000000 : ℝ)*X 1 2+(4489449649/10000000000 : ℝ)*X 2 0+(537266451/1250000000 : ℝ)*X 2 1+(429813177/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2080449897/10000000000 : ℝ)*X 0 0+(679861149/1250000000 : ℝ)*X 0 1+(5273446617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684286101/5000000000 : ℝ)*X 1 0+(-543893811/2500000000 : ℝ)*X 1 1+(5273447261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368572571/10000000000 : ℝ)*X 2 0+(1054689423/2000000000 : ℝ)*X 2 1+(-2175574943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2117216911/5000000000 : ℝ)*X 0 0+(2212818509/5000000000 : ℝ)*X 0 1+(2212818651/5000000000 : ℝ)*X 0 2+(2117216911/5000000000 : ℝ)*X 1 0+(2212818509/5000000000 : ℝ)*X 1 1+(2212818651/5000000000 : ℝ)*X 1 2+(2117216911/5000000000 : ℝ)*X 2 0+(2212818509/5000000000 : ℝ)*X 2 1+(2212818651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12447/20000 : ℝ) ≤ (-4160232528982274901087088164387/6685000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4444473/100000000000000 : ℝ)*(upper0) + (149579953/100000000000000 : ℝ)*(lower2) + (125144301/50000000000000 : ℝ)*(lower3) + (240222481/100000000000000 : ℝ)*(upper5) + (1972284133553551/50000000000000 : ℝ)*(major0) + (1972284133553551/50000000000000 : ℝ)*(major1) + (123267758347097/3125000000000 : ℝ)*(major2) + (27929515153/50000000000000 : ℝ)*(sp2) + (478443957/12500000000000 : ℝ)*(sp3) + (2640433439369833/50000000000000 : ℝ)*(sp4) + (528043405067343/10000000000000 : ℝ)*(sp5) + (66010137746367/1250000000000 : ℝ)*(sp6) + (164313121515493/6250000000000 : ℝ)*(sp7) + (108207016559/25000000000000 : ℝ)*(sp13) + (328626721474943/12500000000000 : ℝ)*(f.failure) + (2640433439369833/50000000000000 : ℝ)*(f.sum) + (174670500199/41781250000000000000000000 : ℝ)*base65 + (4806807774984881649/668500000000000000000000000000000 : ℝ)*base68 + (182859847059290197/41781250000000000000000000000000 : ℝ)*base69 + (4636706524742881649/668500000000000000000000000000000 : ℝ)*base72 + (14384350963481/668500000000000000000000000 : ℝ)*base74 + (249961861698915197/41781250000000000000000000000000 : ℝ)*base75 + (1135245930147881649/668500000000000000000000000000000 : ℝ)*base78 + (33479216070902881649/668500000000000000000000000000000 : ℝ)*base80 + (103907450641/167125000000000000000000000 : ℝ)*base82 + (1066083/156250000000000000000 : ℝ)*base89 + (1066083/156250000000000000000 : ℝ)*base91 + (2058917/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59321/100000 : ℝ) ≤ (396577380990589152625678332151311/668500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26669369/50000000000000 : ℝ)*(upper0) + (131121873/50000000000000 : ℝ)*(lower1) + (274100223/100000000000000 : ℝ)*(upper4) + (163297/20000000000000 : ℝ)*(upper5) + (1002297102974403/25000000000000 : ℝ)*(major0) + (1002297102974403/25000000000000 : ℝ)*(major1) + (4009188411897613/100000000000000 : ℝ)*(major2) + (2663259953798129/50000000000000 : ℝ)*(sp0) + (1065254175308587/20000000000000 : ℝ)*(sp1) + (2663163138278997/50000000000000 : ℝ)*(sp2) + (2672081431447699/100000000000000 : ℝ)*(sp3) + (497773519/50000000000000 : ℝ)*(sp7) + (249031053323/100000000000000 : ℝ)*(sp9) + (24203879783/12500000000000 : ℝ)*(sp10) + (167005151687171/6250000000000 : ℝ)*(f.failure) + (2663259953798129/50000000000000 : ℝ)*(f.sum) + (81143854201/41781250000000000000000000 : ℝ)*base66 + (3302443306733081197/334250000000000000000000000000000 : ℝ)*base68 + (16351068656030799987/1337000000000000000000000000000000 : ℝ)*base70 + (3370812774476581197/334250000000000000000000000000000 : ℝ)*base72 + (19438870665251/1337000000000000000000000000 : ℝ)*base74 + (25019312643846799987/1337000000000000000000000000000000 : ℝ)*base76 + (9075829704213331197/334250000000000000000000000000000 : ℝ)*base78 + (3926711300352081197/334250000000000000000000000000000 : ℝ)*base80 + (5012844352051/1337000000000000000000000000 : ℝ)*base82 + (673751/78125000000000000000 : ℝ)*base89 + (673751/78125000000000000000 : ℝ)*base91 + (107499/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (9987/12500 : ℝ) ≤ (19075878954352253964914889526221/23875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42732919/100000000000000 : ℝ)*(upper0) + (4577713/20000000000000 : ℝ)*(lower1) + (154020831/100000000000000 : ℝ)*(lower3) + (94930841/50000000000000 : ℝ)*(upper4) + (2238415160092351/50000000000000 : ℝ)*(major0) + (2238415160092351/50000000000000 : ℝ)*(major1) + (2238415160092351/50000000000000 : ℝ)*(major2) + (148191524151/100000000000000 : ℝ)*(sp1) + (7978830813/2000000000000 : ℝ)*(sp2) + (33832389277/25000000000000 : ℝ)*(sp3) + (5943266749794643/100000000000000 : ℝ)*(sp8) + (5943118558270491/100000000000000 : ℝ)*(sp9) + (742858476031749/12500000000000 : ℝ)*(sp10) + (186476598200221/6250000000000 : ℝ)*(sp11) + (745940225190161/25000000000000 : ℝ)*(f.failure) + (5943266749794643/100000000000000 : ℝ)*(f.sum) + (44699217039/668500000000000000000000000 : ℝ)*base65 + (1077846246682897151/668500000000000000000000000000000 : ℝ)*base67 + (5522930086762102849/668500000000000000000000000000000 : ℝ)*base70 + (13511372729168397151/668500000000000000000000000000000 : ℝ)*base71 + (1418008347981/668500000000000000000000000 : ℝ)*base73 + (311573624014897151/668500000000000000000000000000000 : ℝ)*base75 + (7175974228012897151/668500000000000000000000000000000 : ℝ)*base77 + (9797804181839897151/668500000000000000000000000000000 : ℝ)*base79 + (217611973553/66850000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2808059/312500000000000000000 : ℝ)*base90 + (2808059/312500000000000000000 : ℝ)*base92 + (2808059/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83189/100000 : ℝ) ≤ (-278051692170351425945329815434943/334250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57822687/50000000000000 : ℝ)*(lower1) + (107438707/50000000000000 : ℝ)*(lower2) + (156173923/100000000000000 : ℝ)*(upper5) + (4511915837643819/100000000000000 : ℝ)*(major0) + (4511915837643819/100000000000000 : ℝ)*(major1) + (225595791882191/5000000000000 : ℝ)*(major2) + (5858396197/20000000000000 : ℝ)*(sp0) + (32874954267/100000000000000 : ℝ)*(sp5) + (47245288989/100000000000000 : ℝ)*(sp6) + (15620799621/50000000000000 : ℝ)*(sp7) + (604438626434771/10000000000000 : ℝ)*(sp12) + (1511095670343607/25000000000000 : ℝ)*(sp13) + (3022184155519853/50000000000000 : ℝ)*(sp14) + (187944612003831/6250000000000 : ℝ)*(sp15) + (1503572516830269/50000000000000 : ℝ)*(f.failure) + (755551944541087/12500000000000 : ℝ)*(f.sum) + (545099581241/95500000000000000000000000 : ℝ)*base66 + (17514924528336144981/1337000000000000000000000000000000 : ℝ)*base68 + (400192593769218991/66850000000000000000000000000000 : ℝ)*base69 + (4072539524820144981/1337000000000000000000000000000000 : ℝ)*base72 + (1774367140209/191000000000000000000000000 : ℝ)*base74 + (53501928177531009/66850000000000000000000000000000 : ℝ)*base76 + (13819211825446144981/1337000000000000000000000000000000 : ℝ)*base78 + (20982358469316144981/1337000000000000000000000000000000 : ℝ)*base80 + (373873165193/133700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6569889/625000000000000000000 : ℝ)*base89 + (6569889/625000000000000000000 : ℝ)*base91 + (319889/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1171_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59321/100000 : ℝ) else (9987/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83189/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1171_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1171_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59321/100000 : ℝ) else (9987/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83189/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1171_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59321/100000 : ℝ) else (9987/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83189/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
